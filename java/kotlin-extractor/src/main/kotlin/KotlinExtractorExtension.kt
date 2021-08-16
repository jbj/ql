package com.github.codeql

import java.io.BufferedWriter
import java.io.File
import java.io.PrintWriter
import java.io.StringWriter
import java.nio.file.Files
import java.nio.file.Paths
import java.text.SimpleDateFormat
import java.util.Date
import kotlin.system.exitProcess
import org.jetbrains.kotlin.backend.common.extensions.IrGenerationExtension
import org.jetbrains.kotlin.backend.common.extensions.IrPluginContext
import org.jetbrains.kotlin.ir.IrElement
import org.jetbrains.kotlin.ir.declarations.*
import org.jetbrains.kotlin.ir.util.dump
import org.jetbrains.kotlin.ir.util.IdSignature
import org.jetbrains.kotlin.ir.util.packageFqName
import org.jetbrains.kotlin.ir.util.render
import org.jetbrains.kotlin.ir.visitors.IrElementVisitor
import org.jetbrains.kotlin.ir.IrFileEntry
import org.jetbrains.kotlin.ir.types.*
import org.jetbrains.kotlin.ir.expressions.*
import org.jetbrains.kotlin.ir.expressions.IrStatementOrigin.*
import org.jetbrains.kotlin.ir.IrStatement
import org.jetbrains.kotlin.ir.symbols.IrClassifierSymbol

class KotlinExtractorExtension(private val tests: List<String>) : IrGenerationExtension {
    override fun generate(moduleFragment: IrModuleFragment, pluginContext: IrPluginContext) {
        val logger = Logger()
        logger.info("Extraction started")
        val trapDir = File(System.getenv("CODEQL_EXTRACTOR_JAVA_TRAP_DIR").takeUnless { it.isNullOrEmpty() } ?: "kotlin-extractor/trap")
        trapDir.mkdirs()
        val srcDir = File(System.getenv("CODEQL_EXTRACTOR_JAVA_SOURCE_ARCHIVE_DIR").takeUnless { it.isNullOrEmpty() } ?: "kotlin-extractor/src")
        srcDir.mkdirs()
        moduleFragment.files.map { extractFile(logger, trapDir, srcDir, it) }
        logger.printLimitedWarningCounts()
        // We don't want the compiler to continue and generate class
        // files etc, so we just exit when we are finished extracting.
        logger.info("Extraction completed")
        exitProcess(0)
    }
}

class Label<T>(val name: Int) {
    override fun toString(): String = "#$name"
}

fun escapeTrapString(str: String) = str.replace("\"", "\"\"")

class Logger() {
    private val warningCounts = mutableMapOf<String, Int>()
    private val warningLimit: Int
    init {
        warningLimit = System.getenv("CODEQL_EXTRACTOR_KOTLIN_WARNING_LIMIT")?.toIntOrNull() ?: 100
    }
    private fun timestamp(): String {
        return "[${SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(Date())} K]"
    }

    fun info(msg: String) {
        print("${timestamp()} $msg\n")
    }
    fun warn(msg: String) {
        val st = Exception().stackTrace
        val suffix =
            if(st.size < 2) {
                "    Missing caller information.\n"
            } else {
                val caller = st[1].toString()
                val count = warningCounts.getOrDefault(caller, 0) + 1
                warningCounts[caller] = count
                when {
                    warningLimit <= 0 -> ""
                    count == warningLimit -> "    Limit reached for warnings from $caller.\n"
                    count > warningLimit -> return
                    else -> ""
                }
            }
        print("${timestamp()} Warning: $msg\n$suffix")
    }
    fun printLimitedWarningCounts() {
        for((caller, count) in warningCounts) {
            if(count >= warningLimit) {
                println("Total of $count warnings from $caller.")
            }
        }
    }
}

class TrapWriter (
    val fileLabel: String,
    val file: BufferedWriter,
    val fileEntry: IrFileEntry
) {
    var nextId: Int = 100
    fun writeTrap(trap: String) {
        file.write(trap)
    }
    fun getLocation(startOffset: Int, endOffset: Int): Label<DbLocation> {
        val unknownLoc = startOffset == -1 && endOffset == -1
        val startLine =   if(unknownLoc) 0 else fileEntry.getLineNumber(startOffset) + 1
        val startColumn = if(unknownLoc) 0 else fileEntry.getColumnNumber(startOffset) + 1
        val endLine =     if(unknownLoc) 0 else fileEntry.getLineNumber(endOffset) + 1
        val endColumn =   if(unknownLoc) 0 else fileEntry.getColumnNumber(endOffset)
        val id: Label<DbLocation> = getFreshLabel()
        // TODO: This isn't right for UnknownLocation
        val fileId: Label<DbFile> = getLabelFor(fileLabel)
        writeTrap("$id = @\"loc,{$fileId},$startLine,$startColumn,$endLine,$endColumn\"\n")
        writeLocations_default(id, fileId, startLine, startColumn, endLine, endColumn)
        return id
    }
    val labelMapping: MutableMap<String, Label<*>> = mutableMapOf<String, Label<*>>()
    fun <T> getExistingLabelFor(label: String): Label<T>? {
        @Suppress("UNCHECKED_CAST")
        return labelMapping.get(label) as Label<T>?
    }
    fun <T> getLabelFor(label: String, initialise: (Label<T>) -> Unit = {}): Label<T> {
        val maybeId: Label<T>? = getExistingLabelFor(label)
        if(maybeId == null) {
            val id: Label<T> = getFreshLabel()
            labelMapping.put(label, id)
            writeTrap("$id = $label\n")
            initialise(id)
            return id
        } else {
            return maybeId
        }
    }
    val variableLabelMapping: MutableMap<IrVariable, Label<out DbLocalvar>> = mutableMapOf<IrVariable, Label<out DbLocalvar>>()
    fun <T> getVariableLabelFor(v: IrVariable): Label<out DbLocalvar> {
        val maybeId = variableLabelMapping.get(v)
        if(maybeId == null) {
            val id = getFreshLabel<DbLocalvar>()
            variableLabelMapping.put(v, id)
            writeTrap("$id = *\n")
            return id
        } else {
            return maybeId
        }
    }
    fun <T> getFreshLabel(): Label<T> {
        return Label(nextId++)
    }
    fun <T> getFreshIdLabel(): Label<T> {
        val label = Label<T>(nextId++)
        writeTrap("$label = *\n")
        return label
    }
}

fun extractFile(logger: Logger, trapDir: File, srcDir: File, declaration: IrFile) {
    val filePath = declaration.path
    val file = File(filePath)
    val fileLabel = "@\"$filePath;sourcefile\""
    val basename = file.nameWithoutExtension
    val extension = file.extension
    val dest = Paths.get("$srcDir/${declaration.path}")
    val destDir = dest.getParent()
    Files.createDirectories(destDir)
    Files.copy(Paths.get(declaration.path), dest)

    val trapFile = File("$trapDir/$filePath.trap")
    val trapFileDir = trapFile.getParentFile()
    trapFileDir.mkdirs()
    trapFile.bufferedWriter().use { trapFileBW ->
        val tw = TrapWriter(fileLabel, trapFileBW, declaration.fileEntry)
        val id: Label<DbFile> = tw.getLabelFor(fileLabel)
        tw.writeFiles(id, filePath, basename, extension, 0)
        val fileExtractor = KotlinFileExtractor(logger, tw)
        val pkg = declaration.fqName.asString()
        val pkgId = fileExtractor.extractPackage(pkg)
        tw.writeCupackage(id, pkgId)
        declaration.declarations.map { fileExtractor.extractDeclaration(it, pkgId) }
    }
}

fun <T> fakeLabel(): Label<T> {
    val sw = StringWriter()
    Exception().printStackTrace(PrintWriter(sw))
    println("Fake label from:\n$sw")
    return Label(0)
}

class KotlinFileExtractor(val logger: Logger, val tw: TrapWriter) {
    fun usePackage(pkg: String): Label<out DbPackage> {
        return extractPackage(pkg)
    }

    fun extractPackage(pkg: String): Label<out DbPackage> {
        val pkgLabel = "@\"package;$pkg\""
        val id: Label<DbPackage> = tw.getLabelFor(pkgLabel, {
            tw.writePackages(it, pkg)
        })
        return id
    }

    fun extractDeclaration(declaration: IrDeclaration, parentid: Label<out DbPackage_or_reftype>) {
        when (declaration) {
            is IrClass -> extractClass(declaration)
            is IrFunction -> extractFunction(declaration, parentid)
            is IrProperty -> extractProperty(declaration, parentid)
            else -> logger.warn("Unrecognised IrDeclaration: " + declaration.javaClass)
        }
    }

    @Suppress("UNUSED_PARAMETER")
    fun useSimpleType(s: IrSimpleType): Label<out DbType> {
        fun primitiveType(name: String): Label<DbPrimitive> {
            return tw.getLabelFor("@\"type;$name\"", {
                tw.writePrimitives(it, name)
            })
        }
        when {
            s.isByte() -> return primitiveType("byte")
            s.isShort() -> return primitiveType("short")
            s.isInt() -> return primitiveType("int")
            s.isLong() -> return primitiveType("long")
            s.isUByte() || s.isUShort() || s.isUInt() || s.isULong() -> {
                logger.warn("Unhandled unsigned type")
                return fakeLabel()
            }

            s.isDouble() -> return primitiveType("double")
            s.isFloat() -> return primitiveType("float")

            s.isBoolean() -> return primitiveType("boolean")

            s.isChar() -> return primitiveType("char")
            s.isString() -> return primitiveType("string") // TODO: Wrong
            s.classifier.owner is IrClass -> {
                val classifier: IrClassifierSymbol = s.classifier
                val cls: IrClass = classifier.owner as IrClass
                return useClass(cls)
            }
            else -> {
                logger.warn("Unrecognised IrSimpleType: " + s.javaClass + ": " + s.render())
                return fakeLabel()
            }
        }
    }

    fun getClassLabel(c: IrClass): String {
        val pkg = c.packageFqName?.asString() ?: ""
        val cls = c.name.asString()
        val qualClassName = if (pkg.isEmpty()) cls else "$pkg.$cls"
        val label = "@\"class;$qualClassName\""
        return label
    }

    fun addClassLabel(c: IrClass): Label<out DbClass> {
        val label = getClassLabel(c)
        val id: Label<DbClass> = tw.getLabelFor(label)
        return id
    }

    fun useClass(c: IrClass): Label<out DbClass> {
        if(c.name.asString() == "Any" || c.name.asString() == "Unit") {
            if(tw.getExistingLabelFor<DbClass>(getClassLabel(c)) == null) {
                return extractClass(c)
            }
        }
        return addClassLabel(c)
    }

    fun extractClass(c: IrClass): Label<out DbClass> {
        val id = addClassLabel(c)
        val locId = tw.getLocation(c.startOffset, c.endOffset)
        val pkg = c.packageFqName?.asString() ?: ""
        val cls = c.name.asString()
        val pkgId = extractPackage(pkg)
        tw.writeClasses(id, cls, pkgId, id)
        tw.writeHasLocation(id, locId)
        c.declarations.map { extractDeclaration(it, id) }
        return id
    }

    fun useType(t: IrType): Label<out DbType> {
        when(t) {
            is IrSimpleType -> return useSimpleType(t)
            is IrClass -> return useClass(t)
            else -> {
                logger.warn("Unrecognised IrType: " + t.javaClass)
                return fakeLabel()
            }
        }
    }

    fun useDeclarationParent(dp: IrDeclarationParent): Label<out DbElement> {
        when(dp) {
            is IrFile -> return usePackage(dp.fqName.asString())
            is IrClass -> return useClass(dp)
            is IrFunction -> return useFunction(dp)
            else -> {
                logger.warn("Unrecognised IrDeclarationParent: " + dp.javaClass)
                return fakeLabel()
            }
        }
    }

    fun useFunction(f: IrFunction): Label<out DbMethod> {
        val paramTypeIds = f.valueParameters.joinToString() { "{${useType(it.type).toString()}}" }
        val returnTypeId = useType(f.returnType)
        val parentId = useDeclarationParent(f.parent)
        val label = "@\"callable;{$parentId}.${f.name.asString()}($paramTypeIds){$returnTypeId}\""
        val id: Label<DbMethod> = tw.getLabelFor(label)
        return id
    }

    fun useValueParameter(vp: IrValueParameter): Label<out DbParam> {
        @Suppress("UNCHECKED_CAST")
        val parentId: Label<out DbMethod> = useDeclarationParent(vp.parent) as Label<out DbMethod>
        val idx = vp.index
        val label = "@\"params;{$parentId};$idx\""
        val id = tw.getLabelFor<DbParam>(label)
        return id
    }

    fun extractValueParameter(vp: IrValueParameter, parent: Label<out DbMethod>, idx: Int) {
        val id = useValueParameter(vp)
        val typeId = useType(vp.type)
        val locId = tw.getLocation(vp.startOffset, vp.endOffset)
        tw.writeParams(id, typeId, idx, parent, id)
        tw.writeHasLocation(id, locId)
        tw.writeParamName(id, vp.name.asString())
    }

    fun extractFunction(f: IrFunction, parentid: Label<out DbPackage_or_reftype>) {
        val id = useFunction(f)
        val locId = tw.getLocation(f.startOffset, f.endOffset)
        val signature = "TODO"
        val returnTypeId = useType(f.returnType)
        tw.writeMethods(id, f.name.asString(), signature, returnTypeId, parentid, id)
        tw.writeHasLocation(id, locId)
        val body = f.body
        if(body != null) {
            extractBody(body, id)
        }
        f.valueParameters.forEachIndexed { i, vp ->
            extractValueParameter(vp, id, i)
        }
    }

    fun useProperty(p: IrProperty): Label<out DbField> {
        val parentId = useDeclarationParent(p.parent)
        val label = "@\"field;{$parentId};${p.name.asString()}\""
        val id: Label<DbField> = tw.getLabelFor(label)
        return id
    }

    fun extractProperty(p: IrProperty, parentid: Label<out DbPackage_or_reftype>) {
        val bf = p.backingField
        if(bf == null) {
            logger.warn("IrProperty without backing field")
        } else {
            val id = useProperty(p)
            val locId = tw.getLocation(p.startOffset, p.endOffset)
            val typeId = useType(bf.type)
            tw.writeFields(id, p.name.asString(), typeId, parentid, id)
            tw.writeHasLocation(id, locId)
        }
    }

    fun extractBody(b: IrBody, callable: Label<out DbCallable>) {
        when(b) {
            is IrBlockBody -> extractBlockBody(b, callable, callable, 0)
            else -> logger.warn("Unrecognised IrBody: " + b.javaClass)
        }
    }

    fun extractBlockBody(b: IrBlockBody, callable: Label<out DbCallable>, parent: Label<out DbStmtparent>, idx: Int) {
        val id = tw.getFreshIdLabel<DbBlock>()
        val locId = tw.getLocation(b.startOffset, b.endOffset)
        tw.writeStmts_block(id, parent, idx, callable)
        tw.writeHasLocation(id, locId)
        for((sIdx, stmt) in b.statements.withIndex()) {
            extractStatement(stmt, callable, id, sIdx)
        }
    }

    fun useVariable(v: IrVariable): Label<out DbLocalvar> {
        return tw.getVariableLabelFor<DbLocalvar>(v)
    }

    fun extractVariable(v: IrVariable, callable: Label<out DbCallable>) {
        val id = useVariable(v)
        val locId = tw.getLocation(v.startOffset, v.endOffset)
        val typeId = useType(v.type)
        val decId = tw.getFreshIdLabel<DbLocalvariabledeclexpr>()
        tw.writeLocalvars(id, v.name.asString(), typeId, decId)
        tw.writeHasLocation(id, locId)
        tw.writeExprs_localvariabledeclexpr(decId, typeId, id, 0)
        tw.writeHasLocation(id, locId)
        val i = v.initializer
        if(i != null) {
            extractExpression(i, callable, decId, 0)
        }
    }

    fun extractStatement(s: IrStatement, callable: Label<out DbCallable>, parent: Label<out DbStmtparent>, idx: Int) {
        when(s) {
            is IrExpression -> {
                extractExpression(s, callable, parent, idx)
            }
            is IrVariable -> {
                extractVariable(s, callable)
            }
            else -> {
                logger.warn("Unrecognised IrStatement: " + s.javaClass)
            }
        }
    }

    fun useValueDeclaration(d: IrValueDeclaration): Label<out DbVariable> {
        when(d) {
            is IrValueParameter -> {
                return useValueParameter(d)
            }
            is IrVariable -> {
                return useVariable(d)
            }
            else -> {
                logger.warn("Unrecognised IrValueDeclaration: " + d.javaClass)
                return fakeLabel()
            }
        }
    }

    fun extractCall(c: IrCall, callable: Label<out DbCallable>, parent: Label<out DbExprparent>, idx: Int) {
        val exprId: Label<out DbExpr> = when {
            c.origin == PLUS -> {
                val id = tw.getFreshIdLabel<DbAddexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_addexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == MINUS -> {
                val id = tw.getFreshIdLabel<DbSubexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_subexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == DIV -> {
                val id = tw.getFreshIdLabel<DbDivexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_divexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == PERC -> {
                val id = tw.getFreshIdLabel<DbRemexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_remexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == EQEQ -> {
                val id = tw.getFreshIdLabel<DbEqexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_eqexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == EXCLEQ -> {
                val id = tw.getFreshIdLabel<DbNeexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_neexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == LT -> {
                val id = tw.getFreshIdLabel<DbLtexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_ltexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == LTEQ -> {
                val id = tw.getFreshIdLabel<DbLeexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_leexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == GT -> {
                val id = tw.getFreshIdLabel<DbGtexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_gtexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } c.origin == GTEQ -> {
                val id = tw.getFreshIdLabel<DbGeexpr>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                tw.writeExprs_geexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                id
            } else -> {
                val id = tw.getFreshIdLabel<DbMethodaccess>()
                val typeId = useType(c.type)
                val locId = tw.getLocation(c.startOffset, c.endOffset)
                val methodId = useFunction(c.symbol.owner)
                tw.writeExprs_methodaccess(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                tw.writeCallableBinding(id, methodId)
                id
            }
        }
        val dr = c.dispatchReceiver
        val offset = if(dr == null) 0 else 1
        if(dr != null) {
            extractExpression(dr, callable, exprId, 0)
        }
        for(i in 0 until c.valueArgumentsCount) {
            val arg = c.getValueArgument(i)
            if(arg != null) {
                extractExpression(arg, callable, exprId, i + offset)
            }
        }
    }

    fun extractExpression(e: IrExpression, callable: Label<out DbCallable>, parent: Label<out DbExprparent>, idx: Int) {
        when(e) {
            is IrCall -> extractCall(e, callable, parent, idx)
            is IrConst<*> -> {
                val v = e.value
                when(v) {
                    is Int -> {
                        val id = tw.getFreshIdLabel<DbIntegerliteral>()
                        val typeId = useType(e.type)
                        val locId = tw.getLocation(e.startOffset, e.endOffset)
                        tw.writeExprs_integerliteral(id, typeId, parent, idx)
                        tw.writeHasLocation(id, locId)
                        tw.writeNamestrings(v.toString(), v.toString(), id)
                    } is Boolean -> {
                        val id = tw.getFreshIdLabel<DbBooleanliteral>()
                        val typeId = useType(e.type)
                        val locId = tw.getLocation(e.startOffset, e.endOffset)
                        tw.writeExprs_booleanliteral(id, typeId, parent, idx)
                        tw.writeHasLocation(id, locId)
                        tw.writeNamestrings(v.toString(), v.toString(), id)
                    } is Char -> {
                        val id = tw.getFreshIdLabel<DbCharacterliteral>()
                        val typeId = useType(e.type)
                        val locId = tw.getLocation(e.startOffset, e.endOffset)
                        tw.writeExprs_characterliteral(id, typeId, parent, idx)
                        tw.writeHasLocation(id, locId)
                        tw.writeNamestrings(v.toString(), v.toString(), id)
                    } is String -> {
                        val id = tw.getFreshIdLabel<DbStringliteral>()
                        val typeId = useType(e.type)
                        val locId = tw.getLocation(e.startOffset, e.endOffset)
                        tw.writeExprs_stringliteral(id, typeId, parent, idx)
                        tw.writeHasLocation(id, locId)
                        tw.writeNamestrings(v.toString(), v.toString(), id)
                    } else -> {
                        if(v == null) {
                            logger.warn("Unrecognised IrConst: null value")
                        } else {
                            logger.warn("Unrecognised IrConst: " + v.javaClass)
                        }
                    }
                }
            }
            is IrGetValue -> {
                val owner = e.symbol.owner
                if (owner is IrValueParameter && owner.index == -1) {
                    val id = tw.getFreshIdLabel<DbThisaccess>()
                    val typeId = useType(e.type)
                    val locId = tw.getLocation(e.startOffset, e.endOffset)
                    tw.writeExprs_thisaccess(id, typeId, parent, idx)
                    tw.writeHasLocation(id, locId)
                } else {
                    val id = tw.getFreshIdLabel<DbVaraccess>()
                    val typeId = useType(e.type)
                    val locId = tw.getLocation(e.startOffset, e.endOffset)
                    tw.writeExprs_varaccess(id, typeId, parent, idx)
                    tw.writeHasLocation(id, locId)

                    val vId = useValueDeclaration(owner)
                    tw.writeVariableBinding(id, vId)
                }
            }
            is IrSetValue -> {
                val id = tw.getFreshIdLabel<DbAssignexpr>()
                val typeId = useType(e.type)
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeExprs_assignexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)

                val lhsId = tw.getFreshIdLabel<DbVaraccess>()
                val lhsTypeId = useType(e.symbol.owner.type)
                tw.writeExprs_varaccess(lhsId, lhsTypeId, id, 0)
                tw.writeHasLocation(id, locId)
                val vId = useValueDeclaration(e.symbol.owner)
                tw.writeVariableBinding(lhsId, vId)

                extractExpression(e.value, callable, id, 1)
            }
            is IrReturn -> {
                val id = tw.getFreshIdLabel<DbReturnstmt>()
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeStmts_returnstmt(id, parent, idx, callable)
                tw.writeHasLocation(id, locId)
                extractExpression(e.value, callable, id, 0)
            } is IrContainerExpression -> {
                val id = tw.getFreshIdLabel<DbBlock>()
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeStmts_block(id, parent, idx, callable)
                tw.writeHasLocation(id, locId)
                e.statements.forEachIndexed { i, s ->
                    extractStatement(s, callable, id, i)
                }
            } is IrWhileLoop -> {
                val id = tw.getFreshIdLabel<DbWhilestmt>()
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeStmts_whilestmt(id, parent, idx, callable)
                tw.writeHasLocation(id, locId)
                extractExpression(e.condition, callable, id, 0)
                val body = e.body
                if(body != null) {
                    extractExpression(body, callable, id, 1)
                }
            } is IrDoWhileLoop -> {
                val id = tw.getFreshIdLabel<DbDostmt>()
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeStmts_dostmt(id, parent, idx, callable)
                tw.writeHasLocation(id, locId)
                extractExpression(e.condition, callable, id, 0)
                val body = e.body
                if(body != null) {
                    extractExpression(body, callable, id, 1)
                }
            } is IrWhen -> {
                val id = tw.getFreshIdLabel<DbWhenexpr>()
                val typeId = useType(e.type)
                val locId = tw.getLocation(e.startOffset, e.endOffset)
                tw.writeExprs_whenexpr(id, typeId, parent, idx)
                tw.writeHasLocation(id, locId)
                if(e.origin == IF) {
                    tw.writeWhen_if(id)
                }
                e.branches.forEachIndexed { i, b ->
                    val bId = tw.getFreshIdLabel<DbWhenbranch>()
                    val bLocId = tw.getLocation(b.startOffset, b.endOffset)
                    tw.writeWhen_branch(bId, id, i)
                    tw.writeHasLocation(bId, bLocId)
                    extractExpression(b.condition, callable, bId, 0)
                    extractExpression(b.result, callable, bId, 1)
                    if(b is IrElseBranch) {
                        tw.writeWhen_branch_else(bId)
                    }
                }
            } else -> {
                logger.warn("Unrecognised IrExpression: " + e.javaClass)
            }
        }
    }
}


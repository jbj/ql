/**
 * @name Jump-to-definition links
 * @description Generates use-definition pairs that provide the data
 *              for jump-to-definition in the code viewer.
 * @kind definitions
 * @id js/jump-to-definition
 */

import javascript
private import Declarations.Declarations

/**
 * Gets the kind of reference that `r` represents.
 *
 * References in callee position have kind `"M"` (for "method"), all
 * others have kind `"V"` (for "variable").
 *
 * For example, in the expression `f(x)`, `f` has kind `"M"` while
 * `x` has kind `"V"`.
 */
string refKind(RefExpr r) {
  if exists(InvokeExpr invk | r = invk.getCallee().getUnderlyingReference())
  then result = "M"
  else result = "V"
}

/**
 * Gets a class, function or object literal `va` may refer to.
 */
ASTNode lookupDef(VarAccess va) {
  exists(AbstractValue av | av = va.analyze().getAValue() |
    result = av.(AbstractClass).getClass() or
    result = av.(AbstractFunction).getFunction() or
    result = av.(AbstractObjectLiteral).getObjectExpr()
  )
}

/**
 * Holds if `va` is of kind `kind` and `def` is the unique class,
 * function or object literal it refers to.
 */
predicate variableDefLookup(VarAccess va, ASTNode def, string kind) {
  count(lookupDef(va)) = 1 and
  def = lookupDef(va) and
  kind = refKind(va)
}

/**
 * Holds if variable access `va` is of kind `kind` and refers to the
 * variable declaration.
 *
 * For example, in the statement `var x = 42, y = x;`, the initializing
 * expression of `y` is a variable access `x` of kind `"V"` that refers to
 * the declaration `x = 42`.
 */
predicate variableDeclLookup(VarAccess va, VarDecl decl, string kind) {
  // restrict to declarations in same file to avoid accidentally picking up
  // unrelated global definitions
  decl = firstRefInTopLevel(va.getVariable(), Decl(), va.getTopLevel()) and
  kind = refKind(va)
}

/**
 * Holds if path expression `path`, which appears in a CommonJS `require`
 * call or an ES 2015 import statement, imports module `target`; `kind`
 * is always "I" (for "import").
 *
 * For example, in the statement `var a = require("./a")`, the path expression
 * `"./a"` imports a module `a` in the same folder.
 */
predicate importLookup(ASTNode path, Module target, string kind) {
  kind = "I" and
  (
    exists(Import i |
      path = i.getImportedPath() and
      target = i.getImportedModule()
    )
    or
    exists(ReExportDeclaration red |
      path = red.getImportedPath() and
      target = red.getImportedModule()
    )
  )
}

/**
 * Gets a node that may write the property read by `prn`.
 */
ASTNode getAWrite(DataFlow::PropRead prn) {
  exists(DataFlow::AnalyzedNode base, DefiniteAbstractValue baseVal, string propName |
    base = prn.getBase() and
    propName = prn.getPropertyName() and
    baseVal = base.getAValue().getAPrototype*()
  |
    // write to a property on baseVal
    exists(AnalyzedPropertyWrite apw |
      result = apw.getAstNode() and
      apw.writes(baseVal, propName, _)
    )
    or
    // non-static class members aren't covered by `AnalyzedPropWrite`, so have to be handled
    // separately
    exists(ClassDefinition c, MemberDefinition m |
      m = c.getMember(propName) and
      baseVal.(AbstractInstance).getConstructor().(AbstractClass).getClass() = c and
      result = m.getNameExpr()
    )
  )
}

/**
 * Holds if `prop` is the property name expression of a property read that
 * may read the property written by `write`. Furthermore, `write` must be the
 * only such property write. Parameter `kind` is always bound to `"M"`
 * at the moment.
 */
predicate propertyLookup(Expr prop, ASTNode write, string kind) {
  exists(DataFlow::PropRead prn | prop = prn.getPropertyNameExpr() |
    count(getAWrite(prn)) = 1 and
    write = getAWrite(prn) and
    kind = "M"
  )
}

/**
 * Holds if `ref` is an identifier that refers to a type declared at `decl`.
 */
predicate typeLookup(ASTNode ref, ASTNode decl, string kind) {
  exists(TypeAccess typeAccess |
    ref = typeAccess.getIdentifier() and
    decl = typeAccess.getTypeName().getADefinition() and
    kind = "T"
  )
}

/**
 * Holds if `ref` is the callee name of an invocation of `decl`.
 */
predicate typedInvokeLookup(ASTNode ref, ASTNode decl, string kind) {
  not variableDefLookup(ref, decl, _) and
  not propertyLookup(ref, decl, _) and
  exists(InvokeExpr invoke, Expr callee |
    callee = invoke.getCallee().getUnderlyingReference() and
    (ref = callee.(Identifier) or ref = callee.(DotExpr).getPropertyNameExpr()) and
    decl = invoke.getResolvedCallee() and
    kind = "M"
  )
}

/**
 * Holds if `ref` is a JSDoc type annotation referring to a class defined at `decl`.
 */
predicate jsdocTypeLookup(JSDocNamedTypeExpr ref, ASTNode decl, string kind) {
  decl = ref.getClass().getAstNode() and
  kind = "T"
}

from Locatable ref, ASTNode decl, string kind
where
  variableDefLookup(ref, decl, kind)
  or
  // prefer definitions over declarations
  not variableDefLookup(ref, _, _) and variableDeclLookup(ref, decl, kind)
  or
  importLookup(ref, decl, kind)
  or
  propertyLookup(ref, decl, kind)
  or
  typeLookup(ref, decl, kind)
  or
  typedInvokeLookup(ref, decl, kind)
  or
  jsdocTypeLookup(ref, decl, kind)
select ref, decl, kind

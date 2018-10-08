import cpp

class SALMacro extends Macro {
  SALMacro() {
    this.getFile().getBaseName() = "sal.h" or
    this.getFile().getBaseName() = "specstrings_strict.h" or
    this.getFile().getBaseName() = "specstrings.h" or
    this.getFile().getBaseName() = "w32p.h" or
    this.getFile().getBaseName() = "minwindef.h"
  }
}

pragma[noinline]
predicate isTopLevelMacroAccess(MacroAccess ma) {
	not exists(ma.getParentInvocation())
}

class SALAnnotation extends MacroInvocation {
  SALAnnotation() {
    this.getMacro() instanceof SALMacro and
    isTopLevelMacroAccess(this)
  }

  /** Returns the `Declaration` annotated by `this`. */
  Declaration getDeclaration() {
    annotatesAt(this, result.getADeclarationEntry(), _, _) and
    not result instanceof Type // exclude typedefs
  }

  /** Returns the `DeclarationEntry` annotated by `this`. */
  DeclarationEntry getDeclarationEntry() {
    annotatesAt(this, result, _, _) and
    not result instanceof TypeDeclarationEntry // exclude typedefs
  }
}

class SALCheckReturn extends SALAnnotation {
  SALCheckReturn() {
    exists(SALMacro m | m = this.getMacro() |
      m.getName() = "_Check_return_" or
      m.getName() = "_Must_inspect_result_"
    )
  }
}

class SALNotNull extends SALAnnotation {
  SALNotNull() {
    exists(SALMacro m | m = this.getMacro() |
      not m.getName().matches("%\\_opt\\_%") and
      (
        m.getName().matches("_In%") or
        m.getName().matches("_Out%") or
        m.getName() = "_Ret_notnull_"
      )
    )
    and
    exists(Type t
    | t = this.getDeclaration().(Variable).getType() or
      t = this.getDeclaration().(Function).getType()
    | t.getUnspecifiedType() instanceof PointerType
    )
  }
}

class SALMaybeNull extends SALAnnotation {
  SALMaybeNull() {
    exists(SALMacro m | m = this.getMacro() |
    m.getName().matches("%\\_opt\\_%") or
    m.getName().matches("\\_Ret_maybenull\\_%") or
    m.getName() = "_Result_nullonfailure_"
    )
  }
}

///////////////////////////////////////////////////////////////////////////////
// Implementation details
/**
 * Holds if `a` annotates the declaration entry `d` and
 * its location is the `idx`th location in `file` that holds a SAL element.
 */
predicate annotatesAt(SALAnnotation a, DeclarationEntry d,
                              File file, int idx) {
  annotatesAtLocation(a.getLocation(), d, file, idx)
}

/**
 * Holds if `loc` is the `idx`th location in `file` that holds a SAL element,
 * which annotates the declaration entry `d` (by occurring before it without
 * any other declaration entries in between).
 */
// For performance reasons, do not mention the annotation itself here,
// but compute with locations instead.
private predicate annotatesAtLocation(Location loc, DeclarationEntry d,
                                  File file, int idx) {
  loc = salRelevantLocationAt(file, idx) and
  // Stop the recursion at the location of a declaration entry.
  not declarationEntryLocation(loc) and
  (
    // Base case: `loc` right before `d`
    d.getLocation() = salRelevantLocationAt(file, idx + 1) or
    // Recursive case: `loc` right before some annotation on `d`
    annotatesAtLocation(_, d, file, idx + 1)
  )
}

/**
 * A parameter annotated by one or more SAL annotations.
 */
class SALParameter extends Parameter {
	/** One of this parameter's annotations. */
	SALAnnotation a;

	SALParameter() {
		annotatesAt(a, this.getADeclarationEntry(), _, _)
	}

	predicate isIn() { a.getMacroName().toLowerCase().matches("%\\_in%") }

	predicate isOut() { a.getMacroName().toLowerCase().matches("%\\_out%") }

	predicate isInOut() { a.getMacroName().toLowerCase().matches("%\\_inout%") }
}

/**
 * A SAL element, i.e. a SAL annotation or a declaration entry
 * that may have SAL annotations.
 */
library class SALElement extends Element {
  SALElement() {
    containsSALAnnotation(this.(DeclarationEntry).getFile()) or
    this instanceof SALAnnotation
  }
}

/** Holds if `file` contains a SAL annotation. */
pragma[noinline]
private predicate containsSALAnnotation(File file) {
  any(SALAnnotation a).getFile() = file
}

/** Holds if `loc` is the location of a SAL element. */
pragma[noinline]
private predicate salLocation(Location loc) {
  any(SALElement e).getLocation() = loc
}

/** Holds if `loc` is the location of a declaration entry. */
pragma[noinline]
private predicate declarationEntryLocation(Location loc) {
  any(DeclarationEntry e).getLocation() = loc
}

/**
 * Gets the `idx`th location in `file` that holds a SAL element,
 * ordering locations lexicographically by their
 * start line, start column, end line, and end column.
 */
private Location salRelevantLocationAt(File file, int idx) {
  result = rank[idx](Location loc |
    salLocation(loc) and loc.getFile() = file |
    loc order by loc.getStartLine(), loc.getStartColumn(), loc.getEndLine(), loc.getEndColumn()
  )
}

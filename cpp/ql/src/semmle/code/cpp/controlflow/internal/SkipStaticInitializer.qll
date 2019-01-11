private import cpp
private import semmle.code.cpp.dataflow.EscapesTree

/**
 * Holds if the expression in this initializer is evaluated at compile time and
 * thus should not have control flow computed.
 */
predicate skipInitializer(Initializer init) {
  exists(LocalVariable local |
    init = local.getInitializer() and
    local.isStatic() and
    not runtimeExprInStaticInitializer(init.getExpr())
  )
}

/**
 * Holds if `e` is an expression in a static initializer that must be evaluated
 * at run time. This predicate computes "is non-const" instead of "is const" in
 * order to avoid recursion through forall.
 */
private predicate runtimeExprInStaticInitializer(Expr e) {
  inStaticInitializer(e) and
  if
    e instanceof AggregateLiteral
    or
    e instanceof PointerArithmeticOperation
    or
    // Extractor doesn't populate this specifier at the time of writing, so
    // this case has not been tested. See CPP-314.
    e.(FunctionCall).getTarget().hasSpecifier("constexpr")
  then runtimeExprInStaticInitializer(e.getAChild())
  else not constantInStaticInitializer(e)
}

private predicate computesConstantAddress(Expr e) {
  inStaticInitializer(e) and
  exists(Variable v |
    v.isStatic()
    or
    v instanceof GlobalOrNamespaceVariable
  |
    addressFromVariableAccess(v.getAnAccess(), e.getFullyConverted())
  )
  or
  computesConstantAddress(e.getParent())
}

private predicate constantInStaticInitializer(Expr e) {
  inStaticInitializer(e) and
  (
    e.isConstant()
    or
    // This represents the function access as implicitly converted to a pointer
    e instanceof FunctionAccess
    or
    e.(AddressOfExpr).getOperand() instanceof FunctionAccess
    or
    computesConstantAddress(e)
  )
}

/** Holds if `e` is part of the initializer of a local static variable. */
private predicate inStaticInitializer(Expr e) {
  exists(LocalVariable local |
    local.isStatic() and
    e.getParent+() = local.getInitializer()
  )
}

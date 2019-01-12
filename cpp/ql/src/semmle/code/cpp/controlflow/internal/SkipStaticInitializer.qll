private import cpp

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
  if e instanceof AggregateLiteral
  then runtimeExprInStaticInitializer(e.getAChild())
  else not constantInStaticInitializer(e)
}

private predicate computesConstantAddress(Expr e) {
  inStaticInitializer(e) and
  (
    e instanceof AddressOfExpr
    or
    e.getConversion+() instanceof ArrayToPointerConversion
    or
    e.getFullyConverted() instanceof ReferenceToExpr
  )
  or
  // Pointer arithmetic involving a constant address and a constant integer.
  // Because the predicates involved restrict the types, we know that it'll be
  // for two different arguments.
  e = any(PointerArithmeticOperation op |
    computesConstantAddress(op.getAnOperand()) and
    op.getAnOperand().isConstant()
  )
}

private predicate constantInStaticInitializer(Expr e) {
  inStaticInitializer(e) and
  (
    e.isConstant()
    or
    // This represents the function access as implicitly converted to a pointer
    e instanceof FunctionAccess
  )
  or
  computesConstantAddress(e)
}

/** Holds if `e` is part of the initializer of a local static variable. */
private predicate inStaticInitializer(Expr e) {
  exists(LocalVariable local |
    local.isStatic() and
    e.getParent+() = local.getInitializer()
  )
}

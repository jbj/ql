private import cpp

cached
predicate addressConstantExpression(Expr e) {
// TODO: propagate these underscores as far down as possible.
  pointerFromVariableAccess(_, e)
  or
  referenceFromVariableAccess(_, e)
  or
  // `e` could be a pointer that is converted to a reference as the final step,
  // meaning that we pass a value that is two dereferences away from referring
  // to `va`. This happens, for example, with `void std::vector::push_back(T&&
  // value);` when called as `v.push_back(&x)`, for a static variable `x`. It
  // can also happen when taking a reference to a const pointer to a
  // (potentially non-const) value.
  exists(Expr pointerValue |
    pointerFromVariableAccess(_, pointerValue) and
    e = pointerValue.getConversion().(ReferenceToExpr)
  )
  or
  isFunctionAccess(e)
}

/**
 * Holds if `e` is a constant function address. Implicit conversions mean that
 * an expression like `myFunction` is equivalent to `&**&***myFunction`.
 */
private predicate isFunctionAccess(Expr e) {
  e instanceof FunctionAccess
  or
  isFunctionAccess(e.(AddressOfExpr).getOperand())
  or
  isFunctionAccess(e.(PointerDereferenceExpr).getOperand())
  // TODO: what about conversions? What about C++ function _references_?
}

/*
 * The following is adapted from EscapesTree.qll and adjusted to require
 * constants everywhere.
 */

private predicate lvalueToLvalueStep(Expr lvalueIn, Expr lvalueOut) {
  lvalueIn = lvalueOut.(DotFieldAccess).getQualifier().getFullyConverted()
  or
  lvalueIn.getConversion() = lvalueOut.(ParenthesisExpr)
}

private predicate pointerToLvalueStep(Expr pointerIn, Expr lvalueOut) {
  lvalueOut = any(ArrayExpr ae |
    pointerIn = ae.getArrayBase().getFullyConverted() and
    ae.getArrayOffset().isConstant()
  )
  or
  pointerIn = lvalueOut.(PointerDereferenceExpr).getOperand().getFullyConverted()
  or
  pointerIn = lvalueOut.(PointerFieldAccess).getQualifier().getFullyConverted()
}

private predicate lvalueToPointerStep(Expr lvalueIn, Expr pointerOut) {
  lvalueIn.getConversion() = pointerOut.(ArrayToPointerConversion)
  or
  lvalueIn = pointerOut.(AddressOfExpr).getOperand().getFullyConverted()
}

private predicate pointerToPointerStep(Expr pointerIn, Expr pointerOut) {
  (
    pointerOut instanceof PointerAddExpr
    or
    pointerOut instanceof PointerSubExpr
  ) and
  pointerIn = pointerOut.getAChild().getFullyConverted() and
  pointerIn.getType().getUnspecifiedType() instanceof PointerType and
  // The pointer arg won't be constant in the sense of `isConstant`, so this
  // will have to match the integer argument.
  pointerOut.getAChild().isConstant()
  or
  pointerIn = pointerOut.(UnaryPlusExpr).getOperand().getFullyConverted()
  or
  pointerIn.getConversion() = pointerOut.(Cast)
  or
  pointerIn.getConversion() = pointerOut.(ParenthesisExpr)
  or
  pointerOut = any(ConditionalExpr cond |
    cond.getCondition().getValue().toInt() != 0 and
    pointerIn = cond.getThen().getFullyConverted()
    or
    cond.getCondition().getValue().toInt() = 0 and
    pointerIn = cond.getElse().getFullyConverted()
  )
}

private predicate lvalueToReferenceStep(Expr lvalueIn, Expr referenceOut) {
  lvalueIn.getConversion() = referenceOut.(ReferenceToExpr)
}

private predicate referenceToLvalueStep(Expr referenceIn, Expr lvalueOut) {
  // This probably cannot happen. It would require an expression to be
  // converted to a reference and back again without an intermediate variable
  // assignment.
  referenceIn.getConversion() = lvalueOut.(ReferenceDereferenceExpr)
}

private predicate referenceToReferenceStep(Expr referenceIn, Expr referenceOut) {
  referenceIn.getConversion() = referenceOut.(Cast)
  or
  referenceIn.getConversion() = referenceOut.(ParenthesisExpr)
}

private predicate lvalueFromVariableAccess(VariableAccess va, Expr lvalue) {
  // Base case for non-reference types.
  lvalue = va and
  not va.getConversion() instanceof ReferenceDereferenceExpr and
  va.getTarget() = any(Variable v |
    v.isStatic()
    or
    v instanceof GlobalOrNamespaceVariable
  )
  or
  // Base case for reference types where we pretend that they are
  // non-reference types. The type of the target of `va` can be `ReferenceType`
  // or `FunctionReferenceType`.
  lvalue = va.getConversion().(ReferenceDereferenceExpr)
  or
  // lvalue -> lvalue
  exists(Expr prev |
    lvalueFromVariableAccess(va, prev) and
    lvalueToLvalueStep(prev, lvalue)
  )
  or
  // pointer -> lvalue
  exists(Expr prev |
    pointerFromVariableAccess(va, prev) and
    pointerToLvalueStep(prev, lvalue)
  )
  or
  // reference -> lvalue
  exists(Expr prev |
    referenceFromVariableAccess(va, prev) and
    referenceToLvalueStep(prev, lvalue)
  )
}

private predicate pointerFromVariableAccess(VariableAccess va, Expr pointer) {
  // pointer -> pointer
  exists(Expr prev |
    pointerFromVariableAccess(va, prev) and
    pointerToPointerStep(prev, pointer)
  )
  or
  // lvalue -> pointer
  exists(Expr prev |
    lvalueFromVariableAccess(va, prev) and
    lvalueToPointerStep(prev, pointer)
  )
}

private predicate referenceFromVariableAccess(VariableAccess va, Expr reference) {
  // reference -> reference
  exists(Expr prev |
    referenceFromVariableAccess(va, prev) and
    referenceToReferenceStep(prev, reference)
  )
  or
  // lvalue -> reference
  exists(Expr prev |
    lvalueFromVariableAccess(va, prev) and
    lvalueToReferenceStep(prev, reference)
  )
}

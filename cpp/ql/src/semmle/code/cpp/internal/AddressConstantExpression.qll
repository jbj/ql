private import cpp

cached
predicate addressConstantExpression(Expr e) {
// TODO: propagate these underscores as far down as possible.
  pointerFromAccess(_, e)
  or
  referenceFromAccess(_, e)
  or
  // Special case for function pointers, where `fp == *fp`.
  lvalueFromAccess(_, e) and
  e.getType() instanceof FunctionPointerType
}

/*
 * The following is adapted from EscapesTree.qll and adjusted to require
 * constants everywhere.
 */

private predicate lvalueToLvalueStep(Expr lvalueIn, Expr lvalueOut) {
  lvalueIn = lvalueOut.(DotFieldAccess).getQualifier().getFullyConverted()
  or
  lvalueIn.getConversion() = lvalueOut.(ParenthesisExpr)
  or
  // Special case for function pointers, where `fp == *fp`.
  lvalueIn = lvalueOut.(PointerDereferenceExpr).getOperand().getFullyConverted() and
  lvalueIn.getType() instanceof FunctionPointerType
}

private predicate pointerToLvalueStep(Expr pointerIn, Expr lvalueOut) {
  lvalueOut = any(ArrayExpr ae |
    pointerIn = ae.getArrayBase().getFullyConverted() and
    hasConstantValue(ae.getArrayOffset())
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
  // The pointer arg won't be constant in the sense of `hasConstantValue`, so
  // this will have to match the integer argument.
  hasConstantValue(pointerOut.getAChild())
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
  or
  pointerOut = any(CommaExpr comma |
    comma.getLeftOperand().isPure() and
    pointerIn = comma.getRightOperand()
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

private predicate lvalueFromAccess(Access va, Expr lvalue) {
  // Base case for non-reference types.
  lvalue = va and
  not va.getConversion() instanceof ReferenceDereferenceExpr and
  va.getTarget() = any(Variable v |
    v.(Variable).isStatic()
    or
    v instanceof GlobalOrNamespaceVariable
  )
  or
  // There is no `Conversion` for the implicit conversion from a function type
  // to a function _pointer_ type. Instead, the type of a `FunctionAccess`
  // tells us how it's going to be used.
  lvalue = va and
  // TODO: not getConversion...
  va.(FunctionAccess).getType() instanceof RoutineType
  or
  // Base case for reference types where we pretend that they are
  // non-reference types. The type of the target of `va` can be `ReferenceType`
  // or `FunctionReferenceType`.
  lvalue = va.getConversion().(ReferenceDereferenceExpr)
  or
  // lvalue -> lvalue
  exists(Expr prev |
    lvalueFromAccess(va, prev) and
    lvalueToLvalueStep(prev, lvalue)
  )
  or
  // pointer -> lvalue
  exists(Expr prev |
    pointerFromAccess(va, prev) and
    pointerToLvalueStep(prev, lvalue)
  )
  or
  // reference -> lvalue
  exists(Expr prev |
    referenceFromAccess(va, prev) and
    referenceToLvalueStep(prev, lvalue)
  )
}

private predicate pointerFromAccess(Access va, Expr pointer) {
  // There is no `Conversion` for the implicit conversion from a function type
  // to a function _pointer_ type. Instead, the type of a `FunctionAccess`
  // tells us how it's going to be used.
  pointer = va and
  // TODO: not getConversion...
  va.(FunctionAccess).getType() instanceof FunctionPointerType
  or
  // pointer -> pointer
  exists(Expr prev |
    pointerFromAccess(va, prev) and
    pointerToPointerStep(prev, pointer)
  )
  or
  // lvalue -> pointer
  exists(Expr prev |
    lvalueFromAccess(va, prev) and
    lvalueToPointerStep(prev, pointer)
  )
}

private predicate referenceFromAccess(Access va, Expr reference) {
  // TODO: base case for function reference?
  // reference -> reference
  exists(Expr prev |
    referenceFromAccess(va, prev) and
    referenceToReferenceStep(prev, reference)
  )
  or
  // lvalue -> reference
  exists(Expr prev |
    lvalueFromAccess(va, prev) and
    lvalueToReferenceStep(prev, reference)
  )
}

/** Holds if `e` is constant according to the database. */
private predicate hasConstantValue(Expr e) {
  valuebind(_,underlyingElement(e))
}

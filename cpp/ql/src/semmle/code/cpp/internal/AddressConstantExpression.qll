private import cpp

/** Holds if `v` is a constexpr variable initialized to a constant address. */
predicate addressConstantVariable(Variable v) {
  addressConstantExpression(v.getInitializer().getExpr().getFullyConverted())
  // Here we should also require that `v` is constexpr, but we don't have that
  // information in the db. See CPP-314.
}

// TODO: make isConstant cached
predicate addressConstantExpression(Expr e) {
  pointerFromAccess(e)
  or
  referenceFromAccess(e)
  or
  // Special case for function pointers, where `fp == *fp`.
  lvalueFromAccess(e) and
  e.getType() instanceof FunctionPointerType
}

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
    hasConstantValue(ae.getArrayOffset().getFullyConverted())
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
  hasConstantValue(pointerOut.getAChild().getFullyConverted())
  or
  pointerIn = pointerOut.(UnaryPlusExpr).getOperand().getFullyConverted()
  or
  pointerIn.getConversion() = pointerOut.(Cast)
  or
  pointerIn.getConversion() = pointerOut.(ParenthesisExpr)
  or
  pointerOut = any(ConditionalExpr cond |
    cond.getCondition().getFullyConverted().getValue().toInt() != 0 and
    pointerIn = cond.getThen().getFullyConverted()
    or
    cond.getCondition().getFullyConverted().getValue().toInt() = 0 and
    pointerIn = cond.getElse().getFullyConverted()
  )
  or
  // The comma operator is allowed by C++17 but disallowed by C99. This
  // disjunct is a compromise that's chosen for being easy to implement.
  pointerOut = any(CommaExpr comma |
    hasConstantValue(comma.getLeftOperand()) and
    pointerIn = comma.getRightOperand().getFullyConverted()
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

// TODO: rename this and others
private predicate lvalueFromAccess(Expr lvalue) {
  lvalue.(VariableAccess).getTarget() = any(Variable v |
    v.(Variable).isStatic()
    or
    v instanceof GlobalOrNamespaceVariable
  )
  or
  // There is no `Conversion` for the implicit conversion from a function type
  // to a function _pointer_ type. Instead, the type of a `FunctionAccess`
  // tells us how it's going to be used.
  lvalue.(FunctionAccess).getType() instanceof RoutineType
  or
  // lvalue -> lvalue
  exists(Expr prev |
    lvalueFromAccess(prev) and
    lvalueToLvalueStep(prev, lvalue)
  )
  or
  // pointer -> lvalue
  exists(Expr prev |
    pointerFromAccess(prev) and
    pointerToLvalueStep(prev, lvalue)
  )
  or
  // reference -> lvalue
  exists(Expr prev |
    referenceFromAccess(prev) and
    referenceToLvalueStep(prev, lvalue)
  )
}

private predicate pointerFromAccess(Expr pointer) {
  // There is no `Conversion` for the implicit conversion from a function type
  // to a function _pointer_ type. Instead, the type of a `FunctionAccess`
  // tells us how it's going to be used.
  pointer.(FunctionAccess).getType() instanceof FunctionPointerType
  or
  addressConstantVariable(pointer.(VariableAccess).getTarget()) and
  pointer.getType().getUnderlyingType() instanceof PointerType
  or
  // pointer -> pointer
  exists(Expr prev |
    pointerFromAccess(prev) and
    pointerToPointerStep(prev, pointer)
  )
  or
  // lvalue -> pointer
  exists(Expr prev |
    lvalueFromAccess(prev) and
    lvalueToPointerStep(prev, pointer)
  )
}

private predicate referenceFromAccess(Expr reference) {
  addressConstantVariable(reference.(VariableAccess).getTarget()) and
  reference.getType().getUnderlyingType() instanceof ReferenceType
  or
  addressConstantVariable(reference.(VariableAccess).getTarget()) and
  reference.getType().getUnderlyingType() instanceof FunctionReferenceType // not a ReferenceType
  or
  // reference -> reference
  exists(Expr prev |
    referenceFromAccess(prev) and
    referenceToReferenceStep(prev, reference)
  )
  or
  // lvalue -> reference
  exists(Expr prev |
    lvalueFromAccess(prev) and
    lvalueToReferenceStep(prev, reference)
  )
}

/** Holds if `e` is constant according to the database. */
private predicate hasConstantValue(Expr e) {
  valuebind(_,underlyingElement(e))
}

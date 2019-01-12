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
  addressFromVariableAccess(_, e.getFullyConverted())
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

/*
 * The following is adapted from EscapesTree.qll and adjusted to require
 * constants everywhere.
 */

private predicate lvalueToLvalueStep(Expr lvalueIn, Expr lvalueOut) {
  lvalueIn = lvalueOut.(DotFieldAccess).getQualifier().getFullyConverted()
  or
  lvalueIn.getConversion() = lvalueOut.(ParenthesisExpr)
  or
  // When an object is implicitly converted to a reference to one of its base
  // classes, it gets two `Conversion`s: there is first an implicit
  // `CStyleCast` to its base class followed by a `ReferenceToExpr` to a
  // reference to its base class. Whereas an explicit cast to the base class
  // would produce an rvalue, which would not be convertible to an lvalue
  // reference, this implicit cast instead produces an lvalue. The following
  // case ensures that we propagate the property of being an lvalue through
  // such casts.
  lvalueIn.getConversion() = lvalueOut and
  lvalueOut.(CStyleCast).isImplicit()
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
  inStaticInitializer(va) and
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

/**
 * Holds if `e` is a fully-converted expression that evaluates to an address
 * derived from the address of `va`.
 */
private predicate addressFromVariableAccess(VariableAccess va, Expr e) {
  pointerFromVariableAccess(va, e)
  or
  referenceFromVariableAccess(va, e)
  or
  // `e` could be a pointer that is converted to a reference as the final step,
  // meaning that we pass a value that is two dereferences away from referring
  // to `va`. This happens, for example, with `void std::vector::push_back(T&&
  // value);` when called as `v.push_back(&x)`, for a static variable `x`. It
  // can also happen when taking a reference to a const pointer to a
  // (potentially non-const) value.
  exists(Expr pointerValue |
    pointerFromVariableAccess(va, pointerValue) and
    e = pointerValue.getConversion().(ReferenceToExpr)
  )
}

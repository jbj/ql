private import semmle.code.cpp.ssa.SSAIR

// Redundant nullness check cases:
// - Because it's already been tested (ESSA or guards)
// - Because it's assigned to a non-null value (SSA)
// - Because it's assigned to a null value (SSA)
// - Dereference followed by null check (guards)
//   - Do we already have a query for that? Or is that for bounds checks?

private newtype TNullity = Null() or NotNull()

private class Nullity extends TNullity {
  string toString() {
    this = Null() and result = "Null"
    or
    this = NotNull() and result = "NotNull"
  }

  Nullity negate() {
    this = Null() and result = NotNull()
    or
    this = NotNull() and result = Null()
  }
}

class NullInstruction extends ConstantValueInstruction {
  NullInstruction() {
    this.getValue() = "0" and
    this.getResultType().getUnspecifiedType() instanceof PointerType
  }
}

class ThisInstruction extends Instruction {
  ThisInstruction() {
    this.getOpcode().toString() = "InitializeThis" // TODO: string?
  }
}

/**
 * Holds if `bool` is an instruction that explicitly checks whether `checked`
 * is null and evaluates to true iff `checked` equals `trueIff`.
 */
predicate explicitNullTestOfInstruction(
  Instruction checked, Instruction bool, Nullity trueIff
) {
  bool = any(CompareInstruction cmp |
    exists(NullInstruction null |
      cmp.getLeftOperand() = null and cmp.getRightOperand() = checked
      or
      cmp.getLeftOperand() = checked and cmp.getRightOperand() = null
    |
      cmp instanceof CompareEQInstruction and trueIff = Null()
      or
      cmp instanceof CompareNEInstruction and trueIff = NotNull()
    )
  )
  or
  bool = any(ConvertInstruction convert |
    checked = convert.getOperand() and
    convert.getResultType() instanceof BoolType and
    checked.getResultType().getUnspecifiedType() instanceof PointerType and
    trueIff = NotNull()
  )
}

predicate pointerConversionStep(
  Instruction converted, Instruction converting
) {
  converting.(ConvertInstruction).getOperand() = converted and
  // TODO: should this also allow ReferenceType?
  converting.getResultType().getUnspecifiedType() instanceof PointerType and
  converted.getResultType().getUnspecifiedType() instanceof PointerType
}

predicate explicitNullTest(
  LoadInstruction load, Instruction bool, Nullity trueIff
) {
  exists(Instruction checked |
    explicitNullTestOfInstruction(checked, bool, trueIff) and
    pointerConversionStep*(load, checked)
  )
}

predicate booleanIsNullTest(
  LoadInstruction load, Instruction bool, Nullity trueIff
) {
  explicitNullTest(load, bool, trueIff)
  or
  booleanIsNullTest(load, bool.(NegateInstruction).getOperand(),
                    trueIff.negate())
}

/*
if (x != nullptr) {
  use(x);
  if (nondet()) {
    x = nondet();
  }
  use(x);
  if (x != nullptr) {
    return;
  }
  use(x);
}

// The 'ssa variable' of `x`, which is the memory instruction where the load
// comes from, is known to be non/null in the entire guarded region.
// Reassignments don't matter as they are to other SSA variables. All I need is
// a Guards library.
//
// Beware that some memory edges have an implicit 'slicing' on them currently.
// In particular, two edges from UnmodeledDefinition do not necessarily denote
// the same value.
 */
predicate edgeIsNullTest(
  LoadInstruction load, Instruction i1, Instruction i2, Nullity edgeImplies
) {
  i1 = any(ConditionalBranchInstruction cond |
    exists(Instruction bool, Nullity trueIff |
      booleanIsNullTest(load, bool, trueIff) and
      cond.getCondition() = bool
    |
      i2 = cond.getTrueSuccessor() and
      edgeImplies = trueIff
      or
      i2 = cond.getFalseSuccessor() and
      edgeImplies = trueIff.negate()
    )
  )
  // TODO: dereference, switch, ...
  // TODO: support this pattern: `if ((x = f()) != NULL)`. It appears when
  // `checked` is an `Invoke` instruction.
}

predicate instructionMayBe(Instruction i, Nullity value) {
  not i instanceof CopyInstruction and // handled below
  not i instanceof PhiInstruction and // handled below
  not i instanceof ConvertInstruction and // handled below
  (
    value = Null() and
    ( not i instanceof VariableAddressInstruction and // is never null
      not i instanceof FunctionInstruction and // is never null
      // TODO: Address of field, except field 0
      not i instanceof ThisInstruction and // is never null
      // TODO: exception for std::nothrow
      // TODO: new[]
      // TODO: is this even correct? Or is `new` not supported yet in IR?
      not i.(InvokeInstruction).getCallTarget().(FunctionInstruction).getFunctionSymbol().getName() = "operator new"
    )
    or
    value = NotNull() and
    ( not i instanceof NullInstruction
    )
  )
  or
  // Copy covers both loads and stores
  instructionMayBe(i.(CopyInstruction).getSourceValue(), value)
  or
  instructionMayBe(i.(PhiInstruction).getAnOperand(), value)
  or
  instructionMayBe(i.(ConvertInstruction).getOperand(), value)
  or
  // TODO: IR bug workaround. If a phi instruction has only one input, we say
  // that it may be both null and non-null since we have to assume the worst
  // about the missing other input(s).
  strictcount(i.(PhiInstruction).getAnOperand()) = 1
}

from LoadInstruction load, Nullity impossibleNullity
where explicitNullTest(load, _, _)
  and not instructionMayBe(load, impossibleNullity)
  and instructionMayBe(load, _) // TODO: probably papers over some problem
  and not load.getAST().isInMacroExpansion()
select load.getLocation().getFile(), load, impossibleNullity

//from LoadInstruction load
//where not exists(load.getSourceValue())
//select load



//from CompareEQInstruction eq, ConstantValueInstruction null
//where eq.getAnOperand() = null
//  and null.getValue() = "0"
//  and null.getResultType().getUnspecifiedType() instanceof PointerType
//select null

//int getPhiInputCount(PhiInstruction phi) {
//  result = count(phi.getAnOperand())
//}
//from int nOperands, int nPhis
//where nOperands = getPhiInputCount(_)
//  and nPhis = count(PhiInstruction phi | nOperands = getPhiInputCount(phi))
//select nOperands, nPhis

//from Instruction i, OperandTag tag
//where i.isMemoryOperand(tag)
//select i.getOpcode().toString(), tag.toString()

//from VariableAddressInstruction vai, StoreInstruction store
//where vai.getVariable().(IRUserVariable).getVariable().getName() = "as_str"
//  and store.getDestinationAddress() = vai
//select vai
//  , count(Instruction i | i.getAnOperand() = store)
//  , count(Instruction i |
//      exists(PhiInstruction phi | phi.getAnOperand() = store |
//        i = phi.getAnOperand()
//      )
//    )

//Instruction getAPhiUse(Instruction i) {
//  result.(PhiInstruction).getAnOperand() = i
//}
//
//from StoreInstruction store, LoadInstruction load, string varname
//where load.getSourceValue() = getAPhiUse+(store)
//  and varname = concat(
//        store.getDestinationAddress().(VariableAddressInstruction)
//             .getVariable().(IRUserVariable).getVariable().getName()
//      , " ### "
//      )
//select varname, store, load

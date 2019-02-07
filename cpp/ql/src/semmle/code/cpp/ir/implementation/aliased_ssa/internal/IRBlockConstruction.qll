import SSAConstructionInternal
private import SSAConstruction as Construction
private import NewIR

import Cached
private cached module Cached {
  cached newtype TIRBlock = MkIRBlock(OldIR::IRBlock oldBlock)

  private OldIR::IRBlock getOldBlock(TIRBlock block) {
    block = MkIRBlock(result)
  }

  // The parameters to this predicate are carefully ordered to allow the QL
  // engine to use the predicate directly instead of computing a `#rank_range`
  // predicate.
  pragma[noinline]
  private predicate hasNewSparseIndex(TIRBlock block, Instruction instr, int sparseIndex) {
    exists(OldIR::Instruction oldInstr, int oldIndex |
      oldInstr = getOldBlock(block).getInstruction(oldIndex) and
      (
        sparseIndex = 2 * oldIndex and
        Construction::getOldInstruction(instr) = oldInstr
        or
        sparseIndex = 2 * oldIndex + 1 and
        instr = Construction::Chi(oldInstr)
      )
    )
  }

  cached Instruction getInstruction(TIRBlock block, int index) {
    result = rank[index + 1](Instruction instr, int sparseIndex |
        hasNewSparseIndex(block, instr, sparseIndex)
      |
        instr
        order by sparseIndex
      )
  }

  cached int getInstructionCount(TIRBlock block) {
    result =
      getOldBlock(block).getInstructionCount() +
      count(OldIR::Instruction oldInstr |
          oldInstr = getOldBlock(block).getAnInstruction() and
          exists(Construction::Chi(oldInstr))
        )
  }

  cached predicate blockSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    succ = MkIRBlock(getOldBlock(pred).getSuccessor(kind))
  }

  cached predicate blockSuccessor(TIRBlock pred, TIRBlock succ) {
    blockSuccessor(pred, succ, _)
  }

  cached predicate backEdgeSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    succ = MkIRBlock(getOldBlock(pred).getBackEdgeSuccessor(kind))
  }

  cached predicate blockImmediatelyDominates(TIRBlock dominator, TIRBlock block) {
    getOldBlock(dominator).immediatelyDominates(getOldBlock(block))
  }

  cached Instruction getFirstInstruction(TIRBlock block) {
    Construction::getOldInstruction(result) =
      getOldBlock(block).getFirstInstruction()
  }
}

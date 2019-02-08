private import IRInternal
import semmle.code.cpp.ir.implementation.raw.Instruction
import semmle.code.cpp.ir.implementation.EdgeKind

private predicate startsBasicBlock(Instruction instr) {
  not instr instanceof PhiInstruction and
  (
    count(Instruction predecessor |
      instr = predecessor.getASuccessor()
    ) != 1 or  // Multiple predecessors or no predecessor
    exists(Instruction predecessor |
      instr = predecessor.getASuccessor() and
      strictcount(Instruction other |
        other = predecessor.getASuccessor()
      ) > 1
    ) or  // Predecessor has multiple successors
    exists(Instruction predecessor, EdgeKind kind |
      instr = predecessor.getSuccessor(kind) and
      not kind instanceof GotoEdge
    ) or  // Incoming edge is not a GotoEdge
    exists(Instruction predecessor |
      instr = Construction::getInstructionBackEdgeSuccessor(predecessor, _)
    )  // A back edge enters this instruction
  )
}

private predicate isEntryBlock(TIRBlock block) {
  block = MkIRBlock(any(EnterFunctionInstruction enter))
}

import Cached
private cached module Cached {
  cached newtype TIRBlock =
    MkIRBlock(Instruction firstInstr) {
      startsBasicBlock(firstInstr)
    }

  /** Holds if `i2` follows `i1` in a `IRBlock`. */
  private predicate adjacentInBlock(Instruction i1, Instruction i2) {
    exists(GotoEdge edgeKind | i2 = i1.getSuccessor(edgeKind)) and
    not startsBasicBlock(i2)
  }

  /** Holds if `i` is the `index`th instruction the block starting with `first`. */
  private Instruction getInstructionFromFirst(Instruction first, int index) =
    shortestDistances(startsBasicBlock/1, adjacentInBlock/2)(first, result, index)

  /** Holds if `i` is the `index`th instruction in `block`. */
  cached Instruction getInstruction(TIRBlock block, int index) {
    result = getInstructionFromFirst(getFirstInstruction(block), index)
  }

  cached int getInstructionCount(TIRBlock block) {
    result = 1 + max(int index | exists(getInstruction(block, index)))
  }

  cached predicate blockSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    exists(Instruction predLast, Instruction succFirst |
      predLast = getInstruction(pred, getInstructionCount(pred) - 1) and
      succFirst = predLast.getSuccessor(kind) and
      succ = MkIRBlock(succFirst)
    )
  }

  cached predicate backEdgeSuccessor(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    backEdgeSuccessorRaw(pred, succ, kind)
    or
    forwardEdgeRaw+(pred, pred) and
    blockSuccessor(pred, succ, kind)
  }

  /**
   * Holds if there is an edge from `pred` to `succ` that is not a back edge.
   */
  private predicate forwardEdgeRaw(TIRBlock pred, TIRBlock succ) {
    exists(EdgeKind kind |
      blockSuccessor(pred, succ, kind) and
      not backEdgeSuccessorRaw(pred, succ, kind)
    )
  }

  /**
   * Holds if the `kind`-edge from `pred` to `succ` is a back edge according to
   * `Construction`.
   *
   * There could be loops of non-back-edges if there is a flaw in the IR
   * construction or back-edge detection, and this could cause non-termination
   * of subsequent analysis. To prevent that, a subsequent predicate further
   * classifies all edges as back edges if they are involved in a loop of
   * non-back-edges.
   */
  private predicate backEdgeSuccessorRaw(TIRBlock pred, TIRBlock succ, EdgeKind kind) {
    exists(Instruction predLast, Instruction succFirst |
      predLast = getInstruction(pred, getInstructionCount(pred) - 1) and
      succFirst = Construction::getInstructionBackEdgeSuccessor(predLast, kind) and
      succ = MkIRBlock(succFirst)
    )
  }

  cached predicate blockSuccessor(TIRBlock pred, TIRBlock succ) {
    blockSuccessor(pred, succ, _)
  }

  cached predicate blockImmediatelyDominates(TIRBlock dominator, TIRBlock block) =
    idominance(isEntryBlock/1, blockSuccessor/2)(_, dominator, block)
}

Instruction getFirstInstruction(TIRBlock block) {
  block = MkIRBlock(result)
}

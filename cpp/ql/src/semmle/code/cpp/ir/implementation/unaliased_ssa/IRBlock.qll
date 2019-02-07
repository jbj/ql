private import internal.IRInternal
import Instruction
import semmle.code.cpp.ir.implementation.EdgeKind
private import internal.IRBlockConstruction

/**
 * A basic block in the IR. A basic block consists of a sequence of `Instructions` with the only
 * incoming edges at the beginning of the sequence and the only outgoing edges at the end of the
 * sequence.
 *
 * This class does not contain any members that query the predecessor or successor edges of the
 * block. This allows different classes that extend `IRBlockBase` to expose different subsets of
 * edges (e.g. ignoring unreachable edges).
 *
 * Most consumers should use the class `IRBlock`.
 */
class IRBlockBase extends TIRBlock {
  final string toString() {
    result = getFirstInstruction(this).toString()
  }

  final Location getLocation() {
    result = getFirstInstruction().getLocation()
  }
  
  final string getUniqueId() {
    result = getFirstInstruction(this).getUniqueId()
  }
  
  /**
   * Gets the zero-based index of the block within its function. This is used
   * by debugging and printing code only.
   */
  int getDisplayIndex() {
    this = rank[result + 1](IRBlock funcBlock |
      funcBlock.getEnclosingFunction() = getEnclosingFunction() |
      funcBlock order by funcBlock.getUniqueId()
    )
  }

  final Instruction getInstruction(int index) {
    result = getInstruction(this, index)
  }

  final PhiInstruction getAPhiInstruction() {
    Construction::getPhiInstructionBlockStart(result) = getFirstInstruction()
  }

  final Instruction getAnInstruction() {
    result = getInstruction(_) or
    result = getAPhiInstruction()
  }

  final Instruction getFirstInstruction() {
    result = getFirstInstruction(this)
  }

  final Instruction getLastInstruction() {
    result = getInstruction(getInstructionCount() - 1)
  }

  final int getInstructionCount() {
    result = strictcount(getInstruction(_))
  }

  final FunctionIR getEnclosingFunctionIR() {
    result = getFirstInstruction(this).getEnclosingFunctionIR()
  }

  final Function getEnclosingFunction() {
    result = getFirstInstruction(this).getEnclosingFunction()
  }
}

/**
 * A basic block with additional information about its predecessor and successor edges. Each edge
 * corresponds to the control flow between the last instruction of one block and the first
 * instruction of another block.
 */
class IRBlock extends IRBlockBase {
  final IRBlock getASuccessor() {
    blockSuccessor(this, result)
  }

  final IRBlock getAPredecessor() {
    blockSuccessor(result, this)
  }

  final IRBlock getSuccessor(EdgeKind kind) {
    blockSuccessor(this, result, kind)
  }

  final IRBlock getBackEdgeSuccessor(EdgeKind kind) {
    backEdgeSuccessor(this, result, kind)
  }

  final predicate immediatelyDominates(IRBlock block) {
    blockImmediatelyDominates(this, block)
  }

  final predicate strictlyDominates(IRBlock block) {
    blockImmediatelyDominates+(this, block)
  }

  final predicate dominates(IRBlock block) {
    strictlyDominates(block) or this = block
  }

  pragma[noinline]
  final IRBlock dominanceFrontier() {
    dominates(result.getAPredecessor()) and
    not strictlyDominates(result)
  }
  
  /**
   * Holds if this block is reachable from the entry point of its function
   */
  final predicate isReachableFromFunctionEntry() {
    this = getEnclosingFunctionIR().getEntryBlock() or
    getAPredecessor().isReachableFromFunctionEntry()
  }
}

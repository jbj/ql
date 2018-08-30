/**
 * Provides the `PrimitiveSubBasicBlock` class, used for partitioning basic blocks in
 * smaller pieces.
 */
private import PrimitiveBasicBlocks
private import ConstantExprs
private class Node = ControlFlowNodeBase;

/**
 * An abstract class that directs where in the control-flow graph a new
 * `PrimitiveSubBasicBlock` must start. If a `Node` is an instance of this
 * class, that node is guaranteed to be the first node in a `PrimitiveSubBasicBlock`.
 * If multiple libraries use the `PrimitiveSubBasicBlock` library, basic blocks may be
 * split in more places than either library expects, but nothing should break
 * as a direct result of that.
 */
abstract class PrimitiveSubBasicBlockCutNode extends Node {
  PrimitiveSubBasicBlockCutNode() {
    // Some control-flow nodes are not in any basic block. This includes
    // `Conversion`s, expressions that are evaluated at compile time, default
    // arguments, and `Function`s without implementation.
    exists(getPrimitiveBasicBlock(this))
  }
}

/**
 * A block that can be smaller than or equal to a `PrimitiveBasicBlock`. Use this class
 * when `Node` is too fine-grained and `PrimitiveBasicBlock` too
 * coarse-grained. Their successor graph is like that of basic blocks, except
 * that the blocks are split up with an extra edge right before any instance of
 * the abstract class `PrimitiveSubBasicBlockCutNode`. Users of this library must
 * therefore extend `PrimitiveSubBasicBlockCutNode` to direct where basic blocks will be
 * split up.
 */
class PrimitiveSubBasicBlock extends Node {
  PrimitiveSubBasicBlock() {
    this instanceof PrimitiveBasicBlock
    or
    this instanceof PrimitiveSubBasicBlockCutNode
  }

  /** Gets the basic block in which this `PrimitiveSubBasicBlock` is contained. */
  PrimitiveBasicBlock getPrimitiveBasicBlock() {
    result = getPrimitiveBasicBlock(this)
  }

  /**
   * Holds if this `PrimitiveSubBasicBlock` comes first in its basic block. This is the
   * only condition under which a `PrimitiveSubBasicBlock` may have multiple
   * predecessors.
   */
  predicate firstInBB() {
    exists(PrimitiveBasicBlock bb | this.getPosInBasicBlock(bb) = 0)
  }

  /**
   * Holds if this `PrimitiveSubBasicBlock` comes last in its basic block. This is the
   * only condition under which a `PrimitiveSubBasicBlock` may have multiple successors.
   */
  predicate lastInBB() {
    exists(PrimitiveBasicBlock bb |
      this.getPosInBasicBlock(bb) = countPrimitiveSubBasicBlocksInBasicBlock(bb) - 1
    )
  }

  /**
   * Gets the position of this `PrimitiveSubBasicBlock` in its containing basic block
   * `bb`, where `bb` is equal to `getPrimitiveBasicBlock()`.
   */
  int getPosInBasicBlock(PrimitiveBasicBlock bb) {
    exists(int nodePos, int rnk |
      bb = this.getPrimitiveBasicBlock() and
      this = bb.getNode(nodePos) and
      nodePos = rank[rnk](int i | exists(PrimitiveSubBasicBlock n | n = bb.getNode(i))) and
      result = rnk - 1
    )
  }

  /** Gets a successor in the control-flow graph of `PrimitiveSubBasicBlock`s. */
  PrimitiveSubBasicBlock getASuccessor() {
    this.lastInBB() and
    pbbSuccessor(this.getPrimitiveBasicBlock(), result)
    or
    exists(PrimitiveBasicBlock bb |
      result.getPosInBasicBlock(bb) = this.getPosInBasicBlock(bb) + 1
    )
  }

  /**
   * Gets the `pos`th control-flow node in this `PrimitiveSubBasicBlock`. Positions
   * start from 0, and the node at position 0 always exists and compares equal
   * to `this`.
   */
  Node getNode(int pos) {
    exists(PrimitiveBasicBlock bb | bb = this.getPrimitiveBasicBlock() |
      exists(int thisPos | this = bb.getNode(thisPos) |
        result = bb.getNode(thisPos + pos) and
        pos >= 0 and
        pos < this.getNumberOfNodes()
      )
    )
  }

  /** Gets a control-flow node in this `PrimitiveSubBasicBlock`. */
  Node getANode() {
    result = this.getNode(_)
  }

  /** Holds if `this` contains `node`. */
  predicate contains(Node node) {
    node = this.getANode()
  }

  /** Gets a predecessor in the control-flow graph of `PrimitiveSubBasicBlock`s. */
  PrimitiveSubBasicBlock getAPredecessor() {
    result.getASuccessor() = this
  }

  /**
   * Gets the number of control-flow nodes in this `PrimitiveSubBasicBlock`. There is
   * always at least one.
   */
  int getNumberOfNodes() {
    exists(PrimitiveBasicBlock bb | bb = this.getPrimitiveBasicBlock() |
      exists(int thisPos | this = bb.getNode(thisPos) |
        this.lastInBB() and
        result = bb.length() - thisPos
        or
        exists(PrimitiveSubBasicBlock succ, int succPos |
          succ.getPosInBasicBlock(bb) = this.getPosInBasicBlock(bb) + 1 and
          bb.getNode(succPos) = succ and
          result = succPos - thisPos
        )
      )
    )
  }

  /** Gets the last control-flow node in this `PrimitiveSubBasicBlock`. */
  Node getEnd() {
    result = this.getNode(this.getNumberOfNodes() - 1)
  }

  /** Gets the first control-flow node in this `PrimitiveSubBasicBlock`. */
  Node getStart() {
    result = this
  }
}

private predicate pbbSuccessor(PrimitiveBasicBlock b1, PrimitiveBasicBlock b2) {
  b1.getASuccessor() = b2 and
  successors_before_adapted(b1.getNode(b1.length() - 1), b2)
}

private PrimitiveBasicBlock getPrimitiveBasicBlock(Node node) {
  result.getANode() = node
}

/** Gets the number of `PrimitiveSubBasicBlock`s in the given basic block. */
private int countPrimitiveSubBasicBlocksInBasicBlock(PrimitiveBasicBlock bb) {
  result = strictcount(PrimitiveSubBasicBlock sbb | sbb.getPrimitiveBasicBlock() = bb)
}

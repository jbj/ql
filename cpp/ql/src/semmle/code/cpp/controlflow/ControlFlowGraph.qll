import cpp
import BasicBlocks
private import semmle.code.cpp.controlflow.internal.ConstantExprs

/**
 * A control-flow node is either a statement or an expression; in addition,
 * functions are control-flow nodes representing the exit point of the
 * function. The graph represents one possible evaluation order out of all the
 * ones the compiler might have picked.
 *
 * Control-flow nodes have successors and predecessors at the expression level,
 * so control flow is accurately represented in expressions as well as between
 * statements. Statements and initializers precede their contained expressions,
 * and expressions deeper in the tree precede those higher up; for example, the
 * statement `x = y + 1` gets a control-flow graph that looks like
 *
 * ```
 * ExprStmt -> y -> 1 -> (+) -> x -> (=)
 * ```
 *
 * The first control-flow node in a function is the body of the function (a
 * block), and the last is the function itself, which is used to represent the
 * exit point.
 *
 * Each `throw` expression or `Handler` has a path (along any necessary
 * destructor calls) to its nearest enclosing `Handler` within the same
 * function, or to the exit point of the function if there is no such
 * `Handler`. There are no edges from function calls to `Handler`s.
 */
class ControlFlowNode extends Locatable, ControlFlowNodeBase {
  ControlFlowNode getASuccessor() { successors_adapted(this, result) }

  ControlFlowNode getAPredecessor() { this = result.getASuccessor() }

  /** Gets the function containing this control-flow node. */
  Function getControlFlowScope() {
    none() // overridden in subclasses
  }

  /** Gets the smallest statement containing this control-flow node. */
  Stmt getEnclosingStmt() {
    none() // overridden in subclasses
  }

  /**
   * Holds if this node is the top-level expression of a conditional statement,
   * meaning that `this.getATrueSuccessor()` or `this.getAFalseSuccessor()`
   * will have a result.
   */
  predicate isCondition() {
    exists(this.getATrueSuccessor()) or
    exists(this.getAFalseSuccessor())
  }

  /**
   * Gets a node such that the control-flow edge `(this, result)` may be
   * taken when this expression is true.
   */
  ControlFlowNode getATrueSuccessor() {
    truecond_base(this, result) and
    result = getASuccessor()
  }

  /**
   * Gets a node such that the control-flow edge `(this, result)` may be
   * taken when this expression is false.
   */
  ControlFlowNode getAFalseSuccessor() {
    falsecond_base(this,result) and
    result = getASuccessor()
  }

  BasicBlock getBasicBlock() {
    result.getANode() = this
  }
}

import Cached
private cached module Cached {
  private predicate entry(ControlFlowNode n) {
    exists(Function f | f.getEntryPoint() = n)
    or
    n instanceof CatchBlock
  }

  private predicate splitty(ControlFlowNode n) {
    strictcount(ControlFlowNode succ | successors_extended(n, succ)) > 1
  }

  private class Interesting extends ControlFlowNode {
    Interesting() {
      splitty(this)
      or
      not successors_pruned(this, _)
      or
      callRequiringRecursiveAnalysis(this)
    }
  }

  private
  predicate interestingAncestorEdge(ControlFlowNode n1, ControlFlowNode n2) {
    not n1 instanceof Interesting and
    successors_extended(n1, n2) and
    not impossibleEdge(n1, n2)
  }

  private predicate interesting_edge(ControlFlowNode n1, ControlFlowNode n2) {
    (
      entry(n1)
      or
      n1 instanceof Interesting
    ) and
    exists(ControlFlowNode ancestor |
      successors_pruned(n1, ancestor) and
      ancestorOf(ancestor, n2)
    )
  }

  // If `interesting` is reachable, then `n` is too.
  private predicate ancestorOf(
      ControlFlowNode n, Interesting interesting) {
    interestingAncestorEdge*(n, interesting)
  }

  /**
   * Holds if the control-flow node `n` is reachable, meaning that either
   * it is an entry point, or there exists a path in the control-flow
   * graph of its function that connects an entry point to it.
   * Compile-time constant conditions are taken into account, so that
   * the call to `f` is not reachable in `if (0) f();` even if the
   * `if` statement as a whole is reachable.
   */
  cached
  predicate reachable(ControlFlowNode n)
  {
    // TODO: work backwards from each call or split  Ignore joins? Collapse
    // everything uninteresting before doing reachability.
    locallyReachable(n)
    or
    // This recursive case looks innocent, but it's actually very tricky. It
    // desugars to an `and` with recursion on both sides, which means that the
    // deltafication involves the full product rule:
    //
    //     (P and Q)' = (P' and Q) or (Q' * P)
    //
    // In other words, in computing the next delta it does not suffice to look
    // at the previous delta. This makes reachability slow to compute. The
    // workaround is to make the base case above as large as possible so we
    // limit the number of iterations necessary in the general predicate.
    reachable(n.getAPredecessor())
  }

  /** Holds if `condition` always evaluates to a nonzero value. */
  cached
  predicate conditionAlwaysTrue(Expr condition) {
    conditionAlways(condition, true)
  }

  /** Holds if `condition` always evaluates to zero. */
  cached
  predicate conditionAlwaysFalse(Expr condition) {
    conditionAlways(condition, false)
    or
    // If a loop condition evaluates to false upon entry, it will always
    // be false
    loopConditionAlwaysUponEntry(_, condition, false)
  }

  /**
   * The condition `condition` for the loop `loop` is provably `true` upon entry.
   * That is, at least one iteration of the loop is guaranteed.
   */
  cached
  predicate loopConditionAlwaysTrueUponEntry(ControlFlowNode loop, Expr condition) {
    loopConditionAlwaysUponEntry(loop, condition, true)
  }
}

private predicate conditionAlways(Expr condition, boolean b) {
  exists(ConditionEvaluator x, int val |
    val = x.getValue(condition) |
    val != 0 and b = true
    or
    val = 0 and b = false
  )
}

private predicate loopConditionAlwaysUponEntry(ControlFlowNode loop, Expr condition, boolean b) {
  exists(LoopEntryConditionEvaluator x, int val |
    x.isLoopEntry(condition, loop) and
    val = x.getValue(condition) |
    val != 0 and b = true
    or
    val = 0 and b = false
  )
}

/**
 * An element that is convertible to `ControlFlowNode`. This class is similar
 * to `ControlFlowNode` except that is has no member predicates apart from
 * `toString`.
 *
 * This class can be used as base class for classes that want to inherit the
 * extent of `ControlFlowNode` without inheriting its public member predicates.
 */
class ControlFlowNodeBase extends ElementBase, @cfgnode {
}

predicate truecond_base(ControlFlowNodeBase n1, ControlFlowNodeBase n2) {
  truecond(unresolveElement(n1), unresolveElement(n2))
}

predicate falsecond_base(ControlFlowNodeBase n1, ControlFlowNodeBase n2) {
  falsecond(unresolveElement(n1), unresolveElement(n2))
}

/**
 * An abstract class that can be extended to add additional edges to the
 * control-flow graph. Instances of this class correspond to the source nodes
 * of such edges, and the predicate `getAnEdgeTarget` should be overridden to
 * produce the target nodes of each source.
 *
 * Changing the control-flow graph in some queries and not others can be
 * expensive in execution time and disk space. Most cached predicates in the
 * library depend on the control-flow graph, so these predicates will be
 * computed and cached for each variation of the control-flow graph
 * that is used.
 *
 * Edges added by this class will still be removed by the library if they
 * appear to be unreachable. See the documentation on `ControlFlowNode` for
 * more information about the control-flow graph.
 */
abstract class AdditionalControlFlowEdge extends ControlFlowNodeBase {
  /** Gets a target node of this edge, where the source node is `this`. */
  abstract ControlFlowNodeBase getAnEdgeTarget();
}

/**
 * Holds if there is a control-flow edge from `source` to `target` in either
 * the extractor-generated control-flow graph or in a subclass of
 * `AdditionalControlFlowEdge`. Use this relation instead of `successors`.
 */
predicate successors_extended(
    ControlFlowNodeBase source, ControlFlowNodeBase target) {
  successors(unresolveElement(source), unresolveElement(target))
  or
  source.(AdditionalControlFlowEdge).getAnEdgeTarget() = target
}

import cpp

/*
TODO: difficulties:
- Particular AST nodes
  - Short-circuiting operators
  - New-expressions
  - throw -> handler
  - StmtExpr and ExprStmt
  - Initializer
  - BlockExpr??? (clang extension)
- The nodes that may or may not have children at all
  - ReturnStmt, BlockStmt, ThrowStmt, PostOrderNode
  - could firstChild and lastChild return something special? Like the node itself.
    - beforeFirstChild returns (node itself, before)
      afterLastChild returns (node itself, before)
      Is that good enough for ThrowStmt?
- lastControlFlowNodeBeforeDestructors and following_destructor
  - Can we just construct the CFG and then inject these calls?
 */

private class Node = ControlFlowNodeBase;

private class Pos extends int {
  // This is to make sure we get compile errors in code that forgets to restrict a `Pos`.
  bindingset[this]
  Pos() { any() }

  // TODO: inline these?
  predicate isBefore() { this = -1 }
  predicate isAt() { this = 0 }
  predicate isAfter() { this = 1 }

  pragma[inline]
  predicate nodeBefore(Node n, Node nEq) { this.isBefore() and n = nEq }
  pragma[inline]
  predicate nodeAt(Node n, Node nEq) { this.isAt() and n = nEq }
  pragma[inline]
  predicate nodeAfter(Node n, Node nEq) { this.isAfter() and n = nEq }
}

private class PostOrderNode extends Node {
  PostOrderNode() {
    this instanceof Expr and
    not this instanceof ShortCircuitOperator and
    not this instanceof Conversion // not in CFG
  }
}

// TODO: Does this belong in PostOrderNode and PreOrderNode?
private Node controlOrderChild(Node n, int i) {
  result = n.(PostOrderNode).(Expr).getChild(i) and
  not n instanceof Assignment // they go from right to left
  or
  result = n.(Stmt).getChild(i)
  // TODO: assignment
  // TODO: more cases
  // TODO: squeeze children together with rank
}

private Node lastControlOrderChild(Node n) {
  result = controlOrderChild(n, max(int i | exists(controlOrderChild(n, i))))
}

private predicate normalEdge(Node n1, Pos p1, Node n2, Pos p2) {
  // -> child1 -> ... -> childN -> @self ->
  exists(PostOrderNode pon |
    n1 = pon and
    p1.isBefore() and
    controlOrderChild(n1, 0) = n2 and
    p2.isBefore()
    or
    exists(int i |
      n1 = controlOrderChild(pon, i) and
      p1.isAfter() and
      n1 = controlOrderChild(pon, i+1) and
      p2.isBefore()
    )
    or
    n1 = lastControlOrderChild(pon) and
    p1.isAfter() and
    n2 = pon and
    p2.isAt()
    or
    // Short circuit if there are no children
    not exists(lastControlOrderChild(pon)) and
    n1 = pon and
    p1.isBefore() and
    n2 = pon and
    p2.isAt()
    or
    n1 = pon and
    p1.isAt() and
    n2 = pon and
    p2.isAfter()
  )
  or
  // All statements start with themselves.
  n1.(Stmt) = n2 and
  p1.isBefore() and
  p2.isAt()
  or
  // -> op -> child1 -> ...
  exists(ShortCircuitOperator op |
    p1.nodeBefore(n1, op) and
    p2.nodeAt(n2, op)
    or
    p1.nodeAt(n1, op) and
    p2.nodeBefore(n2, controlOrderChild(op, 0))
  )
  or
  // -> {} -> child1 -> ... -> childN ->
  exists(Block b |
    p1.nodeBefore(n1, b) and
    p2.nodeAt(n2, b)
    or
    p1.nodeAt(n1, b) and
    p2.nodeBefore(n2, controlOrderChild(b, 0))
    or
    exists(int i |
      p1.nodeAfter(n1, controlOrderChild(b, i)) and
      p2.nodeBefore(n2, controlOrderChild(b, i+1))
    )
    or
    p1.nodeAfter(n1, lastControlOrderChild(b)) and
    p2.nodeAfter(n2, b)
    or
    // Short circuit if there are no children
    p1.nodeAt(n1, b) and
    p2.nodeAfter(n2, b)
  )
  or
  // -> initializer -> expr ->
  exists(Initializer init, Expr e | e = init.getExpr() |
    p1.nodeBefore(n1, init) and
    p2.nodeAt(n2, init)
    or
    p1.nodeAt(n1, init) and
    p2.nodeBefore(n2, e)
    or
    p1.nodeAfter(n1, e) and
    p2.nodeAfter(n2, init)
  )
  // return [-> expr] ->
}

private class ProperConditionContext extends Expr {
  ProperConditionContext() {
    //exists(ControlStructure cs |
    //  // TODO: exclude all switch statements or only non-Boolean ones?
    //  cs.getControllingExpr()
    this instanceof LogicalAndExpr
    or
    this instanceof LogicalOrExpr
    or
    this instanceof ConditionalExpr
  }
}

private class ShortCircuitOperator extends Expr {
  ShortCircuitOperator() {
    this instanceof LogicalAndExpr
    or
    this instanceof LogicalOrExpr
    or
    this instanceof ConditionalExpr
  }
}

/**
 * Holds if `test` is the test of a control-flow construct that will always
 * have a true and a false edge out of it, where the edge goes to before
 * `targetBefore` when `test` evaluates to `truth`.
 */
private predicate conditionJumpsTop(Expr test, boolean truth, Node targetNode, Pos targetPos) {
  exists(IfStmt s | test = s.getCondition() |
    truth = true and
    targetPos.nodeBefore(targetNode, s.getThen())
    or
    truth = false and
    targetPos.nodeBefore(targetNode, s.getElse())
  )
  or
  exists(ConditionalExpr e | test = e.getCondition() |
    truth = true and
    targetPos.nodeBefore(targetNode, e.getThen())
    or
    truth = false and
    targetPos.nodeBefore(targetNode, e.getElse())
  )
}

// Needed for `x = a && b`, where the target is after `a && b`.
private predicate conditionJumps(Expr test, boolean truth, Node targetNode, Pos targetPos) {
  conditionJumpsTop(test, truth, targetNode, targetPos)
  or
  // TODO: This is wrong. When true and false go to the same place, it's just a
  // normal edge. But maybe we should fix this up via post-processing.
  not conditionJumpsTop(test, _, _, _) and
  test instanceof ShortCircuitOperator and
  targetPos.nodeAfter(targetNode, test) and
  (truth = false or truth = true)
  or
  exists(ConditionalExpr e |
    (test = e.getThen() or test = e.getElse()) and
    conditionJumps(e, truth, targetNode, targetPos)
  )
  or
  exists(LogicalAndExpr e |
    test = e.getLeftOperand() and
    truth = true and
    targetNode = e.getRightOperand() and
    targetPos.isBefore()
    or
    test = e.getLeftOperand() and
    truth = false and
    conditionJumps(e, false, targetNode, targetPos)
    or
    test = e.getRightOperand() and
    conditionJumps(e, truth, targetNode, targetPos)
  )
}

//private predicate branchesTo(boolean truth, Expr test, Expr context) {
//  
//}

/**
 * Holds if there's a "true" edge from _after_ n1 to _before_ n2.
 */
private predicate trueEdge(Node n1, Node n2) {
  //exists(WhileStmt 
  // TODO: needs general treatment, including short-circuiting operators
  none()
}

select 1

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
    // TODO: positive list instead of negative list
    this instanceof Expr and
    not this instanceof ShortCircuitOperator and
    not this instanceof Conversion // not in CFG
  }
}

private class PreOrderNode extends Node {
  PreOrderNode() {
    this instanceof Initializer
    or
    this instanceof DeclStmt
    or
    this instanceof Block
  }
}

private Node controlOrderChildSparse(Node n, int i) {
  result = n.(PostOrderNode).(Expr).getChild(i) and
  not n instanceof Assignment // they go from right to left
  or
  n = any(Assignment a |
    i = 0 and result = a.getRValue()
    or
    i = 1 and result = a.getLValue()
  )
  or
  i = 0 and result = n.(Initializer).getExpr()
  or
  result = n.(PreOrderNode).(Stmt).getChild(i)
  or
  result = n.(DeclStmt).getDeclaration(i).(Variable).getInitializer()
}

private Node controlOrderChild(Node n, int i) {
  result = rank[i + 1](Node child, int childIdx |
    child = controlOrderChildSparse(n, childIdx)
  | child
    order by childIdx
  )
}

private Node lastControlOrderChild(Node n) {
  result = controlOrderChild(n, max(int i | exists(controlOrderChild(n, i))))
}

private predicate normalEdge(Node n1, Pos p1, Node n2, Pos p2) {
  // child0 -> ... -> childN
  exists(Node n, int i |
    p1.nodeAfter(n1, controlOrderChild(n, i)) and
    p2.nodeBefore(n2, controlOrderChild(n, i+1))
  )
  or
  // -> [children ->] PostOrderNode ->
  exists(PostOrderNode n |
    p1.nodeBefore(n1, n) and
    p2.nodeBefore(n2, controlOrderChild(n, 0))
    or
    p1.nodeAfter(n1, lastControlOrderChild(n)) and
    p2.nodeAt(n2, n)
    or
    // Short circuit if there are no children
    not exists(lastControlOrderChild(n)) and
    p1.nodeBefore(n1, n) and
    p2.nodeAt(n2, n)
    or
    p1.nodeAt(n1, n) and
    p2.nodeAfter(n2, n)
  )
  or
  // -> PreOrderNode -> [children ->]
  exists(PreOrderNode n |
    p1.nodeBefore(n1, n) and
    p2.nodeAt(n2, n)
    or
    p1.nodeAt(n1, n) and
    p2.nodeBefore(n2, controlOrderChild(n, 0))
    or
    p1.nodeAfter(n1, lastControlOrderChild(n)) and
    p2.nodeAfter(n2, n)
    or
    // Short circuit if there are no children
    not exists(lastControlOrderChild(n)) and
    p1.nodeAt(n1, n) and
    p2.nodeAfter(n2, n)
  )
  or
  // All statements start with themselves.
  n1.(Stmt) = n2 and
  p1.isBefore() and
  p2.isAt()
  or
  // -> ShortCircuitOperator -> child1 -> ...
  exists(ShortCircuitOperator op |
    p1.nodeBefore(n1, op) and
    p2.nodeAt(n2, op)
    or
    p1.nodeAt(n1, op) and
    p2.nodeBefore(n2, controlOrderChild(op, 0))
  )
  or
  // ReturnStmt [-> Expr] -> Function
  exists(ReturnStmt ret |
    exists(Expr e | e = ret.getExpr() |
      p1.nodeAt(n1, ret) and
      p2.nodeBefore(n2, e)
      or
      p1.nodeAfter(n1, e) and
      p2.nodeAt(n2, ret.getEnclosingFunction())
    )
    or
    not exists(ret.getExpr()) and
    p1.nodeAt(n1, ret) and
    p2.nodeAt(n2, ret.getEnclosingFunction())
  )
  or
  // IfStmt -> condition ; { then, else } ->
  exists(IfStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getCondition())
    or
    p1.nodeAfter(n1, s.getThen()) and
    p2.nodeAfter(n2, s)
    or
    p1.nodeAfter(n1, s.getElse()) and
    p2.nodeAfter(n2, s)
  )
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

/**
 * Holds if there should be a `truth`-labeled edge from _after_ `test` to
 * `(targetPos, targetNode)`.
 */
private predicate conditionJumps(Expr test, boolean truth, Node targetNode, Pos targetPos) {
  conditionJumpsTop(test, truth, targetNode, targetPos)
  or
  // When true and false go to the same place, it's just a normal edge. But we
  // can fix this up via post-processing.
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

private predicate groupMember(Node memberNode, Pos memberPos, Node atNode) {
  memberNode = atNode and
  memberPos.isAt()
  or
  exists(Node succNode, Pos succPos |
    groupMember(succNode, succPos, atNode) and
    not memberPos.isAt()
  |
    normalEdge(memberNode, memberPos, succNode, succPos)
    or
    // TODO: If we cut groups at `isAt` positions, can we then recover the jump
    // edges? But we can't cut at any other positions.
    conditionJumps(memberNode, _, succNode, succPos) and
    memberPos.isAfter()
  )
}

select 1

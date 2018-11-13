import cpp

/*
TODO: difficulties:
- Particular AST nodes
  - New-expressions
  - throw -> handler
  - StmtExpr
  - CommaExpr
  - BlockExpr??? (clang extension)
  - Unstructured switch statements
    - Variable init at start of switch block
  - VlaDeclStmt
- The nodes that may or may not have children at all
  - ReturnStmt, BlockStmt, ThrowStmt, PostOrderNode
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
    // TODO: also for the block after a switch?
    this instanceof Block
    or
    this instanceof LabelStmt
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
    // Short circuit if there are no children.
    // TODO: We could make a predicate straightLine(Node scope, int i, Node n,
    // Pos p), where child nodes are inserted with gaps between them.
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
  // TODO: does that mean we should never make edges to _before_ a statement
  // but always _at_ the statement? Or is that premature optimization?
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
    p2.nodeBefore(n2, op.getChild(0))
  )
  or
  // EmptyStmt ->
  exists(EmptyStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeAfter(n2, s)
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
  or
  // WhileStmt -> condition ; body -> condition
  exists(WhileStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getCondition())
    or
    p1.nodeAfter(n1, s.getStmt()) and
    p2.nodeBefore(n2, s.getCondition())
  )
  or
  // DoStmt -> body ; body -> condition
  exists(DoStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getStmt())
    or
    p1.nodeAfter(n1, s.getStmt()) and
    p2.nodeBefore(n2, s.getCondition())
  )
  or
  // ForStmt -> init -> condition ; body -> update -> condition
  exists(ForStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getInitialization())
    or
    p1.nodeAfter(n1, s.getInitialization()) and
    p2.nodeBefore(n2, s.getCondition())
    or
    p1.nodeAfter(n1, s.getStmt()) and
    p2.nodeBefore(n2, s.getUpdate())
    or
    p1.nodeAfter(n1, s.getUpdate()) and
    p2.nodeBefore(n2, s.getCondition())
  )
  or
  // ExprStmt -> expr ->
  exists(ExprStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getExpr())
    or
    p1.nodeAfter(n1, s.getExpr()) and
    p2.nodeAfter(n2, s)
  )
  or
  // JumpStmt -> target
  // TODO: should the extractor continue to compute these targets?
  exists(JumpStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getTarget())
  )
  or
  // SwitchCase ->
  // (note: doesn't evaluate its argument)
  exists(SwitchCase s |
    p1.nodeAt(n1, s) and
    p2.nodeAfter(n2, s)
  )
  or
  // SwitchStmt -> expr -> block -> cases
  exists(SwitchStmt s |
    p1.nodeAt(n1, s) and
    p2.nodeBefore(n2, s.getExpr())
    or
    p1.nodeAfter(n1, s.getExpr()) and
    p2.nodeBefore(n2, s.getStmt())
    or
    exists(SwitchCase case |
      case.getSwitchStmt() = s and
      p1.nodeAt(n1, s.getStmt()) and
      p2.nodeBefore(n2, case)
    )
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
    or
    not exists(s.getElse()) and
    truth = false and
    targetPos.nodeAfter(targetNode, s)
  )
  or
  exists(Loop l | test = l.getCondition() |
    truth = true and
    targetPos.nodeBefore(targetNode, l.getStmt())
    or
    truth = false and
    targetPos.nodeAfter(targetNode, l)
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
  // fix this up via post-processing.
  not conditionJumpsTop(test, _, _, _) and
  test instanceof ShortCircuitOperator and
  targetPos.nodeAfter(targetNode, test) and
  (truth = false or truth = true)
  or
  exists(ConditionalExpr e |
    (test = e.getThen() or test = e.getElse()) and
    conditionJumps(e, truth, targetNode, targetPos)
  )
  // TODO: handle `!` better in the future. Like this?
  //or
  //exists(NotExpr e |
  //  test = e.getOperand() and
  //  conditionJumps(e, truth.booleanNot(), targetNode, targetPos)
  //)
  or
  exists(LogicalAndExpr e |
    test = e.getLeftOperand() and
    truth = true and
    targetPos.nodeBefore(targetNode, e.getRightOperand())
    or
    test = e.getLeftOperand() and
    truth = false and
    conditionJumps(e, false, targetNode, targetPos)
    or
    test = e.getRightOperand() and
    conditionJumps(e, truth, targetNode, targetPos)
  )
  or
  exists(LogicalOrExpr e |
    test = e.getLeftOperand() and
    truth = false and
    targetPos.nodeBefore(targetNode, e.getRightOperand())
    or
    test = e.getLeftOperand() and
    truth = true and
    conditionJumps(e, true, targetNode, targetPos)
    or
    test = e.getRightOperand() and
    conditionJumps(e, truth, targetNode, targetPos)
  )
}

private predicate normalGroupMember(Node memberNode, Pos memberPos, Node atNode) {
  memberNode = atNode and
  memberPos.isAt()
  or
  // TODO: this is a transitive closure. If it's slow, we can speed it up with
  // FastTC (and IPA).
  exists(Node succNode, Pos succPos |
    normalGroupMember(succNode, succPos, atNode) and
    not memberPos.isAt() and
    normalEdge(memberNode, memberPos, succNode, succPos)
  )
}

private predicate precedesCondition(Node memberNode, Pos memberPos, Node test) {
  memberNode = test and
  memberPos.isAfter()
  or
  // TODO: this is a transitive closure. If it's slow, we can speed it up with
  // FastTC (and IPA).
  exists(Node succNode, Pos succPos |
    precedesCondition(succNode, succPos, test) and
    normalEdge(memberNode, memberPos, succNode, succPos) and
    // Unlike the similar TC in normalGroupMember we're here including the
    // At-node in the group. This should generalize better to the case where
    // the base case isn't always an After-node.
    not succPos.isAt()
  )
}

// To find true/false edges, search forward and backward among the ordinary
// half-edges from a true/false half-edge, stopping at At-nodes. Then link,
// with true/false, any At-nodes found backwrads with any At-nodes found
// forward.
private predicate conditionalSuccessor(Node n1, boolean truth, Node n2) {
  // TODO: this is a join of some rather large relations. It's possible that
  // some of them should be cut down with manual magic before being joined.
  exists(Node test, Node targetNode, Pos targetPos |
    precedesCondition(n1, any(Pos at | at.isAt()), test) and
    conditionJumps(test, truth, targetNode, targetPos) and
    normalGroupMember(targetNode, targetPos, n2)
  )
}

predicate qlCFGSuccessor(Node n1, Node n2) {
  exists(Node memberNode, Pos memberPos |
    normalEdge(n1, any(Pos at | at.isAt()), memberNode, memberPos) and
    normalGroupMember(memberNode, memberPos, n2)
  )
  or
  conditionalSuccessor(n1, _, n2)
}

predicate qlCFGTrueSuccessor(Node n1, Node n2) {
  conditionalSuccessor(n1, true, n2) and
  not conditionalSuccessor(n1, false, n2)
}

predicate qlCFGFalseSuccessor(Node n1, Node n2) {
  conditionalSuccessor(n1, false, n2) and
  not conditionalSuccessor(n1, true, n2)
}

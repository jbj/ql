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
  - Pointer-to-member call and access
- The nodes that may or may not have children at all
  - ReturnStmt, BlockStmt, ThrowStmt, PostOrderNode
- Nodes with optional children
  - IfStmt (else), ForStmt (all three)
- lastControlFlowNodeBeforeDestructors and following_destructor
  - Can we just construct the CFG and then inject these calls?
- Synthetic destructor calls. I've taken them out of the reference in the
  comparisons until there is a solution.
 */

private class Node = ControlFlowNodeBase;

/**
 * For compatibility with the extractor-generated CFG, the QL-generated CFG
 * will only be produced for nodes in this class.
 */
private class SupportedNode extends Node {
  SupportedNode() {
    // TODO: It appears the extractor doesn't produce CFG for free-standing
    // expressions. Why?
    exists(this.(ControlFlowNode).getControlFlowScope()) and
    not this.(Expr).getParent+() instanceof SwitchCase and
    not this.(Expr).getParent*() instanceof ConstructorInit and
    not this.(Expr).getParent+() instanceof ConditionDeclExpr
    // TODO: sizeof etc.?
  }
}

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
    not this instanceof ThrowExpr and
    not this instanceof Conversion // not in CFG
  }
}

private class PreOrderNode extends Node {
  PreOrderNode() {
    // TODO: this is to mimic the extractor. Why not extend to all initializers?
    this.(Initializer).getDeclaration() instanceof LocalVariable
    or
    this instanceof DeclStmt
    or
    // TODO: also for the block after a switch?
    this instanceof Block
    or
    this instanceof LabelStmt
    or
    this instanceof ExprStmt
    or
    this instanceof EmptyStmt
    or
    this instanceof AsmStmt
  }
}

private predicate isDeleteDestructorCall(DestructorCall c) {
  exists(DeleteExpr del | c = del.getDestructorCall())
  or
  exists(DeleteArrayExpr del | c = del.getDestructorCall())
}

private Node controlOrderChildSparse(Node n, int i) {
  result = n.(PostOrderNode).(Expr).getChild(i) and
  not n instanceof AssignExpr and // they go from right to left
  not n instanceof Call and // qualifier comes last
  not n instanceof ConditionDeclExpr and
  not n instanceof DeleteExpr and
  not n instanceof DeleteArrayExpr and
  not isDeleteDestructorCall(n) // already evaluated
  or
  n = any(AssignExpr a |
    i = 0 and result = a.getRValue()
    or
    i = 1 and result = a.getLValue()
  )
  or
  n = any(Call c |
    not isDeleteDestructorCall(c) and
    (
      i = -1 and result = c.(ExprCall).getExpr()
      or
      result = c.getArgument(i)
      or
      i = c.getNumberOfArguments() and result = c.getQualifier()
    )
  )
  or
  // TODO: this is compatible with the extractor but could be better
  n = any(ConditionDeclExpr cd |
    i = 0 and result = cd.getVariable().getInitializer().getExpr()
  )
  or
  n = any(DeleteExpr del |
    i = 0 and result = del.getExpr()
    or
    i = 1 and result = del.getDestructorCall()
    or
    i = 2 and result = del.getAllocatorCall()
  )
  or
  n = any(DeleteArrayExpr del |
    i = 0 and result = del.getExpr()
    or
    i = 1 and result = del.getDestructorCall()
    or
    i = 2 and result = del.getAllocatorCall()
  )
  or
  n = any(Initializer init |
    not exists(ConditionDeclExpr cd | init = cd.getVariable().getInitializer()) and
    i = 0 and result = n.(Initializer).getExpr()
  )
  or
  result = n.(PreOrderNode).(Stmt).getChild(i)
  or
  result = n.(DeclStmt).getDeclaration(i).(Variable).getInitializer()
}

private Node controlOrderChild(Node n, int i) {
  exists(int sparseIndex |
    result = controlOrderChildSparse(n, sparseIndex) and
    i = sparseIndex - min(int j | exists(controlOrderChildSparse(n, j)))
  )
}

private int controlOrderChildMax(Node n) {
  result = max(int i | exists(controlOrderChild(n, i)))
  or
  not exists(controlOrderChild(n, _)) and
  result = -1
}

private class Spec extends int {
  bindingset[this]
  Spec() { any() }

  predicate isBefore() { this = -1 }
  predicate isAt() { this = 0 }
  predicate isAfter() { this = 1 }
  predicate isAround() { this = 2 }
  predicate isBarrier() { this = 3 }

  Pos asLeftPos() {
    this = [-1 .. 1] and
    result = this
    or
    this.isAround() and
    result.isAfter()
  }

  Pos asRightPos() {
    this = [-1 .. 1] and
    result = this
    or
    this.isAround() and
    result.isBefore()
  }
}

private predicate straightLine(Node scope, int i, Node ni, Spec spec) {
  scope = any(PostOrderNode n |
    i = -1 and ni = n and spec.isBefore()
    or
    // TODO: here we can use the raw one if we also have a min instead of
    // hard-coding -1. Alternatively, just use min instead of rank to make
    // numbering start at 0.
    ni = controlOrderChild(scope, i) and spec.isAround()
    or
    i = controlOrderChildMax(scope) + 1 and ni = n and spec.isAt()
    or
    i = controlOrderChildMax(scope) + 2 and ni = n and spec.isAfter()
  )
  or
  scope = any(PreOrderNode n |
    i = -1 and ni = n and spec.isBefore()
    or
    i = 0 and ni = n and spec.isAt()
    or
    ni = controlOrderChild(scope, i - 1) and spec.isAround()
    or
    i = controlOrderChildMax(scope) + 2 and ni = n and spec.isAfter()
  )
  or
  scope = any(ShortCircuitOperator op |
    i = -1 and ni = op and spec.isBefore()
    or
    i = 0 and ni = op and spec.isAt()
    or
    i = 1 and ni = op.getChild(0) and spec.isBefore()
  )
  or
  scope = any(ThrowExpr e |
    i = -1 and ni = e and spec.isBefore()
    or
    i = 0 and ni = e.getExpr() and spec.isAround()
    or
    i = 1 and ni = e and spec.isAt()
    or
    i = 2 and ni = e.(ExceptionSource).getExceptionTarget() and spec.isAt()
  )
  or
  scope = any(ReturnStmt ret |
    i = -1 and ni = ret and spec.isAt()
    or
    i = 0 and ni = ret.getExpr() and spec.isAround()
    or
    i = 1 and ni = ret.getEnclosingFunction() and spec.isAt()
  )
  or
  scope = any(ForStmt s |
    // ForStmt [-> init]
    i = -1 and ni = s and spec.isAt()
    or
    i = 0 and ni = s.getInitialization() and spec.isAround()
    or
    if exists(s.getCondition())
    then (
      // ... -> before condition
      i = 1 and ni = s.getCondition() and spec.isBefore()
      or
      // body [-> update] -> before condition
      i = 2 and ni = s and spec.isBarrier()
      or
      i = 3 and ni = s.getStmt() and spec.isAfter()
      or
      i = 4 and ni = s.getUpdate() and spec.isAround()
      or
      i = 5 and ni = s.getCondition() and spec.isBefore()
    ) else (
      // ... -> body [-> update] -> before body
      i = 1 and ni = s.getStmt() and spec.isAround()
      or
      i = 2 and ni = s.getUpdate() and spec.isAround()
      or
      i = 3 and ni = s.getStmt() and spec.isBefore()
    )
  )
  or
  scope = any(TryStmt s |
    i = -1 and ni = s and spec.isAt()
    or
    i = 0 and ni = s.getStmt() and spec.isAround()
    or
    i = 1 and ni = s and spec.isAfter()
  )
}

private predicate straightLineRanked(Node scope, int rnk, Node nrnk, Spec spec) {
  exists(int i |
    straightLine(scope, i, nrnk, spec) and
    i = rank[rnk](int idx | straightLine(scope, idx, _, _))
  )
}

private predicate normalEdge(Node n1, Pos p1, Node n2, Pos p2) {
  exists(Node scope, int rnk, Spec spec1, Spec spec2 |
    straightLineRanked(scope, rnk, n1, spec1) and
    straightLineRanked(scope, rnk + 1, n2, spec2) and
    p1 = spec1.asLeftPos() and
    p2 = spec2.asRightPos()
  )
  or
  // All statements start with themselves.
  // TODO: does that mean we should never make edges to _before_ a statement
  // but always _at_ the statement? Or is that premature optimization?
  n1.(Stmt) = n2 and
  p1.isBefore() and
  p2.isAt()
  or
  // entry point -> Function
  // TODO: delete this later. Only for compatibility with extractor quirks. It
  // happens when the extractor doesn't synthesize a `ReturnStmt` because it
  // can tell that it wouldn't be reached.
  exists(Function f |
    p1.nodeAfter(n1, f.getEntryPoint()) and
    p2.nodeAt(n2, f)
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
  // SwitchStmt -> expr -> block -> { cases ; after block } ->
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
    or
    // If there is no default case, we can jump to after the block
    not exists(DefaultCase default | default.getSwitchStmt() = s) and
    p1.nodeAt(n1, s.getStmt()) and
    p2.nodeAfter(n2, s.getStmt())
    or
    p1.nodeAfter(n1, s.getStmt()) and
    p2.nodeAfter(n2, s)
  )
  or
  exists(Handler h |
    p1.nodeAt(n1, h) and
    p2.nodeBefore(n2, h.getBlock())
    or
    // If this is not a catch-all handler, add an edge to the next handler in
    // case it doesn't match.
    exists(h.getParameter()) and
    (
      exists(int i, TryStmt try |
        h = try.getChild(i) and
        p1.nodeAt(n1, h) and
        p2.nodeAt(n2, try.getChild(i+1))
      )
      or
      p1.nodeAt(n1, h) and
      p2.nodeAt(n2, h.(ExceptionSource).getExceptionTarget())
    )
  )
  or exists(CatchBlock cb |
    p1.nodeAfter(n1, cb) and
    p2.nodeAfter(n2, cb.getTryStmt())
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

private class ExceptionTarget extends ControlFlowNode {
  ExceptionTarget() { this instanceof Handler or this instanceof Function }
}

private class PropagatingHandler extends Handler {
  PropagatingHandler() {
    exists(this.getParameter()) and
    exists(int i, TryStmt try |
      this = try.getChild(i) and
      i = max(int j | exists(try.getChild(j)))
    )
  }
}

private class ExceptionSource extends ControlFlowNode {
  ExceptionSource() { this instanceof ThrowExpr or this instanceof PropagatingHandler }

  // TODO: Performance: if there are multiple sources far down in the AST, this
  // will compute their parents separately without sharing. If that's a
  // performance problem, we can go up the tree first with a unary predicate
  // `isThrowParent` and then down along those edges only.
  private predicate reachesParent(Stmt parent) {
    parent = this.(ThrowExpr).getEnclosingStmt()
    or
    parent = this.(PropagatingHandler).getTryStmt().getParentStmt()
    or
    exists(Stmt s |
      this.reachesParent(s) and
      not s instanceof TryStmt and
      parent = s.getParentStmt()
    )
  }

  ExceptionTarget getExceptionTarget() {
    exists(Stmt parent |
      this.reachesParent(parent)
    |
      result.(Function).getBlock() = parent
      or
      result = parent.(TryStmt).getChild(1)
    )
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
  // TODO: Is it slow to use the abstract class `Loop`? It gets compiled to a
  // join with `stmts`.
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
  memberPos.isAt() and
  // We check for SupportedNode here as it's slower to check in all the leaf
  // cases during construction of the half-graph.
  atNode instanceof SupportedNode
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

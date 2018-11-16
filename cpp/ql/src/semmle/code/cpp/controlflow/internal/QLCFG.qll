import cpp

/*
TODO: difficulties:
- Particular AST nodes
  - StmtExpr
    - Interaction with throw-catch
  - BlockExpr??? (clang extension)
  - Microsoft __try
  - Unstructured switch statements
    - Variable init at start of switch block
  - VlaDeclStmt
  - Pointer-to-member call and access
- Synthetic destructor calls. I've taken them out of the reference in the
  comparisons until there is a solution.
  - following_destructor extractor changes
    - Can we just construct the CFG and then inject these calls?
 */

private class Node = ControlFlowNodeBase;

private class Orphan extends Expr {
  Orphan() {
    not exists(this.getParent()) and
    not this instanceof DestructorCall
    or
    // For the GNU binary `? :` operator, an extra copy of the condition is
    // extracted and attached at position -1. We do not want this copy in the
    // CFG.
    exists(ConditionalExpr conditional |
      this = conditional.getChild(-1) and
      this != conditional.getChild(0) and
      not this.getParent() != conditional
    )
  }
}

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
    // Constructor init lists should be evaluated, but this will mean that a
    // `Function` entry point is not always a `Block`.
    not this.(Expr).getParent*() instanceof ConstructorInit and
    // TODO: this can be improved.
    not this.(Expr).getParent+() instanceof ConditionDeclExpr and
    not this.(Expr).getParent+() instanceof ArgumentsUnevaluatedNode and
    not this.(Expr).getParent*() instanceof Orphan and
    // Initializers of static locals in C
    not exists(LocalVariable staticLocal |
      staticLocal.isStatic() and
      not fileUsedInCPP(staticLocal.getFile()) and
      this.(Expr).getParent+() = staticLocal.getInitializer()
    )
  }
}

/**
 * A node that is part of the CFG but whose arguments are not. That means the
 * arguments should not be linked to the CFG and should not have internal
 * control flow in them.
 */
// TODO: perhaps generalize to a predicate that specifies _which_ argument is
// not evaluated.
private class ArgumentsUnevaluatedNode extends Node {
  ArgumentsUnevaluatedNode() {
    this instanceof BuiltInOperationOffsetOf
    // TODO: others?
    // TODO: sizeof belongs here, but the extractor pretends it doesn't.
  }
}

// TODO: test what the extractor does for a `.h` file included from both `.c`
// and `.cpp`, where the `.h` file contains a static local with initializer.
private predicate fileUsedInCPP(File f) {
  exists(File cppFile | cppFile.compiledAsCpp() |
    f = cppFile.getAnIncludedFile*()
  )
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
    or
    // It's highly unusual for a statement not to start with itself. This type
    // of statement is only found in `Block`s.
    this instanceof VlaDeclStmt
  }
}

private class PreOrderNode extends Node {
  PreOrderNode() {
    // TODO: this is to mimic the extractor. Why not extend to all initializers?
    this.(Initializer).getDeclaration() instanceof LocalVariable
    or
    this instanceof DeclStmt
    or
    this instanceof Block
    or
    this instanceof LabelStmt
    or
    this instanceof ExprStmt
    or
    this instanceof EmptyStmt
    or
    this instanceof AsmStmt
    or
    this instanceof VlaDimensionStmt
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
  not n instanceof ArgumentsUnevaluatedNode and
  not result instanceof TypeName and // TODO: is this the right place?
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
      result = c.getArgument(i)
      or
      i = c.getNumberOfArguments() and result = c.(ExprCall).getExpr()
      or
      i = c.getNumberOfArguments() + 1 and result = c.getQualifier()
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
  n = any(StmtExpr e |
    i = 0 and result = e.getStmt()
  )
  or
  n = any(Initializer init |
    not exists(ConditionDeclExpr cd | init = cd.getVariable().getInitializer()) and
    i = 0 and result = n.(Initializer).getExpr()
  )
  or
  result = n.(PreOrderNode).(Stmt).getChild(i) and
  not n instanceof Block // handled below
  // VLAs are special because of how their associated statements are added
  // in-line in the block containing their corresponding DeclStmt but should
  // not be evaluated in the order implied by their position in the block. We
  // do the following.
  // - Block skips all the VlaDeclStmt and VlaDimensionStmt children.
  // - VlaDeclStmt is inserted as a child of DeclStmt
  // - VlaDimensionStmt is inserted as a child of VlaDeclStmt
  or
  result = n.(Block).getChild(i) and
  not result instanceof VlaDeclStmt and
  not result instanceof VlaDimensionStmt
  or
  n = any(DeclStmt s |
    exists(Variable var | var = s.getDeclaration(i) |
      result = var.getInitializer() and
      (
        // Non-static locals always have control flow to their initializers
        not s.getDeclaration(i).isStatic()
        or
        // In C++, static locals do too
        fileUsedInCPP(n.(Element).getFile())
      )
      or
      // A VLA cannot have an initializer, so there is no conflict between this
      // case and the above.
      result.(VlaDeclStmt).getVariable() = var
    )
  )
  or
  result = n.(VlaDeclStmt).getVlaDimensionStmt(i)
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
    i = 1 and ni = op.getFirstChildNode() and spec.isBefore()
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
  or
  scope = any(SwitchStmt s |
    i = -1 and ni = s and spec.isAt()
    or
    i = 0 and ni = s.getExpr() and spec.isAround()
    or
    // If the switch body is not a block then this step is skipped, and the
    // expression jumps directly to the cases.
    i = 1 and ni = s.getStmt().(Block) and spec.isAt()
    or
    i = 2 and ni = s.getASwitchCase() and spec.isBefore()
    or
    // If there is no default case, we can jump to after the block. Note: `i`
    // is same value as above.
    not s.getASwitchCase() instanceof DefaultCase and
    i = 2 and ni = s.getStmt() and spec.isAfter()
    or
    i = 3 and ni = s and spec.isBarrier()
    or
    i = 4 and ni = s.getStmt() and spec.isAfter()
    or
    i = 5 and ni = s and spec.isAfter()
  )
  or
  scope = any(ComputedGotoStmt s |
    i = -1 and ni = s and spec.isAt()
    or
    i = 0 and ni = s.getExpr() and spec.isBefore()
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
  // ALmost all statements start with themselves.
  // TODO: does that mean we should never make edges to _before_ a statement
  // but always _at_ the statement? Or is that premature optimization?
  // To make this change, we'd need an `isAroundStmt` spec.
  n1.(Stmt) = n2 and
  not n1 instanceof VlaDeclStmt and
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
  exists(DeclStmt s |
    // For static locals in C++, the declarations will be skipped after the
    // first init. We only check whether the first declared variable is static
    // since there is no syntax for declaring one variable static without all
    // of them becoming static.
    // There is no CFG for initialization of static locals in C, so this edge
    // is redundant there.
    s.getDeclaration(0).isStatic() and
    p1.nodeAt(n1, s) and
    p2.nodeAfter(n2, s)
  )
  or
  // SwitchCase ->
  // (note: doesn't evaluate its argument)
  exists(SwitchCase s |
    p1.nodeAt(n1, s) and
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

private import ShortCircuit
private module ShortCircuit {
  abstract class ShortCircuitOperator extends Expr {
    final Expr getFirstChildNode() { result = this.getChild(0) }
  }

  class LogicalAndLikeExpr extends ShortCircuitOperator, LogicalAndExpr { }

  class LogicalOrLikeExpr extends ShortCircuitOperator {
    Expr left;
    Expr right;

    LogicalOrLikeExpr() {
      this = any(LogicalOrExpr e |
        left = e.getLeftOperand() and
        right = e.getRightOperand()
      )
      or
      // GNU extension: the `? :` operator
      this = any(ConditionalExpr e |
        left = e.getCondition() and
        right = e.getElse() and
        left = e.getThen()
      )
    }

    Expr getLeftOperand() { result = left }

    Expr getRightOperand() { result = right }
  }

  class ConditionalLikeExpr extends ShortCircuitOperator {
    Expr condition;
    Expr thenExpr;
    Expr elseExpr;

    ConditionalLikeExpr() {
      this = any(ConditionalExpr e |
        condition = e.getCondition() and
        thenExpr = e.getThen() and
        elseExpr = e.getElse() and
        thenExpr != condition
      )
      or
      this = any(BuiltInChooseExpr e |
        condition = e.getChild(0) and
        thenExpr = e.getChild(1) and
        elseExpr = e.getChild(2)
      )
    }

    Expr getCondition() { result = condition }

    Expr getThen() { result = thenExpr }

    Expr getElse() { result = elseExpr }
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
  exists(ConditionalLikeExpr e |
    (test = e.getThen() or test = e.getElse()) and
    conditionJumps(e, truth, targetNode, targetPos)
  )
  or
  exists(ConditionalLikeExpr e | test = e.getCondition() |
    truth = true and
    targetPos.nodeBefore(targetNode, e.getThen())
    or
    truth = false and
    targetPos.nodeBefore(targetNode, e.getElse())
  )
  // TODO: handle `!` better in the future. Like this?
  //or
  //exists(NotExpr e |
  //  test = e.getOperand() and
  //  conditionJumps(e, truth.booleanNot(), targetNode, targetPos)
  //)
  or
  exists(LogicalAndLikeExpr e |
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
  exists(LogicalOrLikeExpr e |
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

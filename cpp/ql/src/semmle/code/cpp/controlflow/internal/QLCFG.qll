import cpp

/*
TODO: difficulties:
- Particular AST nodes
  - StmtExpr interaction with throw-catch
    - Use the new Node.getParent
  - Pointer-to-member call and access
- Take cases from Ian's orphanedExpr and orphanedInitializer.
- getSwitchStmtEndLabel. What's going on there, and do I need it? Doesn't work
  with macros and templates.
- Synthetic destructor calls. I've taken them out of the reference in the
  comparisons until there is a solution.
  - following_destructor extractor changes
    - Can we just construct the CFG and then inject these calls? It looks like
      they should be injected After the marked node.
    - For prototyping, I'd like to take this information from `successors`, but
      I don't see how to reconstruct it. I'd have to splice them in based on
      where `successors` tells me to add them, but that's cheating just as much
      as the current workaround in Compare.
    - index_destructor_call documentation mentions `\param following`, not
      `\param label`.
    - Why add both the var access and the call to following_destructor? I'd
      just add the call.
    - How does the size and contents of the `label` buffers match up?
      (`char label[sizeof(unsigned long) + strlen(suffix)];`)
 */

private class Node extends ControlFlowNodeBase {
  /**
   * Gets the nearest control-flow node that's a parent of this one, never
   * crossing function boundaries.
   */
  final Node getParentNode() {
    result = this.(Expr).getParent()
    or
    result = this.(Stmt).getParent()
    or
    // ConditionDeclExpr not supported yet.
    result.(DeclStmt).getADeclaration().(LocalVariable) = this.(Initializer).getDeclaration()
  }
}

private class Orphan extends Expr {
  Orphan() {
    not exists(this.getParent()) and
    not this instanceof DestructorCall and
    not this = getStrayVDCQualifier(_)
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

// TODO: this is a workaround for CPP-298
Expr getStrayVDCQualifier(VacuousDestructorCall c) {
  successors(unresolveElement(result), unresolveElement(c)) and
  exists(c.getEnclosingFunction()) and
  not exists(result.getEnclosingFunction())
}

/**
 * For compatibility with the extractor-generated CFG, the QL-generated CFG
 * will only be produced for nodes in this class.
 */
private class SupportedNode extends Node {
  SupportedNode() {
    // TODO: It appears the extractor doesn't produce CFG for free-standing
    // expressions. Why?
    (
      exists(this.(ControlFlowNode).getControlFlowScope())
      or
      this.getParentNode*() = getStrayVDCQualifier(_)
    ) and
    not this.getParentNode+() instanceof SwitchCase and
    // Constructor init lists should be evaluated, and we can change this in
    // the future, but it would mean that a `Function` entry point is not
    // always a `Block`.
    // TODO: Ian's prototype built CFG for ConstructorBaseInit. Was that
    // deliberate?
    not this.getParentNode*() instanceof ConstructorInit and
    // Destructor field destructions should also be hooked into the CFG
    // properly in the future.
    not this.getParentNode*() instanceof DestructorFieldDestruction and
    // TODO: this can be improved.
    not this.getParentNode+() instanceof ConditionDeclExpr and
    not this.getParentNode+() instanceof ArgumentsUnevaluatedNode and
    not this.getParentNode*() instanceof Orphan and
    not skipInitializer(this.getParentNode+())
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
    or
    this instanceof BuiltInOperationBuiltInShuffleVector
    or
    this instanceof AssumeExpr
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

// TODO: remove this class when we don't need extractor compatibility
private class PostOrderInitializer extends Initializer {
  PostOrderInitializer() {
    exists(RangeBasedForStmt for |
      this.getDeclaration() = for.getVariable()
      or
      this.getDeclaration() = for.getRangeVariable()
      or
      this.getDeclaration() = for.getBeginEndDeclaration().(DeclStmt).getADeclaration()
    )
  }
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
    // TODO: Turn this into a PreOrderNode when we're no longer comparing with
    // the extractor CFG.
    this instanceof VlaDeclStmt
    or
    this instanceof PostOrderInitializer
  }
}

private class PreOrderNode extends Node {
  PreOrderNode() {
    // TODO: this is to mimic the extractor. Why not extend to all initializers?
    this.(Initializer).getDeclaration() instanceof LocalVariable and
    not this instanceof PostOrderInitializer
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
    or
    this instanceof MicrosoftTryFinallyStmt
  }
}

/** Holds if `c` is part of a `delete` or `delete[]` operation. */
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
  not n instanceof NewArrayExpr and
  not n instanceof NewExpr and
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
  n = any(NewArrayExpr new |
    // An extra argument to a built-in allocator, such as alignment or pointer
    // address, is found at child position 3. Extra arguments to custom
    // allocators are instead placed as subexpressions of `getAllocatorCall`.
    i = 0 and result = new.getChild(3)
    or
    i = 1 and result = new.getExtent()
    or
    i = 2 and result = new.getAllocatorCall()
    or
    i = 3 and result = new.getInitializer()
  )
  or
  n = any(NewExpr new |
    // An extra argument to a built-in allocator, such as alignment or pointer
    // address, is found at child position 3. Extra arguments to custom
    // allocators are instead placed as subexpressions of `getAllocatorCall`.
    i = 0 and result = new.getChild(3)
    or
    i = 1 and result = new.getAllocatorCall()
    or
    i = 2 and result = new.getInitializer()
  )
  or
  i = 0 and result = getStrayVDCQualifier(n)
  or
  n = any(StmtExpr e |
    i = 0 and result = e.getStmt()
  )
  or
  n = any(Initializer init |
    not skipInitializer(init) and
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
    exists(LocalVariable var | var = s.getDeclaration(i) |
      result = var.getInitializer() and
      not skipInitializer(result)
      or
      // A VLA cannot have an initializer, so there is no conflict between this
      // case and the above.
      result.(VlaDeclStmt).getVariable() = var
    )
  )
  or
  result = n.(VlaDeclStmt).getVlaDimensionStmt(i)
}

private predicate skipInitializer(Initializer init) {
  exists(LocalVariable local |
    init = local.getInitializer() and
    local.isStatic() and
    (
      // In C, there is never control flow through static initializers
      not fileUsedInCPP(local.getFile())
      or
      not runtimeExprInStaticInitializer(init.getExpr())
    )
  )
}

private predicate runtimeExprInStaticInitializer(Expr e) {
  inStaticInitializer(e) and
  if e instanceof AggregateLiteral
  then runtimeExprInStaticInitializer(e.(AggregateLiteral).getAChild())
  else
    if e instanceof PointerArithmeticOperation
    then runtimeExprInStaticInitializer(e.(PointerArithmeticOperation).getAnOperand())
    else (
      // Not constant
      not e.isConstant() and
      // Not a function address
      not e instanceof FunctionAccess and
      // Not a function address-of (same as above)
      not e.(AddressOfExpr).getOperand() instanceof FunctionAccess and
      // Not the address of a global variable
      not exists(Variable v |
        v.isStatic()
        or
        v instanceof GlobalOrNamespaceVariable
      |
        e.(AddressOfExpr).getOperand() = v.getAnAccess()
      )
    )
}

private predicate inStaticInitializer(Expr e) {
  exists(LocalVariable local |
    local.isStatic() and
    e.(Node).getParentNode*() = local.getInitializer()
  )
}

private Node controlOrderChild(Node n, int i) {
  result = rank[i + 1](Node child, int childIdx |
    child = controlOrderChildSparse(n, childIdx)
  |
    child
    order by childIdx
  )
}

private Node lastControlOrderChild(Node n) {
  result = controlOrderChild(n, max(int i | exists(controlOrderChild(n, i))))
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
  scope = any(RangeBasedForStmt for |
    i = -1 and ni = for and spec.isAt()
    or
    exists(DeclStmt s |
      s.getADeclaration() = for.getRangeVariable() and
      i = 0 and ni = s and spec.isAround()
    )
    or
    i = 1 and ni = for.getBeginEndDeclaration() and spec.isAround()
    or
    i = 2 and ni = for.getCondition() and spec.isBefore()
    or
    i = 3 and ni = for and spec.isBarrier()
    or
    exists(DeclStmt declStmt |
      declStmt.getADeclaration() = for.getVariable() and
      i = 4 and ni = declStmt and spec.isAfter()
    )
    or
    i = 5 and ni = for.getStmt() and spec.isAround()
    or
    i = 6 and ni = for.getUpdate() and spec.isAround()
    or
    i = 7 and ni = for.getCondition() and spec.isBefore()
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
  scope = any(MicrosoftTryExceptStmt s |
    i = -1 and ni = s and spec.isAt()
    or
    i = 0 and ni = s.getStmt() and spec.isAround()
    or
    i = 1 and ni = s and spec.isAfter()
    or
    i = 2 and ni = s and spec.isBarrier()
    or
    i = 3 and ni = s.getExcept() and spec.isAfter()
    or
    i = 4 and ni = s and spec.isAfter()
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
  // child1 -> ... -> childn
  exists(Node n, int childIdx |
    p1.nodeAfter(n1, controlOrderChild(n, childIdx)) and
    p2.nodeBefore(n2, controlOrderChild(n, childIdx+1))
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
  // ALmost all statements start with themselves.
  // TODO: does that mean we should never make edges to _before_ a statement
  // but always _at_ the statement? Or is that premature optimization?
  // To make this change, we'd need an `isAroundStmt` spec. We also need to do
  // something about exception targets, Microsoft `__try`-exceptions can either
  // propagate to an expression (`__except(e)`) or a statement (`__finally`).
  exists(Stmt s |
    not s instanceof VlaDeclStmt and
    p1.nodeBefore(n1, s) and
    p2.nodeAt(n2, s)
  )
  or
  exists(Function f |
    p1.nodeBefore(n1, f) and
    p2.nodeAt(n2, f)
  )
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
    exists(int i, TryStmt try |
      h = try.getChild(i) and
      p1.nodeAt(n1, h) and
      p2.nodeAt(n2, try.getChild(i+1))
    )
    or
    p1.nodeAt(n1, h) and
    p2.nodeAt(n2, h.(ExceptionSource).getExceptionTarget())
  )
  or exists(CatchBlock cb |
    p1.nodeAfter(n1, cb) and
    p2.nodeAfter(n2, cb.getTryStmt())
  )
  or
  // Additional edge for `MicrosoftTryFinallyStmt` for the case where an
  // exception is propagated. It gets its other edges from being a
  // `PreOrderNode` and a `Stmt`.
  exists(MicrosoftTryFinallyStmt s, Stmt finally |
    finally = s.getFinally() and
    p1.nodeAfter(n1, finally) and
    p2.nodeBefore(n2, finally.(ExceptionSource).getExceptionTarget())
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

/**
 * A `Handler` that might fail to match its exception and instead propagate it
 * further up the AST. This can happen in the last `Handler` of a `TryStmt` if
 * it's not a catch-all handler.
 */
private class PropagatingHandler extends Handler {
  PropagatingHandler() {
    exists(this.getParameter()) and
    exists(int i, TryStmt try |
      this = try.getChild(i) and
      i = max(int j | exists(try.getChild(j)))
    )
  }
}

/** A control-flow node that might pass an exception up in the AST. */
private class ExceptionSource extends Node {
  ExceptionSource() {
    this instanceof ThrowExpr
    or
    this instanceof PropagatingHandler
    or
    // By reusing the same set of predicates for Microsoft exceptions and C++
    // exceptions, we're pretending that their handlers can catch each other.
    // This may or may not be true depending on compiler options.
    exists(MicrosoftTryExceptStmt try | this = try.getCondition())
    or
    exists(MicrosoftTryFinallyStmt try | this = try.getFinally())
  }

  // TODO: Performance: if there are multiple sources far down in the AST, this
  // will compute their parents separately without sharing. If that's a
  // performance problem, we can go up the tree first with a unary predicate
  // `isThrowParent` and then down along those edges only.
  private predicate reachesStmt(Stmt parent) {
    parent = this.(Expr).getEnclosingStmt()
    or
    parent = this
    or
    exists(Stmt s |
      this.reachesStmt(s) and
      not s = any(TryStmt try).getStmt() and
      not s = any(MicrosoftTryStmt try).getStmt() and
      parent = s.getParentStmt()
    )
  }

  Node getExceptionTarget() {
    exists(Stmt parent |
      this.reachesStmt(parent)
    |
      result.(Function).getEntryPoint() = parent
      or
      exists(TryStmt try |
        parent = try.getStmt() and
        result = try.getChild(1)
      )
      or
      exists(MicrosoftTryExceptStmt try |
        parent = try.getStmt() and
        result = try.getCondition()
      )
      or
      exists(MicrosoftTryFinallyStmt try |
        parent = try.getStmt() and
        result = try.getFinally()
      )
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
  exists(Loop l |
    (
      l instanceof WhileStmt
      or
      l instanceof DoStmt
      or
      l instanceof ForStmt
    ) and
    test = l.getCondition()
  |
    truth = true and
    targetPos.nodeBefore(targetNode, l.getStmt())
    or
    truth = false and
    targetPos.nodeAfter(targetNode, l)
  )
  or
  exists(RangeBasedForStmt for | test = for.getCondition() |
    truth = true and
    exists(DeclStmt declStmt |
      declStmt.getADeclaration() = for.getVariable() and
      targetPos.nodeBefore(targetNode, declStmt)
    )
    or
    truth = false and
    targetPos.nodeAfter(targetNode, for)
  )
  or
  exists(MicrosoftTryExceptStmt try | test = try.getCondition() |
    truth = true and
    targetPos.nodeBefore(targetNode, try.getExcept())
    or
    // TODO: Actually, this test is ternary.
    truth = false and
    targetPos.nodeBefore(targetNode, test.(ExceptionSource).getExceptionTarget())
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
  // TODO: we could check at lower levels than this without going all the way
  // to the leaves.
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

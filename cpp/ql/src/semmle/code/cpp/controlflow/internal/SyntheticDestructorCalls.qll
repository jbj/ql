// TODO: `private` annotations
import cpp

// TODO: copied from QLCFG.qll. Needed?
private predicate isDeleteDestructorCall(DestructorCall c) {
  exists(DeleteExpr del | c = del.getDestructorCall())
  or
  exists(DeleteArrayExpr del | c = del.getDestructorCall())
}

// Things we know about these calls
// - isCompilerGenerated() always holds
// - They all have a predecessor of type VariableAccess
// - They all have successors
// - After subtracting all the jumpy dtor calls for a particular variable
//   (PrematureScopeExitNode), there's at most one call left, and that will be
//   the ordinary one.
//   - TODO: Not true for ConditionDeclExpr! One chain should be directly
//     connected to the false edge out of the parent, and the other should not.
class SyntheticDestructorCall extends FunctionCall {
  SyntheticDestructorCall() {
    (
      this instanceof DestructorCall
      or
      // Workaround for CPP-320
      exists(Function target |
        target = this.(FunctionCall).getTarget() and
        not exists(target.getName())
      )
    ) and
    not exists(this.getParent()) and
    not isDeleteDestructorCall(this) and
    not this.isUnevaluated() and
    this.isCompilerGenerated()
  }

  VariableAccess getAccess() { successors(result, this) }

  SyntheticDestructorCall getNext() { successors(this, result.getAccess()) }

  SyntheticDestructorCall getPrev() { this = result.getNext() }
}

// Things we know about these blocks
// - If they follow a JumpStmt, the VariableAccesses of their calls never
//   have multiple predecessors.
//   - But after ReturnStmt, that may happen.
/**
 * Describes a straight line of `SyntheticDestructorCall`s. Node that such
 * lines can share tails.
 */
private class SyntheticDestructorBlock extends ControlFlowNodeBase {
  SyntheticDestructorBlock() {
    this = any(SyntheticDestructorCall call |
      not exists(call.getPrev())
      or
      exists(ControlFlowNodeBase pred |
        not pred instanceof SyntheticDestructorCall and
        successors(pred, call.getAccess())
      )
    )
  }

  SyntheticDestructorCall getCall(int i) {
    i = 0 and result = this
    or
    result = this.getCall(i - 1).getNext()
  }

  ControlFlowNode getAPredecessor() {
    successors(result, this.(SyntheticDestructorCall).getAccess()) and
    not result instanceof SyntheticDestructorCall
  }

  ControlFlowNode getSuccessor() {
    successors(this.getCall(max(int i | exists(this.getCall(i)))), result)
  }
}

class PrematureScopeExitNode extends ControlFlowNodeBase {
  PrematureScopeExitNode() {
    this instanceof JumpStmt
    or
    this instanceof Handler
    or
    this instanceof ThrowExpr
    or
    this instanceof ReturnStmt
    or
    this instanceof MicrosoftTryExceptStmt
    or
    // TODO: Detecting exception edges out of a MicrosoftTryExceptStmt is not
    // implemented. It may not be easy to do. It'll be something like finding
    // the first synthetic destructor call that crosses out of the scope of the
    // statement and does not belong to some other `PrematureScopeExitNode`.
    // Note that the exception destructors after __try can follow right after
    // ordinary cleanup from the __finally block.
    this instanceof MicrosoftTryFinallyStmt
  }

  // TODO: is this always a straight line, or might the tail be shared? Does that matter?
  SyntheticDestructorBlock getSyntheticDestructorBlock() {
    result.getAPredecessor() = this
    or
    // TODO: StmtExpr not handled properly here.
    result.getAPredecessor().(Expr).getParent+() = this.(ReturnStmt)
    or
    // TODO: Only handles post-order conditions. Won't work with
    // short-circuiting operators.
    falsecond_base(
      this.(MicrosoftTryExceptStmt).getCondition(),
      result.(SyntheticDestructorCall).getAccess()
    )
  }
}

class DestructedVariable extends LocalScopeVariable {
  DestructedVariable() {
    exists(SyntheticDestructorCall call | call.getAccess().getTarget() = this)
  }

  /**
   * Gets the single destructor call that that corresponds to falling off the
   * end of the scope of this variable.
   */
  SyntheticDestructorCall getOrdinaryCall() {
    exists(SyntheticDestructorBlock block |
      block.getCall(_) = result and
      not exists(PrematureScopeExitNode exit | exit.getSyntheticDestructorBlock() = block) and
      result.getAccess().getTarget() = this
    |
      falsecond_base(getDeclaringLoop().getCondition(), block.getCall(0).getAccess())
      or
      not exists(this.getDeclaringLoop())
    )
  }

  predicate hasPositionInScope(int x, int y, Stmt scope) {
    exists(DeclStmt declStmt |
      this = declStmt.getDeclaration(y) and
      declStmt = scope.getChild(x)
    )
    or
    exists(ConditionDeclExpr decl |
      this = decl.getVariable() and
      // These coordinates are chosen to place the destruction correctly
      // relative to the destruction of other variables declared in
      // `decl.getParent()`. Only a `for` loop can have other declarations in
      // it. These show up as a `DeclStmt` with `x = 0`, so by choosing `x = 1`
      // here we get the `ConditionDeclExpr` placed after all variables
      // declared in the init statement of the `for` loop.
      x = 1 and
      y = 0 and
      scope = decl.getParent()
    )
  }

  SyntheticDestructorCall getInnerScopeCall() {
    exists(SyntheticDestructorBlock block |
      block.getCall(_) = result and
      not exists(PrematureScopeExitNode exit | exit.getSyntheticDestructorBlock() = block) and
      result.getAccess().getTarget() = this
    |
      exists(Loop loop | loop = this.getDeclaringLoop() |
        not falsecond_base(loop.getCondition(), block.getCall(0).getAccess())
      )
    )
  }

  predicate hasPositionInInnerScope(int x, int y, ControlFlowNodeBase scope) {
    exists(ConditionDeclExpr decl |
      this = decl.getVariable() and
      // These coordinates are chosen to place the destruction correctly
      // relative to the destruction of other variables in `scope`. Only in the
      // `while` case can there be other variables in `scope`, and in that case
      // `scope` will be a `Block`, whose smallest `x` coordinate can be 0.
      x = -1 and
      y = 0 and
      (
        scope = decl.getParent().(ForStmt).getUpdate()
        or
        scope = decl.getParent().(WhileStmt).getStmt()
      )
    )
  }

  private Loop getDeclaringLoop() {
    exists(ConditionDeclExpr decl | this = decl.getVariable() and result = decl.getParent())
  }
}

SyntheticDestructorCall getDestructorCallAfterNode(ControlFlowNodeBase node, int index) {
  result = rank[index + 1](SyntheticDestructorCall call, DestructedVariable var, int x, int y |
    call = var.getOrdinaryCall() and
    var.hasPositionInScope(x, y, node)
    or
    call = var.getInnerScopeCall() and
    var.hasPositionInInnerScope(x, y, node)
  |
    call
    order by x desc, y desc
  )
  or
  exists(SyntheticDestructorBlock block |
    node.(PrematureScopeExitNode).getSyntheticDestructorBlock() = block and
    result = block.getCall(index)
  )
}

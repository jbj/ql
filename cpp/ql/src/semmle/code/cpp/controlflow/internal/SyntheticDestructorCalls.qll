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
class SyntheticDestructorCall extends DestructorCall {
  SyntheticDestructorCall() {
    not exists(this.getParent()) and
    not isDeleteDestructorCall(this) and
    not this.isUnevaluated() /*and
    this.isCompilerGenerated()*/
  }

  VariableAccess getAccess() { successors(result, this) }

  SyntheticDestructorCall getNext() { successors(this, result.getAccess()) }

  SyntheticDestructorCall getPrev() { this = result.getNext() }
}

// Things we know about these blocks
// - If they follow a JumpStmt, the VariableAccesses of their calls never
//   have multiple predecessors.
//   - TODO: what about ReturnStmt?
private class SyntheticDestructorBlock extends ControlFlowNodeBase {
  SyntheticDestructorBlock() {
    this = any(SyntheticDestructorCall call | not exists(call.getPrev()))
  }

  SyntheticDestructorCall getCall(int i) {
    i = 0 and result = this
    or
    result = this.getCall(i - 1).getNext()
  }

  ControlFlowNode getAPredecessor() {
    successors(result, this.(SyntheticDestructorCall).getAccess())
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
    this instanceof ReturnStmt/* and
    not this.(ReturnStmt).isCompilerGenerated()*/ // TODO: correct?
  }

  // TODO: is this always a straight line, or might the tail be shared? Does that matter?
  SyntheticDestructorBlock getSyntheticDestructorBlock() {
    result.getAPredecessor() = this
    or
    // StmtExpr not handled properly here.
    result.getAPredecessor().(Expr).getParent+() = this.(ReturnStmt)
  }
}

class DestructedVariable extends LocalScopeVariable {
  DestructedVariable() {
    exists(SyntheticDestructorCall call | call.getAccess().getTarget() = this)
  }

  /**
   * Gets the single destructor call that doesn't come from a
   * `PrematureScopeExitNode`.
   */
  SyntheticDestructorCall getOrdinaryCall() {
    exists(SyntheticDestructorBlock block |
      block.getCall(_) = result and
      not exists(PrematureScopeExitNode exit | exit.getSyntheticDestructorBlock() = block) and
      result.getAccess().getTarget() = this
    )
  }

  predicate hasPositionInParent(int x, int y, Stmt parent) {
    exists(DeclStmt declStmt |
      this = declStmt.getDeclaration(y) and
      declStmt = parent.getChild(x)
    )
  }
}

SyntheticDestructorCall getDestructorCallAfterNode(ControlFlowNodeBase node, int index) {
  result = rank[index + 1](SyntheticDestructorCall call, DestructedVariable var, int x, int y |
    call = var.getOrdinaryCall() and
    var.hasPositionInParent(x, y, node)
  |
    call
    order by x desc, y desc
  )
  or
  // Return statement with expression: destructor calls come after that expression
  exists(SyntheticDestructorBlock block, ReturnStmt ret |
    node = ret.getExpr() and
    ret.(PrematureScopeExitNode).getSyntheticDestructorBlock() = block and
    result = block.getCall(index)
  )
}

SyntheticDestructorCall getDestructorCallAtNode(ControlFlowNodeBase node, int index) {
  exists(SyntheticDestructorBlock block |
    node.(PrematureScopeExitNode).getSyntheticDestructorBlock() = block and
    result = block.getCall(index) and
    not exists(node.(ReturnStmt).getExpr()) // handled in getDestructorCallAfterNode
  )
}

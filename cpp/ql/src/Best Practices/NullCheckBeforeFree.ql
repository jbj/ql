/**
 * @name Redundant null check before 'free'
 * @description TODO Insert description here...
 * @kind problem
 * @problem.severity recommendation
 * @precision very-high
 * @id cpp/null-check-before-free
 */

import cpp

// TODO: verify paths like `obj->field` or use GVN

// TODO: simplify this if we're not supporting `return`
predicate nullBranch(
    Expr cond, Variable var,
    ControlFlowNode validSucc, ControlFlowNode nullSucc
) {
  validCheckExpr(cond, var) and
  cond.getATrueSuccessor() = validSucc and
  cond.getAFalseSuccessor() = nullSucc
  or
  nullCheckExpr(cond, var) and
  cond.getATrueSuccessor() = nullSucc and
  cond.getAFalseSuccessor() = validSucc
}

predicate freeStmt(ExprStmt stmt, Variable var) {
  stmt.getExpr() = any(FunctionCall call |
    call.getTarget().getName() = "free" and
    call.getArgument(0) = var.getAnAccess()
  )
  or
  stmt.getExpr().(DeleteExpr).getExpr() = var.getAnAccess()
  or
  stmt.getExpr().(DeleteArrayExpr).getExpr() = var.getAnAccess()
  or
  stmt.getExpr() = any(AssignExpr assign |
    assign.getLValue() = var.getAnAccess() and
    assign.getRValue().getValue() = "0"
  )
}

predicate onValidPath(Expr cond, Variable var, ControlFlowNode node) {
  (
    nullBranch(cond, var, node, _)
    or
    onValidPath(cond, var, node.getAPredecessor())
  ) and
  (
    node instanceof Block
    or
    freeStmt(node, var)
    or
    freeStmt(node.(Expr).getEnclosingStmt(), var)
  )
}

from Expr cond, Variable var,
     ControlFlowNode validSucc, ControlFlowNode nullSucc
where nullBranch(cond, var, validSucc, nullSucc)
  and onValidPath(cond, var, nullSucc.getAPredecessor())
// TODO: make sure there's something on the path other than a Block
// TODO: might not be (only) free. Produce a nice message with concat.
select cond, "Redundant null check before free"

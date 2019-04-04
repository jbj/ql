/**
 * @name Call to alloca in a loop
 * @description Using alloca in a loop can lead to a stack overflow
 * @kind problem
 * @problem.severity warning
 * @precision high
 * @id cpp/alloca-in-loop
 * @tags reliability
 *       correctness
 *       security
 *       external/cwe/cwe-770
 */

import cpp
import semmle.code.cpp.rangeanalysis.RangeAnalysisUtils

Loop getAnEnclosingLoopOfExpr(Expr e) {
  result = getAnEnclosingLoopOfStmt(e.getEnclosingStmt())
}

Loop getAnEnclosingLoopOfStmt(Stmt s) {
  result = s.getParent*() and
  not s = result.(ForStmt).getInitialization()
  or
  result = getAnEnclosingLoopOfExpr(s.getParent*())
}

class AllocaCall extends FunctionCall {
  AllocaCall() {
    this.getTarget().getName() = "__builtin_alloca"
    or
    (this.getTarget().getName() = "_alloca" or this.getTarget().getName() = "_malloca") and
    this.getTarget().getADeclarationEntry().getFile().getBaseName() = "malloc.h"
  }
}

class LoopWithAlloca extends Stmt {
  LoopWithAlloca() { this = getAnEnclosingLoopOfExpr(any(AllocaCall ac)) }

  AllocaCall getAnAllocaCall() { this = getAnEnclosingLoopOfExpr(result) }

  /**
   */
  private predicate conditionRequires(Expr condition, boolean truth) {
    condition = this.(Loop).getCondition() and
    truth = true
    or
    // `e == 0`
    exists(EQExpr eq |
      conditionRequires(eq, truth.booleanNot()) and
      eq.getAnOperand().getValue().toInt() = 0 and
      condition = eq.getAnOperand() and
      not exists(condition.getValue())
    )
    or
    // `e != 0`
    exists(NEExpr eq |
      conditionRequires(eq, truth) and
      eq.getAnOperand().getValue().toInt() = 0 and
      condition = eq.getAnOperand() and
      not exists(condition.getValue())
    )
    or
    // `(bool)e == true`
    exists(EQExpr eq |
      conditionRequires(eq, truth) and
      eq.getAnOperand().getValue().toInt() = 1 and
      condition = eq.getAnOperand() and
      condition.getType().getUnspecifiedType() instanceof BoolType and
      not exists(condition.getValue())
    )
    or
    // `(bool)e != true`
    exists(NEExpr eq |
      conditionRequires(eq, truth.booleanNot()) and
      eq.getAnOperand().getValue().toInt() = 1 and
      condition = eq.getAnOperand() and
      condition.getType().getUnspecifiedType() instanceof BoolType and
      not exists(condition.getValue())
    )
    or
    exists(NotExpr notExpr |
      conditionRequires(notExpr, truth.booleanNot()) and
      condition = notExpr.getOperand()
    )
    or
    // If the condition of `this` requires `andExpr` to be true, then it
    // requires both of its operand to be true as well.
    exists(LogicalAndExpr andExpr |
      truth = true and
      conditionRequires(andExpr, truth) and
      condition = andExpr.getAnOperand()
    )
    or
    // Dually, if the condition of `this` requires `orExpr` to be false, then
    // it requires both of its operand to be false as well.
    exists(LogicalOrExpr orExpr |
      truth = false and
      conditionRequires(orExpr, truth) and
      condition = orExpr.getAnOperand()
    )
  }

  private predicate conditionRequiresInequality(Expr e, int value, RelationDirection dir) {
    exists(RelationalOperation rel, Expr constant, boolean branch |
      this.conditionRequires(rel, branch) and
      // TODO: semantic merge conflict with
      // `jbj:SimpleRangeAnalysis-use-after-cast` branch.
      relOpWithSwapAndNegate(rel, e, constant, dir, _, branch) and
      value = constant.getValue().toInt() and
      not exists(e.getValue())
    )
    or
    // Because we're not worried about off-by-one, it's not important whether
    // the `CrementOperation` is a {pre,post}-{inc,dec}rement.
    exists(CrementOperation inc |
      this.conditionRequiresInequality(inc, value, dir) and
      e = inc.getOperand()
    )
  }

  private Variable getAControllingVariable() {
    conditionRequires(result.getAnAccess(), _)
    or
    conditionRequiresInequality(result.getAnAccess(), _, _)
  }

  private VariableAccess getAControllingVariableUpdate(Variable var) {
    var = result.getTarget() and
    var = this.getAControllingVariable() and
    this = getAnEnclosingLoopOfExpr(result) and
    result.isUsedAsLValue()
  }

  private predicate conditionReachesWithoutUpdate(Variable var, ControlFlowNode node) {
    node = this.(Loop).getCondition().getATrueSuccessor() and
    var = this.getAControllingVariable()
    or
    this.conditionReachesWithoutUpdate(var, node.getAPredecessor()) and
    not node = this.getAControllingVariableUpdate(var)
  }

  private predicate hasMandatoryUpdate(Variable var) {
    var = this.getAControllingVariable() and
    not this.conditionReachesWithoutUpdate(var, this.(Loop).getCondition())
  }

  // TODO
  //private predicate precedesLoopBeforeDefOf(Variable var, ControlFlowNode node) {
  //  this = getAnEnclosingLoopOfExpr(node.getASuccessor()) and
  //  not this = getAnEnclosingLoopOfExpr(node) and
  //  var = this.getAControllingVariable()
  //}

  predicate isTightlyBounded() {
    exists(Variable var | this.hasMandatoryUpdate(var) |
      this.conditionRequires(var.getAnAccess(), false) and
      forall(VariableAccess update | update = this.getAControllingVariableUpdate(var) |
        exists(AssignExpr assign |
          assign.getLValue() = update and
          assign.getRValue().getValue().toInt() != 0
        )
      )
      or
      this.conditionRequires(var.getAnAccess(), true) and
      forall(VariableAccess update | update = this.getAControllingVariableUpdate(var) |
        exists(AssignExpr assign |
          assign.getLValue() = update and
          assign.getRValue().getValue().toInt() = 0
        )
      )
      or
      exists(int bound |
        this.conditionRequiresInequality(var.getAnAccess(), bound, Lesser()) and
        bound <= 16 and // TODO: relate bound to initial value
        forall(VariableAccess update | update = this.getAControllingVariableUpdate(var) |
          // var++;
          // ++var;
          exists(IncrementOperation inc | inc.getOperand() = update)
          or
          // var += positive_number;
          exists(AssignAddExpr aa |
            aa.getLValue() = update and
            aa.getRValue().getValue().toInt() > 0
          )
          or
          // var = var + positive_number;
          // var = positive_number + var;
          exists(AssignExpr assign, AddExpr add |
            assign.getLValue() = update and
            assign.getRValue() = add and
            add.getAnOperand() = var.getAnAccess() and
            add.getAnOperand().getValue().toInt() > 0
          )
        )
      )
    )
  }
}

from LoopWithAlloca l
where
  not l.(DoStmt).getCondition().getValue() = "0" and
  not l.isTightlyBounded()
select l.getAnAllocaCall(), "Stack allocation is inside a $@ and could lead to stack overflow.", l,
  l.toString()

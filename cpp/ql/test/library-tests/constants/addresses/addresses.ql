import cpp
import semmle.code.cpp.internal.AddressConstantExpression

from Expr e, string msg, LocalVariable var, Function f
where
  e = var.getInitializer().getExpr().getFullyConverted() and
  var.getFunction() = f and
  (
    addressConstantExpression(e) and
    f.getName() = "nonConstantAddresses" and
    msg = "misclassified as constant"
    or
    not addressConstantExpression(e) and
    f.getName() = "constantAddresses" and
    msg = "misclassified as NOT constant"
  )
select e, var.getName(), msg

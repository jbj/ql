import semmle.code.cpp.security.TaintTrackingImpl

from Expr source, Element tainted
where tainted(source, tainted)
select source, tainted
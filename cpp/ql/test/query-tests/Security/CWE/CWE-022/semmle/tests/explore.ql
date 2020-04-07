import semmle.code.cpp.ir.dataflow.DefaultTaintTracking as Default
import semmle.code.cpp.ir.IR
import semmle.code.cpp.ir.dataflow.DataFlow

query predicate tainted = Default::tainted/2;

from Default::DefaultTaintTrackingCfg cfg, Instruction i1, Instruction i2
where cfg.hasFlow(DataFlow::instructionNode(i1), DataFlow::instructionNode(i2))
select i1, i2
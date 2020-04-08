/**
 * @kind path-problem
 */

import TaintTestCommon
import DataFlow::PathGraph

from DataFlow::PathNode sink, DataFlow::PathNode source, TestAllocationConfig cfg
where cfg.hasFlowPath(source, sink)
select sink, source, sink, "I'm a path"
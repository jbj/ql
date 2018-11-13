// query-type: graph
import Compare

from
  Element scopeElement,
  string scopeString, boolean isEdge, ControlFlowNode x, ControlFlowNode y, string label
where
  BothCFG::qltestGraph(scopeElement, scopeString, isEdge, x, y, label) and
  differentFunction(scopeElement)
select
  scopeString, isEdge, x, y, label

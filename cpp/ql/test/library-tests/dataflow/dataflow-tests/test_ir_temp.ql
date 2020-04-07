import IRDataflowTestCommon

class ExploreTestAllocationConfig extends TestAllocationConfig {
  override int explorationLimit() {
    result = 100
  }
}

query predicate sources(DataFlow::Node node) {
    exists(TestAllocationConfig cfg |
      cfg.isSource(node)
    )
}

from DataFlow::PartialPathNode node, DataFlow::PartialPathNode source, int dist, TestAllocationConfig cfg
where cfg.hasPartialFlow(source, node, dist)
select source.getNode().getEnclosingCallable().getQualifiedName(), source, node, dist

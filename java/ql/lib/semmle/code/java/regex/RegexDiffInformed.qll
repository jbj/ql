private import java
private import semmle.code.java.dataflow.DataFlow
private import codeql.util.Unit

class RegexDiffInformedConfig instanceof Unit {
  abstract predicate observeDiffInformedIncrementalMode();

  abstract Location getASelectedSinkLocation(DataFlow::Node sink);

  string toString() { result = "RegexDiffInformedConfig" }
}

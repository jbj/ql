/** Provides classes to reason about System Information Leak vulnerabilities. */

import java
import semmle.code.java.dataflow.DataFlow
private import semmle.code.java.dataflow.ExternalFlow
import semmle.code.java.security.XSS

/**
 * A sink that represent a method that outputs data to an HTTP response. Extend
 * this class to add more sinks that should be considered information leak
 * points by every query.
 */
abstract class AbstractInformationLeakSink extends DataFlow::Node { }

/**
 * A sink that represent a method that outputs data to an HTTP response. To add
 * more sinks, extend `AbstractInformationLeakSink` rather than this class.
 */
final class InformationLeakSink extends DataFlow::Node instanceof InformationLeakDiffInformed<xssNotDiffInformed/0>::InformationLeakSink
{ }

/** A default sink representing methods outputing data to an HTTP response. */
private class DefaultInformationLeakSink extends AbstractInformationLeakSink {
  DefaultInformationLeakSink() { sinkNode(this, "information-leak") }
}

/**
 * A module for finding XSS sinks faster in a diff-informed query. The
 * `querySource` parameter should be the `querySource` predicate for the
 * overall data-flow configuration of the query. In full generality,
 * `querySource` should hold for at least all the nodes that may be emitted in
 * an alert message together with a sink found by this module.
 */
module InformationLeakDiffInformed<xssNullaryPredicate/0 hasSourceInDiffRange> {
  final private class Node = DataFlow::Node;

  /**
   * A diff-informed replacement for the top-level `InformationLeakSink`,
   * omitting for efficiency some sinks that would never be reported by a
   * diff-informed query.
   */
  final class InformationLeakSink extends Node {
    InformationLeakSink() {
      this instanceof AbstractInformationLeakSink
      or
      this instanceof XssDiffInformed<hasSourceInDiffRange/0>::XssSink
    }
  }
}

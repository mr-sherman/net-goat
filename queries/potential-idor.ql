/**
 * @name Potential insecure direct object reference
 * @description The system's authorization functionality does not prevent one user from gaining access to another user's data or record by modifying the key value identifying the data.
 * @kind path-problem
 * @id cs/potential-idor
 * @precision high
 * @problem.severity error
 * @tags security
 *       external/cwe/cwe-639
 */

import csharp
import semmle.code.csharp.dataflow.TaintTracking
import semmle.code.csharp.security.dataflow.flowsinks.ExternalLocationSink
import semmle.code.csharp.security.dataflow.flowsinks.Remote
import semmle.code.csharp.security.dataflow.SqlInjection
import semmle.code.csharp.dataflow.DataFlow
import semmle.code.csharp.frameworks.ServiceStack
import semmle.code.csharp.frameworks.system.Net
import semmle.code.csharp.frameworks.System
import semmle.code.csharp.frameworks.Test
private import semmle.code.csharp.security.dataflow.flowsources.Remote

class SystemNetHttpClientClass extends Class {
  SystemNetHttpClientClass() { this.hasName("HttpClient") }
}

//an http client sink/source is any argument called 'requestUri' or 'content' of
//any instance of HttpClient calling a method with those arguments
//If the data flow goes to a URL or a request body, it's an http
//client sink.  If data comes from that request and is used in
//another request, it's also an http client source
class HttpSinkSource extends Expr {
  Call theCall;

  HttpSinkSource() {
    exists(Method m |
      m = any(SystemNetHttpClientClass f).getAMethod() and
      theCall = m.getACall() and
      (
        this = theCall.getArgumentForName("requestUri") or
        this = theCall.getArgumentForName("content")
      )
    )
  }

  Call getTheCall() { result = theCall }
}

predicate hasHttpCall(Expr e) {
  exists(HttpSinkSource h, Interface i, Class c, Method m, Method im |
    c = m.getDeclaringType() and
    c.getABaseInterface() = i and
    m = h.getTheCall().getEnclosingCallable() and
    im.getAnImplementor() = m and
    e = im.getACall().getAnArgument()
  ) and
  not exists(TestMethod t |
    (
      e.getEnclosingCallable() = t or
      e.getEnclosingCallable().(LambdaExpr).getEnclosingCallable() = t
    )
  )
}

class IDORConfig extends TaintTracking::Configuration {
  IDORConfig() { this = "IDORConfig" }

  //sources are anything that has ID or Code in the name
  //this may produce false positives with things like "postalcode"
  override predicate isSource(DataFlow::Node source) {
    source instanceof RemoteFlowSource and
    exists(Access a |
      a = source.asExpr() and
      (
        a.getTarget().getName().regexpMatch(".*[iI][dD]") or
        a.getTarget().getName().regexpMatch(".*[cC][oO][dD][eE]")
      ) and
      not exists(TestMethod tm | a.getEnclosingCallable() = tm)
    ) and
    not exists(TestMethod t |
      (
        source.getEnclosingCallable() = t or
        source.getEnclosingCallable().(LambdaExpr).getEnclosingCallable() = t
      )
    )
  }

  //sinks are calls to http client
  override predicate isSink(DataFlow::Node sink) {
    exists(MethodCall mc | hasHttpCall(mc.getAnArgument()) and mc.getAnArgument() = sink.asExpr())
  }

  //it's an additional taint step if this call to http client
  //gets assigned to something that is later used in an http client call
  override predicate isAdditionalTaintStep(DataFlow::Node n1, DataFlow::Node n2) {
    exists(Variable d, MethodCall mc |
      (
        d.getName().toLowerCase().regexpMatch(".*code")
        or
        d.getName().toLowerCase().regexpMatch(".*id")
      ) and
      d.getAnAssignedValue() = n2.asExpr() and
      mc.getAnArgument() = n1.asExpr()
    ) and
    not exists(TestMethod t |
      n2.getEnclosingCallable() = t or
      n2.getEnclosingCallable().(LambdaExpr).getEnclosingCallable() = t
    )
  }

  //sanitizers are if statements that throw unauthorized access
  //exceptions
  override predicate isSanitizer(DataFlow::Node sanitizer) {
    exists(IfStmt i, ThrowStmt t |
      sanitizer.asExpr() = t.getAChildExpr() and
      t.getParent() = i.getAChild() and
      t.getThrownExceptionType().hasName("UnauthorizedAccessException")
    )
  }
}

from IDORConfig idorcfg, DataFlow::PathNode idorSource, DataFlow::PathNode idorSink
where idorcfg.hasFlowPath(idorSource, idorSink)
select idorSource.getNode(), idorSource, idorSink, "Potential IDOR"

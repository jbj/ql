/**
 * Provides classes for working with the [fasthttp](github.com/valyala/fasthttp) package.
 */

import go
private import semmle.go.security.RequestForgeryCustomizations

/**
 * Provides classes for working with the [fasthttp](github.com/valyala/fasthttp) package.
 */
module Fasthttp {
  /**
   * A class when you are using Fasthttp related queries to fully supports additional steps
   */
  bindingset[this]
  abstract class AdditionalStep extends string {
    /**
     * Holds if `pred` to `succ` is an additional taint-propagating step for this query.
     */
    abstract predicate hasTaintStep(DataFlow::Node pred, DataFlow::Node succ);
  }

  /**
   * Provide models for sanitizer/Dangerous Functions of fasthttp
   */
  module Functions {
    /**
     * A function that don't sanitize user-provided file paths
     */
    class FileSystemAccess extends FileSystemAccess::Range, DataFlow::CallNode {
      FileSystemAccess() {
        exists(DataFlow::Function f |
          f.hasQualifiedName("github.com/valyala/fasthttp",
            [
              "ServeFile", "ServeFileUncompressed", "ServeFileBytes", "ServeFileBytesUncompressed",
              "SaveMultipartFile"
            ]) and
          this = f.getACall()
        )
      }

      override DataFlow::Node getAPathArgument() { result = this.getArgument(1) }
    }

    /**
     * A function that can be used as a sanitizer for XSS
     */
    class HtmlQuoteSanitizer extends SharedXss::Sanitizer {
      HtmlQuoteSanitizer() {
        exists(DataFlow::CallNode c |
          c.getTarget()
              .hasQualifiedName("github.com/valyala/fasthttp",
                ["AppendHTMLEscape", "AppendHTMLEscapeBytes", "AppendQuotedArg"])
        |
          this = c.getArgument(1)
        )
      }
    }

    /**
     * A function that sends HTTP requests
     * Get* send a HTTP GET request.
     * Post send a HTTP POST request.
     * these Functions first arguments is a URL.
     */
    class RequestForgerySink extends RequestForgery::Sink {
      RequestForgerySink() {
        exists(DataFlow::Function f |
          f.hasQualifiedName("github.com/valyala/fasthttp",
            ["Get", "GetDeadline", "GetTimeout", "Post"]) and
          this = f.getACall().getArgument(1)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "URL" }
    }

    /**
     * A function that sends HTTP requests.
     * First argument of following functions need Additional steps.
     * look at URI module, additional steps part for more information.
     */
    class RequestForgerySinkDo extends RequestForgery::Sink {
      RequestForgerySinkDo() {
        exists(DataFlow::Function f |
          f.hasQualifiedName("github.com/valyala/fasthttp",
            ["Do", "DoDeadline", "DoTimeout", "DoRedirects"]) and
          this = f.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "URL" }
    }

    /**
     * A function that create initial connection to a TCP address.
     * Following Functions only accept TCP address + Port in their first argument
     */
    class RequestForgerySinkDial extends RequestForgery::Sink {
      RequestForgerySinkDial() {
        exists(DataFlow::Function f |
          f.hasQualifiedName("github.com/valyala/fasthttp",
            ["DialDualStack", "Dial", "DialTimeout", "DialDualStackTimeout"]) and
          this = f.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "TCP Addr + Port" }
    }
  }

  /**
   * Provide modeling for fasthttp.URI Type
   */
  module URI {
    /**
     * The additioanl steps that can be used in fasthttp framework.
     * Fasthttp has its own uri creating/manipulation methods and these methods usually are used in code.
     * Pred can be an user controlled value like any potential part of URL and succ is the URI instance.
     * So if we called a method like `URIInstance.SetHost(pred)` then the URIInstance is succ.
     */
    class UriAdditionalStep extends AdditionalStep {
      UriAdditionalStep() { this = "URI additioanl steps" }

      override predicate hasTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
        exists(DataFlow::MethodCallNode m, DataFlow::Variable frn |
          (
            m.getTarget()
                .hasQualifiedName("github.com/valyala/fasthttp.URI",
                  ["SetHost", "SetHostBytes", "Update", "UpdateBytes"]) and
            pred = m.getArgument(0)
            or
            m.getTarget().hasQualifiedName("github.com/valyala/fasthttp.URI", "Parse") and
            pred = m.getArgument([0, 1])
          ) and
          frn.getARead() = m.getReceiver() and
          succ = frn.getARead()
        )
        or
        // CopyTo method copy receiver to first argument
        exists(DataFlow::MethodCallNode m |
          m.getTarget().hasQualifiedName("github.com/valyala/fasthttp.URI", "CopyTo") and
          pred = m.getReceiver() and
          succ = m.getArgument(1)
        )
      }
    }

    /**
     * The methods as Remote user controllable source which are part of the incoming URL
     */
    class UntrustedFlowSource extends UntrustedFlowSource::Range instanceof DataFlow::Node {
      UntrustedFlowSource() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.URI",
            ["Path", "PathOriginal", "LastPathSegment", "FullURI", "QueryString", "String"]) and
          this = m.getACall()
          or
          m.hasQualifiedName("github.com/valyala/fasthttp.URI", "WriteTo") and
          this = m.getACall().getArgument(0)
        )
      }
    }
  }

  /**
   * Provide modeling for fasthttp.Args Type
   */
  module Args {
    /**
     * The methods as Remote user controllable source which are part of the incoming URL Parameters.
     */
    class UntrustedFlowSource extends UntrustedFlowSource::Range instanceof DataFlow::Node {
      UntrustedFlowSource() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.Args",
            ["Peek", "PeekBytes", "PeekMulti", "PeekMultiBytes", "QueryString", "String"]) and
          this = m.getACall()
          or
          m.hasQualifiedName("github.com/valyala/fasthttp.Args", "WriteTo") and
          this = m.getACall().getArgument(0)
        )
      }
    }
  }

  /**
   * Provide modeling for fasthttp.TCPDialer Type
   */
  module TcpDialer {
    /**
     * A method that create initial connection to a TCP address.
     * Provide Methods which can be used as dangerous RequestForgery Sinks.
     * Following Methods only accept TCP address + Port in their first argument
     */
    class RequestForgerySinkDial extends RequestForgery::Sink {
      RequestForgerySinkDial() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.TCPDialer",
            ["Dial", "DialTimeout", "DialDualStack", "DialDualStackTimeout"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "TCP Addr + Port" }
    }
  }

  /**
   * Provide modeling for fasthttp.Client Type
   */
  module Client {
    /**
     * A method that sends HTTP requests.
     * Get* send a HTTP GET request.
     * Post send a HTTP POST request.
     * these Functions first arguments is a URL.
     */
    class RequestForgerySink extends RequestForgery::Sink {
      RequestForgerySink() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.Client",
            ["Get", "GetDeadline", "GetTimeout", "Post"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "URL" }
    }

    /**
     * A method that sends HTTP requests.
     * First argument of following methods need Additional steps.
     * Look at Request module, additional steps part for more information.
     */
    class RequestForgerySinkDo extends RequestForgery::Sink {
      RequestForgerySinkDo() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.Client",
            ["Do", "DoDeadline", "DoTimeout", "DoRedirects"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      // Kind can be vary because input is a fasthttp.URI type
      override string getKind() { result = "URL" }
    }
  }

  /**
   * Provide modeling for fasthttp.PipelineClient Type
   */
  module PipelineClient {
    /**
     * A method that sends HTTP requests.
     * First argument of following methods need Additional steps.
     * Look at Request module, additional steps part for more information.
     */
    class RequestForgerySinkDo extends RequestForgery::Sink {
      RequestForgerySinkDo() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.PipelineClient",
            ["Do", "DoDeadline", "DoTimeout"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      // Kind can be vary because input is a fasthttp.URI type
      override string getKind() { result = "URL" }
    }
  }

  /**
   * Provide modeling for fasthttp.HostClient Type
   */
  module HostClient {
    /**
     * A method that sends HTTP requests.
     * Get* send a HTTP GET request.
     * Post send a HTTP POST request.
     * these Functions first arguments is a URL.
     */
    class RequestForgerySink extends RequestForgery::Sink {
      RequestForgerySink() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.HostClient",
            ["Get", "GetDeadline", "GetTimeout", "Post"]) and
          this = m.getACall().getArgument(1)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      override string getKind() { result = "URL" }
    }

    /**
     * A method that sends HTTP requests.
     * first argument of following methods need Additional steps.
     * Look at Request module, additional steps part for more information.
     */
    class RequestForgerySinkDo extends RequestForgery::Sink {
      RequestForgerySinkDo() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.HostClient",
            ["Do", "DoDeadline", "DoTimeout", "DoRedirects"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      // Kind can be vary because input is a fasthttp.URI type
      override string getKind() { result = "URL" }
    }
  }

  /**
   * Provide modeling for fasthttp.LBClient Type
   */
  module LBClient {
    /**
     * A method that sends HTTP requests.
     * first argument of following methods need Additional steps.
     * Look at Request module, additional steps part for more information.
     */
    class RequestForgerySinkDo extends RequestForgery::Sink {
      RequestForgerySinkDo() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.LBClient",
            ["Do", "DoDeadline", "DoTimeout"]) and
          this = m.getACall().getArgument(0)
        )
      }

      override DataFlow::Node getARequest() { result = this }

      // Kind can be vary because input is a fasthttp.URI type
      override string getKind() { result = "URL" }
    }
  }

  /**
   * Provide modeling for fasthttp.Request Type
   */
  module Request {
    /**
     * The additioanl steps that can be used in fasthttp framework.
     * Pred can be an user controlled value like any potential part of URL and succ is the URI instance.
     * So if we called a method like `RequestInstance.SetHost(pred)` then the RequestInstance is succ.
     * for SetURI the argument type is fasthttp.URI which is already modeled, look at URI module.
     */
    class RequestAdditionalStep extends AdditionalStep {
      RequestAdditionalStep() { this = "Request additioanl steps" }

      override predicate hasTaintStep(DataFlow::Node pred, DataFlow::Node succ) {
        exists(DataFlow::MethodCallNode m, DataFlow::Variable frn |
          m.getTarget()
              .hasQualifiedName("github.com/valyala/fasthttp.Request",
                ["SetRequestURI", "SetRequestURIBytes", "SetURI", "SetHost", "SetHostBytes"]) and
          pred = m.getArgument(0) and
          frn.getARead() = m.getReceiver() and
          succ = frn.getARead()
        )
      }
    }

    /**
     * Provide modeling for fasthttp.Response Type
     */
    module Response {
      /**
       * A Method That send files from its input and it does not check input path against path traversal attacks, so it is a dangerous method
       */
      class FileSystemAccess extends FileSystemAccess::Range, DataFlow::CallNode {
        FileSystemAccess() {
          exists(DataFlow::Method mcn |
            mcn.hasQualifiedName("github.com/valyala/fasthttp.Response", "SendFile") and
            this = mcn.getACall()
          )
        }

        override DataFlow::Node getAPathArgument() { result = this.getArgument(0) }
      }

      /**
       * The methods that can write to HTTP Response Body.
       * These methods can be dangerous if they are user controllable.
       */
      class HttpResponseBodySink extends SharedXss::Sink {
        HttpResponseBodySink() {
          exists(DataFlow::Method m |
            m.hasQualifiedName("github.com/valyala/fasthttp", "Response",
              [
                "AppendBody", "AppendBodyString", "SetBody", "SetBodyString", "SetBodyRaw",
                "SetBodyStream"
              ]) and
            this = m.getACall().getArgument(0)
          )
        }
      }
    }

    /**
     * The methods as Remote user controllable source which can be many part of request
     */
    class UntrustedFlowSource extends UntrustedFlowSource::Range instanceof DataFlow::Node {
      UntrustedFlowSource() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.Request",
            [
              "Host", "RequestURI", "Body", "BodyGunzip", "BodyInflate", "BodyUnbrotli",
              "BodyStream", "BodyUncompressed"
            ]) and
          this = m.getACall()
          or
          m.hasQualifiedName("github.com/valyala/fasthttp.Request",
            [
              "BodyWriteTo", "WriteTo", "ReadBody", "ReadLimitBody", "ContinueReadBodyStream",
              "ContinueReadBody"
            ]) and
          this = m.getACall().getArgument(0)
        )
      }
    }
  }

  /**
   * Provide modeling for fasthttp.RequestCtx Type
   */
  module RequestCtx {
    /**
     * The Methods that don't sanitize user provided file paths
     */
    class FileSystemAccess extends FileSystemAccess::Range, DataFlow::CallNode {
      FileSystemAccess() {
        exists(DataFlow::Method mcn |
          mcn.hasQualifiedName("github.com/valyala/fasthttp.RequestCtx",
            ["SendFileBytes", "SendFile"]) and
          this = mcn.getACall()
        )
      }

      override DataFlow::Node getAPathArgument() {
        this.getTarget().getName() = ["SendFile", "SendFileBytes"] and
        result = this.getArgument(0)
      }
    }

    /**
     * The Methods that can be dangerous if they take user controlled URL as their first argument
     */
    class Redirect extends Http::Redirect::Range, DataFlow::CallNode {
      Redirect() {
        exists(DataFlow::Function f |
          f.hasQualifiedName("github.com/valyala/fasthttp.RequestCtx", ["Redirect", "RedirectBytes"]) and
          this = f.getACall()
        )
      }

      override DataFlow::Node getUrl() { result = this.getArgument(0) }

      override Http::ResponseWriter getResponseWriter() { none() }
    }

    /**
     * The methods as Remote user controllable source which are generally related to HTTP request
     */
    class UntrustedFlowSource extends UntrustedFlowSource::Range instanceof DataFlow::Node {
      UntrustedFlowSource() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.RequestCtx",
            ["Path", "Referer", "PostBody", "RequestBodyStream", "RequestURI", "UserAgent", "Host"]) and
          this = m.getACall()
        )
      }
    }

    /**
     * The methods that can write to HTTP Response Body.
     * These methods can be dangerous if they are user controllable.
     */
    class HttpResponseBodySink extends SharedXss::Sink {
      HttpResponseBodySink() {
        exists(DataFlow::Method m |
          m.hasQualifiedName("github.com/valyala/fasthttp.RequestCtx", ["Success", "SuccessString"]) and
          this = m.getACall().getArgument(1)
        )
      }
    }
  }
}

/**
 * Provide Methods of fasthttp.RequestHeader which mostly used as remote user controlled sources
 */
module RequestHeader {
  /**
   * The methods as Remote user controllable source which are mostly related to HTTP Request Headers
   */
  class UntrustedFlowSource extends UntrustedFlowSource::Range instanceof DataFlow::Node {
    UntrustedFlowSource() {
      exists(DataFlow::Method m |
        m.hasQualifiedName("github.com/valyala/fasthttp.RequestHeader",
          [
            "Header", "TrailerHeader", "RequestURI", "Host", "UserAgent", "ContentEncoding",
            "ContentType", "Cookie", "CookieBytes", "MultipartFormBoundary", "Peek", "PeekAll",
            "PeekBytes", "PeekKeys", "PeekTrailerKeys", "Referer", "RawHeaders"
          ]) and
        this = m.getACall()
        or
        m.hasQualifiedName("github.com/valyala/fasthttp.RequestHeader", "Write") and
        this = m.getACall().getArgument(0)
      )
    }
  }
}

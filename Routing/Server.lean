/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http.Server
public import Routing.Trie

public section

@[expose] section

namespace Routing

open Std Async
open Std Http Server

abbrev Result := Request Body.Stream → ContextAsync (Response Body.Any)

/-- Default `404 Not Found` response used by `toHandler` when no route
matches. -/
def defaultNotFound : Result :=
  fun _request => Response.notFound.text "Not Found"

/-- Reads back the `MatchedRoute` `toHandler` published, from a request's or a response's
`extensions`. `none` means no route matched; absence is the signal, so a 404 is distinguishable
from a match rather than reported as an empty or guessed pattern. -/
def matchedRoute? (extensions : Extensions) : Option MatchedRoute :=
  extensions.get MatchedRoute

/-- The endpoint template of the route that matched (`MatchedRoute.template`), from a request's or
a response's `extensions`; `none` where `matchedRoute?` gives `none`.

Provided as a value telemetry middleware can be handed directly, supplying both an `http.route`
attribute and the span name built from it, so no consumer hand-rolls the composition and reaches
for `renderPattern` on the way. -/
def matchedPattern? (extensions : Extensions) : Option String :=
  (matchedRoute? extensions).map (·.template)

/-- Whether a request for `path` would match one of `routes` with a trailing slash added, as a
mounted index does (`mountSegs`, `Pattern.lean`). -/
def wantsSlash (routes : RouteIndex result) (method : Method) (path : List String) : Bool :=
  path.getLast? != some "" && (routes.matchTable method (path ++ [""])).isSome

/-- Where to redirect a request that matched no route but `wantsSlash`: its target with the slash
added, query intact. Serving the slashless form instead would break relative links from that
page. -/
def slashRedirect? (routes : RouteIndex result) (method : Method) (target : RequestTarget)
    (path : List String) : Option Header.Value :=
  if wantsSlash routes method path then
    let query := target.query
    Header.Value.ofString?
      (toString target.path ++ "/" ++ if query.isEmpty then "" else toString query)
  else
    none

/-- The decoded path segments that routes match against. -/
def decodedPath (target : RequestTarget) : List String :=
  target.path.toDecodedSegments.toList

/-- Decodes the request's method and path (`decodedPath` feeds `dispatch` via
`RouteIndex.matchTable`), finds the first route that matches, and applies its handler to the full
request.
A request that matches nothing but would with a trailing slash gets a `308` there instead
(`slashRedirect?`). `none` if neither.

The matched route is published (as a `MatchedRoute` extension, read back with `matchedRoute?`)
in *both* directions, because they reach different readers. The request copy is visible to the
matched handler and to anything the router calls into. The response copy is the one visible to
middleware *wrapping* the router: such middleware has already passed its request downwards by the
time matching happens, so the response is the only channel that travels back up to it. -/
def respond? (routes : RouteIndex Result) (request : Request Body.Stream) :
    Option (ContextAsync (Response Body.Any)) :=
  let path := decodedPath request.line.uri
  match routes.matchTable request.line.method path with
  | some (matched, handler) => some do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      (slashRedirect? routes request.line.method request.line.uri path).map fun location =>
        Response.withStatus .permanentRedirect |>.header Header.Name.location location |>.text ""

/-- Wires a route table into a `Std.Http.Server.Handler`, answering with `respond?`, else with
`notFound`. It builds a `RouteIndex` over `routes`, so build the handler once. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  let routes := RouteIndex.of routes
  Handler.ofFn fun request => (respond? routes request).getD (notFound request)

end Routing

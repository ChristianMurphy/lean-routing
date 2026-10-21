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
def wantsSlash (routes : List (Route Result)) (method : Method) (path : List String) : Bool :=
  path.getLast? != some "" && (matchTable routes method (path ++ [""])).isSome

/-- `target` with a slash added to its path, query intact. -/
def Internal.slashLocation? (target : RequestTarget) : Option Header.Value :=
  let query := target.query
  Header.Value.ofString?
    (toString target.path ++ "/" ++ if query.isEmpty then "" else toString query)

/-- Where to redirect a request that matched no route but `wantsSlash`: its target with the slash
added, query intact. Serving the slashless form instead would break relative links from that
page. -/
def slashRedirect? (routes : List (Route Result)) (method : Method) (target : RequestTarget)
    (path : List String) : Option Header.Value :=
  if wantsSlash routes method path then Internal.slashLocation? target else none

/-- The response to `request` from the route `found`, else a `308` when `slash ()` says a trailing
slash would match. -/
def Internal.respondTo (request : Request Body.Stream) (found : Option (MatchedRoute × Result))
    (slash : Unit → Bool) : Option (ContextAsync (Response Body.Any)) :=
  match found with
  | some (matched, handler) => some do
      let response ← handler { request with extensions := request.extensions.insert matched }
      return { response with extensions := response.extensions.insert matched }
  | none =>
      if slash () then
        (Internal.slashLocation? request.line.uri).map fun location =>
          Response.withStatus .permanentRedirect |>.header Header.Name.location location |>.text ""
      else
        none

/-- The decoded path segments that routes match against. -/
def decodedPath (target : RequestTarget) : List String :=
  target.path.toDecodedSegments.toList

/-- Decodes the request's method and path (`decodedPath` feeds `dispatch` via `matchTable`), tries
each route in order, and applies the matched handler to the full request.
A request that matches nothing but would with a trailing slash gets a `308` there instead
(`slashRedirect?`). `none` if neither.

The matched route is published (as a `MatchedRoute` extension, read back with `matchedRoute?`)
in *both* directions, because they reach different readers. The request copy is visible to the
matched handler and to anything the router calls into. The response copy is the one visible to
middleware *wrapping* the router: such middleware has already passed its request downwards by the
time matching happens, so the response is the only channel that travels back up to it. -/
def respond? (routes : List (Route Result)) (request : Request Body.Stream) :
    Option (ContextAsync (Response Body.Any)) :=
  let path := decodedPath request.line.uri
  let method := request.line.method
  Internal.respondTo request (matchTable routes method path) fun _ =>
    wantsSlash routes method path

/-- `respond?` through `index`, with one walk of its trie. -/
def Internal.RouteIndex.respond? (index : Internal.RouteIndex Result)
    (request : Request Body.Stream) : Option (ContextAsync (Response Body.Any)) :=
  let path := decodedPath request.line.uri
  let method := request.line.method
  let candidates := index.candidates path
  Internal.respondTo request (index.first candidates method path) fun _ =>
    index.wantsSlash candidates method path

/-- Wires a route table into a `Std.Http.Server.Handler`, answering as `respond?` does, else with
`notFound`. It builds a trie over `routes` to find each request's route, so build the handler
once. -/
def toHandler (routes : List (Route Result)) (notFound : Result := defaultNotFound) :
    StatelessHandler :=
  let index := Internal.RouteIndex.of routes
  Handler.ofFn fun request => (index.respond? request).getD (notFound request)

end Routing

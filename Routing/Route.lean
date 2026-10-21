/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Std.Http.Data.Method
public import Routing.Handler

/-!
Bundling a method, a path pattern, and a matching handler into a `Route`,
and dispatching an incoming `(Method, path)` against a table of them in
order.
-/

public section

@[expose] section

namespace Routing

open Std.Http (Method)

/-- An HTTP method, a path pattern (as already-parsed segments, so `HandlerType segs result`,
and therefore `handler`'s arity and types, is checked at the point the route is built), and its
handler. -/
structure Route (result : Type) where
  method : Method
  segs : List PathSeg
  handler : HandlerType segs result

/-- Builds a `Route` straight from already-parsed segments; no parsing, so no failure mode at
this call site. `segs` is meant to come from a `route_table`-generated `App.Patterns` value
(`RouteTable.lean`), whose pattern was already validated at the `route_table` row that declared
it. -/
def route (method : Method) (segs : List PathSeg) {result : Type}
    (handler : HandlerType segs result) : Route result :=
  { method, segs, handler }

/-- Per-method aliases for `route`, for `segs` sourced from a `route_table`-generated
`App.Patterns` value, so a route table can write `.get`/`.post`/`.put`/`.delete` instead of
`route .get`/`route .post`/etc. -/
def Route.get (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .get segs handler

def Route.post (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .post segs handler

def Route.put (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .put segs handler

def Route.delete (segs : List PathSeg) {result : Type} (handler : HandlerType segs result) :
    Route result :=
  route .delete segs handler

/-- Which route a dispatch matched. Carries the matched `Route`'s `method` and `segs` rather than
the `Route` itself: `segs` is the low-cardinality route *template* that identifies the endpoint
(what an OpenTelemetry `http.route` attribute wants, for instance), whereas the `Route` would also
hand out its `handler`, which is the router's business alone.

`segs` has any mount prefixes already applied, because `mount_routes`/`mount` rewrite a route's
own `segs` field (`RouteMount.lean`) rather than prefixing at dispatch time. -/
structure MatchedRoute where
  method : Method
  segs : List PathSeg
deriving Repr, DecidableEq, TypeName

/-- The matched route's endpoint template, e.g. `"/users/:id"`, with any mount prefixes already
applied. `renderTemplate` rather than `renderPattern`, so the string survives a change to a
capture's kind (`Pattern.lean`). -/
def MatchedRoute.template (matched : MatchedRoute) : String :=
  renderTemplate matched.segs

/-- Matches one route against an incoming method and decoded path,
producing the handler's result applied to any extracted captures. `none`
if the method doesn't match, or if `dispatch` rejects the path (literal
mismatch, mistyped capture, or arity mismatch; `Handler.lean`). -/
def Route.tryDispatch (r : Route result) (method : Method) (path : List String) :
    Option result :=
  if r.method == method then dispatch r.segs r.handler path else none

/-- Tries each route in order, returning the first match. Pairing this with
`Std.Http.Server.Handler` is `Server.lean`. -/
def dispatchTable (routes : List (Route result)) (method : Method) (path : List String) :
    Option result :=
  routes.findSome? (Route.tryDispatch · method path)

/-- `Route.tryDispatch`, additionally reporting *which* route matched. -/
def Route.tryMatch (r : Route result) (method : Method) (path : List String) :
    Option (MatchedRoute × result) :=
  (r.tryDispatch method path).map (fun res => ({ method := r.method, segs := r.segs }, res))

/-- `dispatchTable`, additionally reporting which route matched, since a `result` on its own says
nothing about the pattern that produced it.

Kept separate rather than either being defined in terms of the other, so `dispatchTable`'s callers
keep the definition they already unfold. The two share their first-match-wins order, so any change
to matching order belongs in both. `RouteIndex.matchTable` finds the same route with a trie
(`RouteIndex.matchTable_of`, `test/RoutingTests/Trie.lean`). -/
def matchTable (routes : List (Route result)) (method : Method) (path : List String) :
    Option (MatchedRoute × result) :=
  routes.findSome? (Route.tryMatch · method path)

end Routing

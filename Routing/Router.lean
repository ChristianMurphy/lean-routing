/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Server

public section

namespace Routing

open Std Async
open Std Http Server

/-- A route, or a group of entries mounted under a literal root. A mount's entries are written
against patterns relative to its root, typically the mounted table's own unprefixed `patterns`. A
root holding a `dotSegment` serves nothing, since no request can reach it. -/
inductive Entry where
  | route (route : Route Result)
  | mount (root : MountPoint) (entries : List Entry)

/-- `Route`'s per-method aliases, as entries; a handler's type is still fixed by its pattern. -/
def Entry.get (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.get segs handler)

def Entry.post (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.post segs handler)

def Entry.put (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.put segs handler)

def Entry.delete (segs : List PathSeg) (handler : HandlerType segs Result) : Entry :=
  .route (.delete segs handler)

/-- `r` with the literal `s` in front; `none` if `s` is a `dotSegment`. Its handler needs no
cast, because `HandlerType` reduces through a `.lit`. -/
def Route.consLit? (s : String) (r : Route result) : Option (Route result) :=
  if h : dotSegment s = false then
    some { method := r.method, segs := .lit s h :: r.segs, handler := r.handler }
  else
    none

/-- An index as a directory, so it renders and matches with a trailing slash once mounted. -/
def Route.asDirectory : Route result → Route result
  | { method, segs := [], handler } => { method, segs := [.lit ""], handler }
  | r => r

/-- `r` under the literal prefix `pre`, with the segments `mountSegs` gives; `none` if `pre`
holds a `dotSegment`. -/
def Route.under (pre : List String) (r : Route result) : Option (Route result) :=
  if pre.isEmpty then some r else pre.foldrM Route.consLit? r.asDirectory

mutual
/-- The routes an entry serves, in order, each with the full pattern of every mount enclosing it. -/
def Entry.toRoutes : Entry → List (Route Result)
  | .route r => [r]
  | .mount root entries => (Entry.listToRoutes entries).filterMap (Route.under root.segs)

def Entry.listToRoutes : List Entry → List (Route Result)
  | [] => []
  | e :: es => e.toRoutes ++ Entry.listToRoutes es
end

/-- A group of routes behind its own middleware, applied in list order, the first outermost.

A router takes a request if one of its routes matches it, or would with a trailing slash, if it
falls under one of its mounts' roots, or if one of its `routers` takes it. It serves a request with
its first route that matches (or the redirect `respond?` gives), else its first sub-router that
takes it, else `fallback`, a plain `404 Not Found` when `none`. So a miss under a mount is answered
by the router holding the mount, behind that router's middleware. -/
structure Router where
  middlewares : List (StatelessHandler → StatelessHandler) := []
  routes : List Entry := []
  routers : List Router := []
  fallback : Option StatelessHandler := none

private structure Compiled where
  takes : Method → List String → Bool
  handler : StatelessHandler

private def decodedPath (target : RequestTarget) : List String :=
  target.path.toDecodedSegments.toList

mutual
/-- Everything not depending on the request is computed here, once, middleware included. -/
private def Router.compile : Router → Compiled
  | { middlewares, routes, routers, fallback } =>
    let flat := Entry.listToRoutes routes
    let roots := routes.filterMap fun
      | .mount root _ => if root.segs.any dotSegment then none else some root.segs
      | .route _ => none
    let subs := Router.compileAll routers
    let fallback := fallback.getD (Handler.ofFn defaultNotFound)
    let own (method : Method) (path : List String) : Bool :=
      (matchTable flat method path).isSome || wantsSlash flat method path
    let next (method : Method) (path : List String) : StatelessHandler :=
      match subs.find? (·.takes method path) with
      | some sub => sub.handler
      | none => fallback
    let inner : StatelessHandler :=
      { onRequest := fun request =>
          match respond? flat request with
          | some response => response
          | none => (next request.line.method (decodedPath request.line.uri)).onRequest request
        -- A sub-router's middleware may refuse a body it would not accept, so ask the router
        -- that would serve the request.
        onContinue := fun head =>
          let path := decodedPath head.uri
          if own head.method path then pure true else (next head.method path).onContinue head }
    { takes := fun method path =>
        own method path || roots.any (·.isPrefixOf path) || subs.any (·.takes method path)
      handler := middlewares.foldr (· ·) inner }

private def Router.compileAll : List Router → List Compiled
  | [] => []
  | r :: rs => r.compile :: Router.compileAll rs
end

def Router.toHandler (router : Router) : StatelessHandler :=
  router.compile.handler

end Routing

/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Router
import Routing.RouteTable

namespace Routing

open Std Async
open Std Http Server

theorem foldrM_consLit_segs (pre : List String) (r : Route α) :
    (pre.foldrM Route.consLit? r).map (·.segs) = (pre.mapM PathSeg.lit?).map (· ++ r.segs) := by
  induction pre with
  | nil => simp
  | cons s rest ih =>
    simp only [List.foldrM_cons, List.mapM_cons]
    cases h : rest.foldrM Route.consLit? r <;> cases hm : rest.mapM PathSeg.lit? <;>
      simp_all [Route.consLit?, PathSeg.lit?] <;> split <;> simp_all

theorem mapM_lit?_ne_nil (s : String) (rest : List String) :
    (s :: rest).mapM PathSeg.lit? ≠ some [] := by
  simp only [List.mapM_cons]
  cases PathSeg.lit? s <;> cases rest.mapM PathSeg.lit? <;> simp

/-- A route in a `Router` mount has exactly the pattern a `route_table` mount gives it, so it
matches, and reports, what the table's links point at; and a mount holding a dot segment, which
no `PathSeg.lit` can, serves nothing. -/
theorem Route.under_segs (pre : List String) (r : Route α) :
    (r.under pre).map (·.segs) = (pre.mapM PathSeg.lit?).map (mountSegs · r.segs) := by
  obtain ⟨method, segs, handler⟩ := r
  cases pre with
  | nil => simp [Route.under, mountSegs]
  | cons s rest =>
    simp only [Route.under, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      foldrM_consLit_segs]
    have := mapM_lit?_ne_nil s rest
    cases h : (s :: rest).mapM PathSeg.lit? with
    | none => rfl
    | some ps =>
      cases ps with
      | nil => exact absurd h this
      | cons p ps => cases segs <;> simp [Route.asDirectory, mountSegs]

route_table RouterV1
  [ ping := "/ping" ]

route_table RouterApi
  [ index := "/",
    user := "/users/:id:Nat",
    v1 := mount "/v1" RouterV1 ]

route_table RouterSite
  [ home := "/",
    api := mount "/api" RouterApi ]

#guard RouterSite.patterns.mountedAt = []
#guard RouterSite.patterns.api.v1.mountedAt = ["api", "v1"]
#guard RouterSite.links.mountedAt = "/"
#guard RouterSite.links.api.v1.mountedAt = "/api/v1"
#guard ((RouterSite.patterns.api : MountPoint)).segs = ["api"]

/--
error: route name 'mountedAt' is reserved for the prefix the table is mounted under
-/
#guard_msgs in
route_table RouterReserved
  [ mountedAt := "/x" ]

/-- The middleware names a response passed through, innermost first. -/
private structure Trace where
  names : List String
deriving TypeName

private def tag (name : String) (h : StatelessHandler) : StatelessHandler :=
  { h with onRequest := fun request => do
      let response ← h.onRequest request
      let names := ((response.extensions.get Trace).map (·.names)).getD []
      return { response with extensions := response.extensions.insert (Trace.mk (names ++ [name])) } }

private def refuseContinue (h : StatelessHandler) : StatelessHandler :=
  { h with onContinue := fun _ => pure false }

/-- The template the handler saw on its own request. -/
private structure TemplateSeen where
  template : Option String
deriving TypeName

private def ok (body : String) : Result := fun _ => Response.ok.text body

private def apiRouter : Router :=
  { middlewares := [tag "api", refuseContinue]
    routes :=
      [ .mount RouterSite.patterns.api
          [ .get RouterApi.patterns.index (ok "api"),
            .get RouterApi.patterns.user fun (id : Nat) request => do
              let response ← Response.ok.text s!"user {id}"
              let seen := TemplateSeen.mk (matchedPattern? request.extensions)
              return { response with extensions := response.extensions.insert seen },
            .mount RouterApi.patterns.v1 [ .get RouterV1.patterns.ping (ok "pong") ] ] ]
    fallback := some (Handler.ofFn fun _ => Response.badRequest.text "api miss") }

private def tenantRouter : Router :=
  { routes := ["acme", ".."].map fun tenant => .mount ⟨["t", tenant]⟩ [ .get [] (ok tenant) ] }

#guard (Entry.mount ⟨["t", ".."]⟩ [ .get [] (ok "unreachable") ]).toRoutes.isEmpty

private def siteRouter : Router :=
  { middlewares := [tag "outer", tag "inner"]
    routes :=
      [ .get RouterSite.patterns.home (ok "home"),
        .get [.lit "api", .lit "special"] (ok "special") ]
    routers := [apiRouter, tenantRouter] }

private def siteHandler : StatelessHandler := siteRouter.toHandler

private structure Outcome where
  status : Status
  trace : List String
  pattern : Option String
  seen : Option (Option String)
  location : Option String

private def run (target : String) : IO Outcome :=
  Async.block <| ContextAsync.run do
    let some uri := RequestTarget.parse? target
      | throw (IO.userError s!"test target {target.quote} is not a valid request target")
    let body ← Body.empty
    let response ← siteHandler.onRequest ((Request.get uri).body body)
    return { status := response.line.status
             trace := ((response.extensions.get Trace).map (·.names)).getD []
             pattern := matchedPattern? response.extensions
             seen := (response.extensions.get TemplateSeen).map (·.template)
             location := (response.line.headers.get? Header.Name.location).map toString }

private def continues (target : String) : IO Bool := do
  let some uri := RequestTarget.parse? target
    | throw (IO.userError s!"test target {target.quote} is not a valid request target")
  Async.block <| siteHandler.onContinue { method := .post, version := .v11, uri }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

#eval show IO Unit from do
  let o ← run "/"
  check s!"/: {repr o.trace} {repr o.pattern}"
    (o.status == .ok && o.trace == ["inner", "outer"] && o.pattern == some "/")

  let o ← run "/api/users/7"
  check s!"/api/users/7: {repr o.trace} {repr o.pattern} {repr o.seen}"
    (o.status == .ok && o.trace == ["api", "inner", "outer"] &&
      o.pattern == some "/api/users/:id" && o.seen == some (some "/api/users/:id"))

  let o ← run "/api/v1/ping"
  check s!"/api/v1/ping: {repr o.pattern}" (o.status == .ok && o.pattern == some "/api/v1/ping")

  -- A miss under a mount is answered by the router holding it, behind its own middleware.
  let o ← run "/api/v1/nope"
  check s!"/api/v1/nope: {repr o.trace} {repr o.pattern}"
    (o.status == .badRequest && o.trace == ["api", "inner", "outer"] && o.pattern == none)

  let o ← run "/api?q=1"
  check s!"/api: {repr o.location}"
    (o.status == .permanentRedirect && o.location == some "/api/?q=1" &&
      o.trace == ["api", "inner", "outer"])

  -- A router's own entries come before its sub-routers, even one whose mount covers the path.
  let o ← run "/api/special"
  check s!"/api/special: {repr o.trace}" (o.status == .ok && o.trace == ["inner", "outer"])

  let o ← run "/t/acme/"
  check s!"/t/acme/: {repr o.pattern}" (o.status == .ok && o.pattern == some "/t/acme/")

  let o ← run "/nope"
  check s!"/nope: {repr o.trace} {repr o.pattern}"
    (o.status == .notFound && o.trace == ["inner", "outer"] && o.pattern == none)

  check "/api/users/7 should ask the API router whether to continue"
    (!(← continues "/api/users/7"))
  check "/ should continue" (← continues "/")
  check "/nope should continue" (← continues "/nope")

end Routing

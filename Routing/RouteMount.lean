/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Routing.Route
public meta import Routing.Pattern

/-!
`mount_routes "prefix" routes`: the `Route`-level analogue of `route_table`'s `mount` row
(`RouteTable.lean`). It prefixes every route in `routes` (a `List (Route result)`, typically built
against a sub-app's own, unprefixed `route_table`-generated `patterns`) with `prefix`'s literal
segments, for splicing into a parent app's route list.

Unlike `mount`, this needs no structural recursion to reach arbitrary nesting depth: `Route`s
already live in a flat, ordered `List`, so nesting is just repeated prefixing and `++`, which
associates freely (`mount_routes "/outer" (mount_routes "/mid" innerRoutes ++ ownRoutes)`).

No handler-level glue is needed either: `HandlerType` (`Handler.lean`) skips over `.lit` segments
without adding an argument, so only each route's `segs` field actually changes, to `mountSegs prefix
segs` (`Pattern.lean`). The prefix's `.lit` segments are literal constructors sitting right there in
the generated term, and the match on whether `segs` is empty settles which case of `mountSegs`
applies, so in each branch `HandlerType` reduces to `HandlerType segs result` and the unchanged
`handler` field is accepted without a cast or proof.
-/

public section

namespace Routing

open Lean

private meta def segTerm : PathSeg → MacroM (TSyntax `term)
  | .lit s _ => `(Routing.PathSeg.lit $(quote s))
  | .capture name .nat => `(Routing.PathSeg.capture $(quote name) .nat)
  | .capture name .string => `(Routing.PathSeg.capture $(quote name) .string)

/-- Parses `pat` into segments for a mount prefix, rejecting captures: the same restriction, and
the same error message, as `route_table`'s `mount` row; see `prefixSegsSrcFor`,
`RouteTable.lean`. -/
private meta def mountPrefixSegs (pat : TSyntax `str) : MacroM (List PathSeg) := do
  match parsePattern pat.getString with
  | none => Macro.throwErrorAt pat s!"invalid route pattern {pat.getString.quote}"
  | some segs =>
      if segs.any (fun | .capture .. => true | .lit _ _ => false) then
        Macro.throwErrorAt pat
          s!"mount prefix must not contain captures (got {pat.getString.quote}); captured mount prefixes are not yet supported"
      else
        pure segs

macro "mount_routes" pat:str routes:term:max : term => do
  let segs ← mountPrefixSegs pat
  let segTerms ← segs.toArray.mapM segTerm
  `(($routes).map fun
      | { method, segs := [], handler } =>
          { method, segs := Routing.mountSegs [$segTerms,*] [], handler }
      | { method, segs := s :: ss, handler } =>
          { method, segs := Routing.mountSegs [$segTerms,*] (s :: ss), handler })

end Routing

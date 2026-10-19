/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Handler
import Routing.RelativeLink
import Std.Http.Data.URI
import Std.Data.String.ToNat
import Plausible

namespace Routing

private def userPattern : List PathSeg := [.lit "users", .capture "id" .nat]

private def userHandler : HandlerType userPattern String :=
  fun (id : Nat) => s!"user #{id}"

#guard dispatch userPattern userHandler ["users", "42"] = some "user #42"
#guard dispatch userPattern userHandler ["users", "notanumber"] = none
#guard dispatch userPattern userHandler ["users", "042"] = none -- only the digits a link renders
#guard dispatch userPattern userHandler ["users", "4_2"] = none
#guard dispatch userPattern userHandler ["posts", "42"] = none          -- literal mismatch
#guard dispatch userPattern userHandler ["users"] = none                -- too few path segments
#guard dispatch userPattern userHandler ["users", "42", "extra"] = none -- too many path segments
#guard dispatch userPattern userHandler ["users", "42", ""] = some "user #42" -- trailing slash

/-- A `Nat` capture matches the digits a link renders for it. -/
theorem parseNat?_toString (n : Nat) : parseNat? (toString n) = some n := by
  simp [parseNat?, Option.filter, toString, Nat.toNat?_repr]

/-- A `Nat` capture matches nothing else, so each number has one path. -/
theorem toString_of_parseNat? {s : String} {n : Nat} (h : parseNat? s = some n) :
    toString n = s := by
  unfold parseNat? Option.filter at h
  split at h
  · split at h
    · cases h; simp_all
    · cases h
  · cases h

-- Negative-compile regression: a wrong-arity handler against a real
-- pattern is rejected at compile time.
/--
error: Type mismatch
  fun _id _extra => "oops"
has type
  Nat → String → String
but is expected to have type
  HandlerType userPattern String
-/
#guard_msgs in
def badArity : HandlerType userPattern String :=
  fun (_id : Nat) (_extra : String) => "oops"

-- These examples stand in for the theorem one really wants: that dispatching the path `linkFor`
-- renders recovers the very captures it was given. Both halves of that round trip bottom out in
-- string functions with no equational theory to work from: `pathSegments` is `String.splitOn`,
-- whose implementation walks byte positions with a hand-written termination argument, and a `.nat`
-- capture needs `String.toNat?` to invert `toString`. Neither round trip has lemmas in core, so
-- proving this means building both theories first. `Routing/Pattern.lean` sidesteps exactly this
-- by parsing over `List Char` structurally, which is why its round trip *is* proved
-- (`parsePattern_renderPattern`, `Pattern.lean`).
#guard linkFor ([] : List PathSeg) = "/"
#guard linkFor [.lit "active"] = "/active"
#guard linkFor [.lit "todos", .capture "id" .nat] 42 = "/todos/42"
#guard linkFor [.lit "todos", .capture "id" .nat, .lit "edit"] 42 = "/todos/42/edit"
#guard linkFor [.lit "users", .capture "name" .string] "ada" = "/users/ada"
#guard linkFor [.lit "users", .capture "name" .string] "a b/c%" = "/users/a%20b%2Fc%25"

#guard dispatch userPattern userHandler (pathSegments (linkFor userPattern 42)) = some "user #42"

private def namePattern : List PathSeg := [.lit "users", .capture "name" .string, .lit "posts"]

private def nameHandler : HandlerType namePattern String := fun (name : String) => name

/-- The segments a server dispatches on: parsed and percent-decoded by `Std.Http`, as `toHandler`
does with a request's target. -/
private def served (link : String) : List String :=
  ((Std.Http.RequestTarget.parse? link).map (·.path.toDecodedSegments.toList)).getD []

private def literalRoundTrips (s : String) (h : dotSegment s = false := by decide) : Bool :=
  dispatch [.lit "docs", .lit s h] "ok" (served (linkFor [.lit "docs", .lit s h])) == some "ok"

#guard literalRoundTrips "c#" && literalRoundTrips "a?b" && literalRoundTrips "50%off" &&
  literalRoundTrips "a%20b"

#guard ["", ".", ".."].all fun name =>
  dispatch namePattern nameHandler (served (linkFor namePattern name)) == none

/-- Weighted towards the characters a path segment treats specially, with arbitrary ones mixed in.
`Plausible`'s own `String` generator fixes its `Char` generator, so this replaces it whole. -/
private local instance (priority := high) : Plausible.Arbitrary String where
  arbitrary := do
    let chars ← Plausible.Gen.listOf
      (Plausible.Char.arbitraryFromList 3 "./%?#: aZ".toList (by decide)).arbitrary
    return String.ofList chars

-- A property, not a theorem: the round trip rests on `Std.Http`'s encoder and decoder, which have
-- no lemmas relating them.
#eval Plausible.Testable.check
  (∀ lit name : String, (if h : dotSegment lit = false then
    lit == "" || dispatch [.lit lit h, .capture "name" .string] (fun name => name)
      (served (linkFor [.lit lit h, .capture "name" .string] name)) ==
      if unlinkable name then none else some name
  else true) = true)
  { numInst := 1000, quiet := true }

end Routing

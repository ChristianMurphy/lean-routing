/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Handler
import Std.Data.String.ToNat
import Std.Http.Data.URI

namespace Routing

open Std.Http

/-- One value per capture in `segs`, in order. -/
def Args : List PathSeg → Type
  | [] => Unit
  | .lit _ _ :: rest => Args rest
  | .capture _ kind :: rest => kind.type × Args rest

def applyHandler : (segs : List PathSeg) → HandlerType segs r → Args segs → r
  | [], h, _ => h
  | .lit _ _ :: rest, h, args => applyHandler rest h args
  | .capture _ _ :: rest, h, (a, args) => applyHandler rest (h a) args

def applyLink : (segs : List PathSeg) → LinkType segs → Args segs → String
  | [], l, _ => l
  | .lit _ _ :: rest, l, args => applyLink rest l args
  | .capture _ _ :: rest, l, (a, args) => applyLink rest (l a) args

/-- The decoded segments of the link built from `args`. -/
def pathOf : (segs : List PathSeg) → Args segs → List String
  | [], _ => []
  | .lit s _ :: rest, args => s :: pathOf rest args
  | .capture _ .nat :: rest, (n, args) => toString n :: pathOf rest args
  | .capture _ .string :: rest, (s, args) => s :: pathOf rest args

/-- Every `String` capture in `args` is one a link can carry. -/
def Linkable : (segs : List PathSeg) → Args segs → Prop
  | [], _ => True
  | .lit _ _ :: rest, args => Linkable rest args
  | .capture _ .nat :: rest, (_, args) => Linkable rest args
  | .capture _ .string :: rest, (s, args) => unlinkable s = false ∧ Linkable rest args

theorem dispatch_pathOf : ∀ (segs : List PathSeg) (h : HandlerType segs r) (args : Args segs),
    Linkable segs args → dispatch segs h (pathOf segs args) = some (applyHandler segs h args)
  | [], h, _, _ => by simp [pathOf, dispatch, applyHandler]
  | .lit s _ :: rest, h, args, hl => by
    simp only [pathOf, dispatch, BEq.rfl, ite_true, applyHandler]
    exact dispatch_pathOf rest h args hl
  | .capture _ .nat :: rest, h, (n, args), hl => by
    simp only [pathOf, dispatch, toString, Nat.toNat?_repr, Option.bind_some, applyHandler]
    exact dispatch_pathOf rest (h n) args hl
  | .capture _ .string :: rest, h, (s, args), ⟨hs, hl⟩ => by
    simp only [pathOf, dispatch, hs, Bool.false_eq_true, ite_false, applyHandler]
    exact dispatch_pathOf rest (h s) args hl

/-- The decoded segments `respond?` dispatches on, for a request target. -/
def requestSegments (target : String) : Option (List String) :=
  (RequestTarget.parse? target).map (·.path.toDecodedSegments.toList)

/-- A link to the decoded segments `xs`, each percent-encoded as `linkParts` encodes it. -/
def joinEncoded (xs : List String) : String :=
  "/" ++ "/".intercalate (xs.map fun x => toString (URI.EncodedSegment.encode x))

/-- Whether `joinEncoded xs` is within `Std.Http`'s default limits on a path. -/
def fits (xs : List String) : Bool :=
  let config : URI.Config := {}
  xs.length ≤ config.maxPathSegments &&
    xs.all (fun x => (toString (URI.EncodedSegment.encode x)).utf8ByteSize ≤
      config.maxSegmentLength) &&
    (joinEncoded xs).utf8ByteSize ≤ config.maxTotalPathLength

/-- `Std.Http` reads a link back as the segments it joins. The link `/` for `[""]` reads back as `[]`,
hence the first condition. The parser and decoder have no lemmas, so `Handler.lean` checks this as a
property. -/
def ReadsBack : Prop :=
  ∀ xs : List String, xs.head? ≠ some "" → fits xs → requestSegments (joinEncoded xs) = some xs

/-- Encoding leaves a number's digits alone, so `linkParts` can leave a `Nat` capture unencoded.
The encoder has no lemmas, so `Handler.lean` checks this as a property. -/
def EncodesDigits : Prop :=
  ∀ n : Nat, toString (URI.EncodedSegment.encode (toString n)) = toString n

/-- `segs` does not start with an empty literal. A browser sends a link starting with `//` to
another host (#9). -/
def FirstNonEmpty : List PathSeg → Prop
  | .lit s _ :: _ => s ≠ ""
  | _ => True

private theorem applyLink_linkParts (hd : EncodesDigits) :
    ∀ (segs : List PathSeg) (parts : List String) (args : Args segs),
    applyLink segs (linkParts segs parts) args =
      "/" ++ "/".intercalate
        (parts ++ (pathOf segs args).map fun x => toString (URI.EncodedSegment.encode x))
  | [], parts, _ => by simp [applyLink, linkParts, pathOf]
  | .lit _ _ :: rest, parts, args =>
    (applyLink_linkParts hd rest _ args).trans (by simp [pathOf])
  | .capture _ .nat :: rest, parts, (n, args) =>
    (applyLink_linkParts hd rest _ args).trans (by simp only [pathOf, List.map_cons, hd n]; simp)
  | .capture _ .string :: rest, parts, (_, args) =>
    (applyLink_linkParts hd rest _ args).trans (by simp [pathOf])

theorem applyLink_linkFor (hd : EncodesDigits) (segs : List PathSeg) (args : Args segs) :
    applyLink segs (linkFor segs) args = joinEncoded (pathOf segs args) := by
  simpa [linkFor, joinEncoded] using applyLink_linkParts hd segs [] args

theorem head_pathOf_ne_empty : ∀ (segs : List PathSeg) (args : Args segs),
    Linkable segs args → FirstNonEmpty segs → (pathOf segs args).head? ≠ some ""
  | [], _, _, _ => by simp [pathOf]
  | .lit _ _ :: _, _, _, hf => by simpa [pathOf, FirstNonEmpty] using hf
  | .capture _ .nat :: _, (n, _), _, _ => by
    intro h
    have : (toString n).toNat? = some n := Nat.toNat?_repr n
    simp_all [pathOf]
  | .capture _ .string :: _, (_, _), ⟨_, _⟩, _ => by
    simp_all [pathOf, unlinkable]

/-- A request for a link that `linkFor` builds reaches the route's handler with the values passed to
`linkFor`. -/
theorem requestSegments_linkFor (hr : ReadsBack) (hd : EncodesDigits) (segs : List PathSeg)
    (h : HandlerType segs r) (args : Args segs) (hl : Linkable segs args)
    (hf : FirstNonEmpty segs) (hfits : fits (pathOf segs args)) :
    (requestSegments (applyLink segs (linkFor segs) args)).bind (dispatch segs h) =
      some (applyHandler segs h args) := by
  rw [applyLink_linkFor hd, hr _ (head_pathOf_ne_empty segs args hl hf) hfits, Option.bind_some,
    dispatch_pathOf segs h args hl]

end Routing

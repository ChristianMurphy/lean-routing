/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Server
import Std.Data.String.ToNat
import Std.Http.Data.URI

namespace Routing

open Std.Http URI Internal.Char

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
  (RequestTarget.parse? target).map decodedPath

/-- A link to the decoded segments `xs`, each percent-encoded as `linkParts` encodes it. -/
def joinEncoded (xs : List String) : String :=
  "/" ++ "/".intercalate (xs.map fun x => toString (URI.EncodedSegment.encode x))

/-- Whether `joinEncoded xs` is within `Std.Http`'s default limits on a path and on a request
target. -/
def fits (xs : List String) : Bool :=
  let config : URI.Config := {}
  xs.length ≤ config.maxPathSegments &&
    xs.all (fun x => (toString (URI.EncodedSegment.encode x)).utf8ByteSize ≤
      config.maxSegmentLength) &&
    (joinEncoded xs).utf8ByteSize ≤ config.maxTotalPathLength &&
    (joinEncoded xs).utf8ByteSize ≤ ({} : Std.Http.Config).maxUriLength

/-- Whether `Std.Http` reads the link for `xs` back as `xs`. The link `/` for `[""]` reads back as
`[]`, hence the first condition. -/
def readsBack (xs : List String) : Bool :=
  xs == [""] || !fits xs || requestSegments (joinEncoded xs) == some xs

/-- `readsBack` holds for every list. `Std.Http`'s parser and decoder have no lemmas, so
`Handler.lean` checks this as a property. -/
def ReadsBack : Prop :=
  ∀ xs, readsBack xs = true

theorem requestSegments_joinEncoded (hr : ReadsBack) (xs : List String) (he : xs ≠ [""])
    (hfits : fits xs) : requestSegments (joinEncoded xs) = some xs := by
  simpa [readsBack, he, hfits] using hr xs

-- `encode_repr` reads the encoder's `ByteArray.foldl` as a list fold, which core has no lemma for.
private theorem foldlM_loop_id {β : Type} (f : β → UInt8 → β) (as : ByteArray) (stop : Nat)
    (h : stop ≤ as.size) : ∀ (i j : Nat) (b : β), stop - j ≤ i →
    ByteArray.foldlM.loop (m := Id) (fun b a => pure (f b a)) as stop h i j b =
      ((as.data.toList.drop j).take (stop - j)).foldl f b := by
  intro i
  induction i with
  | zero =>
    intro j b hi
    unfold ByteArray.foldlM.loop
    simp [show stop - j = 0 by omega]; rfl
  | succ i ih =>
    intro j b hi
    unfold ByteArray.foldlM.loop
    by_cases hj : j < stop
    · simp only [hj, dite_true]
      have hjs : j < as.data.toList.length := by
        rw [Array.length_toList]; exact Nat.lt_of_lt_of_le hj h
      rw [List.drop_eq_getElem_cons hjs, show stop - j = (stop - (j + 1)) + 1 by omega,
        List.take_succ_cons, List.foldl_cons]
      exact ih (j + 1) (f b as[j]) (by omega)
    · simp [hj, show stop - j = 0 by omega]; rfl

private theorem foldl_eq_foldl_toList {β : Type} (f : β → UInt8 → β) (init : β) (as : ByteArray) :
    as.foldl f init = as.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  show ByteArray.foldlM.loop (m := Id) _ as as.size _ (as.size - 0) 0 init = _
  rw [foldlM_loop_id f as as.size (Nat.le_refl _) _ 0 init (by omega), Nat.sub_zero,
    List.drop_zero, List.take_of_length_le (i := as.size) (l := as.data.toList)
      (Nat.le_of_eq Array.length_toList)]

private theorem digit_kept (b : UInt8) (h1 : 48 ≤ b.toNat) (h2 : b.toNat ≤ 57) :
    isAsciiByte b ∧ isPChar b := by
  have hk : ∀ k, k < 10 → isAsciiByte (UInt8.ofNat (48 + k)) ∧ isPChar (UInt8.ofNat (48 + k)) := by
    decide
  have := hk (b.toNat - 48) (by omega)
  rwa [show 48 + (b.toNat - 48) = b.toNat by omega, UInt8.ofNat_toNat] at this

private theorem foldl_push {β : Type} (f : β → UInt8 → β) (bytes : β → ByteArray)
    (hf : ∀ acc c, 48 ≤ c.toNat → c.toNat ≤ 57 → bytes (f acc c) = (bytes acc).push c) :
    ∀ (l : List UInt8) (acc : β), (∀ b ∈ l, 48 ≤ b.toNat ∧ b.toNat ≤ 57) →
      (bytes (l.foldl f acc)).data.toList = (bytes acc).data.toList ++ l
  | [], _, _ => by simp
  | b :: l, acc, hl => by
    have ⟨h1, h2⟩ := hl b (by simp)
    rw [List.foldl_cons, foldl_push f bytes hf l _ (fun x hx => hl x (by simp [hx])),
      hf acc b h1 h2]
    simp [ByteArray.push]

private theorem encode_digits (s : String)
    (hs : ∀ b ∈ s.toUTF8.data.toList, 48 ≤ b.toNat ∧ b.toNat ≤ 57) :
    (EncodedSegment.encode s).toByteArray = s.toUTF8 := by
  unfold EncodedSegment.encode EncodedString.encode
  rw [foldl_eq_foldl_toList]
  generalize hf : (fun (acc : EncodedString isPChar) c => _) = f
  have hstep : ∀ acc c, 48 ≤ c.toNat → c.toNat ≤ 57 →
      (f acc c).toByteArray = acc.toByteArray.push c := by
    intro acc c h1 h2
    subst hf
    simp only [dite_eq_left (digit_kept c h1 h2)]
    -- The encoder's `push` is private, but this file is not a module, so `rfl` can unfold it.
    rfl
  exact ByteArray.ext (Array.toList_inj.mp
    (foldl_push f EncodedString.toByteArray hstep _ EncodedString.empty hs))

private theorem toUTF8_repr (n : Nat) :
    ∀ b ∈ (toString n).toUTF8.data.toList, 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  intro b hb
  simp only [String.toUTF8_eq_toByteArray, toString, Nat.repr, String.toByteArray_ofList,
    List.utf8Encode, List.toList_data_toByteArray, List.mem_flatMap] at hb
  obtain ⟨c, hc, hb⟩ := hb
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at hd
  rw [String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.mpr
    (by rw [UInt32.le_iff_toNat_le]; simp at hd ⊢; omega))] at hb
  simp only [List.mem_singleton] at hb
  subst hb
  simp only [UInt32.toNat_toUInt8] at hd ⊢
  simp at hd
  have : c.toNat = c.val.toNat := rfl
  omega

/-- Encoding leaves a number's digits alone, so `linkParts` can leave a `Nat` capture unencoded. -/
theorem encode_repr (n : Nat) : toString (EncodedSegment.encode (toString n)) = toString n :=
  String.toByteArray_inj.mp (encode_digits _ (toUTF8_repr n))

/-- `segs` does not start with an empty literal. A browser sends a link starting with `//` to
another host (#9). -/
def FirstNonEmpty : List PathSeg → Prop
  | .lit s _ :: _ => s ≠ ""
  | _ => True

private theorem applyLink_linkParts :
    ∀ (segs : List PathSeg) (parts : List String) (args : Args segs),
    applyLink segs (linkParts segs parts) args =
      "/" ++ "/".intercalate
        (parts ++ (pathOf segs args).map fun x => toString (URI.EncodedSegment.encode x))
  | [], parts, _ => by simp [applyLink, linkParts, pathOf]
  | .lit _ _ :: rest, parts, args =>
    (applyLink_linkParts rest _ args).trans (by simp [pathOf])
  | .capture _ .nat :: rest, parts, (n, args) =>
    (applyLink_linkParts rest _ args).trans
      (by simp only [pathOf, List.map_cons, encode_repr n]; simp)
  | .capture _ .string :: rest, parts, (_, args) =>
    (applyLink_linkParts rest _ args).trans (by simp [pathOf])

theorem applyLink_linkFor (segs : List PathSeg) (args : Args segs) :
    applyLink segs (linkFor segs) args = joinEncoded (pathOf segs args) := by
  simpa [linkFor, joinEncoded] using applyLink_linkParts segs [] args

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
theorem requestSegments_linkFor (hr : ReadsBack) (segs : List PathSeg)
    (h : HandlerType segs r) (args : Args segs) (hl : Linkable segs args)
    (hf : FirstNonEmpty segs) (hfits : fits (pathOf segs args)) :
    (requestSegments (applyLink segs (linkFor segs) args)).bind (dispatch segs h) =
      some (applyHandler segs h args) := by
  have he : pathOf segs args ≠ [""] := fun h' =>
    head_pathOf_ne_empty segs args hl hf (by simp [h'])
  rw [applyLink_linkFor, requestSegments_joinEncoded hr _ he hfits, Option.bind_some,
    dispatch_pathOf segs h args hl]

end Routing

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
  encodedPath (xs.map fun x => toString (URI.EncodedSegment.encode x))

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
`[]`, and `decodedPath` drops a `.` before an empty first segment, hence the first two conditions. -/
def readsBack (xs : List String) : Bool :=
  xs == [""] || xs.take 2 == [".", ""] || !fits xs || requestSegments (joinEncoded xs) == some xs

/-- `readsBack` holds for every list. `Std.Http`'s parser and decoder have no lemmas, so
`Handler.lean` checks this as a property. -/
def ReadsBack : Prop :=
  ∀ xs, readsBack xs = true

theorem requestSegments_joinEncoded (hr : ReadsBack) (xs : List String) (he : xs ≠ [""])
    (hd : xs.take 2 ≠ [".", ""]) (hfits : fits xs) : requestSegments (joinEncoded xs) = some xs := by
  simpa [readsBack, he, hd, hfits] using hr xs

-- `encode_repr` reads the encoder's `ByteArray.foldl` as a list fold, which core has no lemma for.
private theorem foldlM_loop_data {β : Type} {m : Type → Type} [Monad m] {f : β → UInt8 → m β}
    {as : ByteArray} {stop : Nat} (h : stop ≤ as.size) (i j : Nat) (b : β) :
    ByteArray.foldlM.loop f as stop h i j b = Array.foldlM.loop f as.data stop h i j b := by
  induction i generalizing j b with
  | zero => unfold ByteArray.foldlM.loop Array.foldlM.loop; rfl
  | succ i ih =>
    unfold ByteArray.foldlM.loop Array.foldlM.loop
    split
    · simp only [ih]; rfl
    · rfl

private theorem foldlM_data {β : Type} {m : Type → Type} [Monad m] {f : β → UInt8 → m β}
    {init : β} {as : ByteArray} {start stop : Nat} :
    as.foldlM f init start stop = as.data.foldlM f init start stop := by
  unfold ByteArray.foldlM Array.foldlM
  by_cases h : stop ≤ as.size
  · have h' : stop ≤ as.data.size := h
    simp only [h, h', ↓reduceDIte, foldlM_loop_data]
  · have h' : ¬stop ≤ as.data.size := h
    simp only [h, h', ↓reduceDIte, foldlM_loop_data]; rfl

private theorem foldl_eq_foldl_toList {β : Type} (f : β → UInt8 → β) (init : β) (as : ByteArray) :
    as.foldl f init = as.data.toList.foldl f init :=
  (foldlM_data (m := Id)).trans (Array.foldl_toList f).symm

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

private theorem applyLink_linkParts :
    ∀ (segs : List PathSeg) (parts : List String) (args : Args segs),
    applyLink segs (linkParts segs parts) args =
      encodedPath (parts ++ (pathOf segs args).map fun x => toString (URI.EncodedSegment.encode x))
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

private theorem pathOf_ne_nil : ∀ (segs : List PathSeg) (args : Args segs),
    segs ≠ [] → pathOf segs args ≠ []
  | .lit _ _ :: _, _, _ => by simp [pathOf]
  | .capture _ .nat :: _, (_, _), _ => by simp [pathOf]
  | .capture _ .string :: _, (_, _), _ => by simp [pathOf]

theorem pathOf_ne_singleton_empty : ∀ (segs : List PathSeg) (args : Args segs),
    Linkable segs args → (∀ h, segs ≠ [.lit "" h]) → pathOf segs args ≠ [""]
  | [], _, _, _ => by simp [pathOf]
  | [.lit s h], _, _, hn => by
    intro he
    simp [pathOf] at he
    subst he
    exact hn h rfl
  | .lit _ _ :: s :: rest, args, _, _ => by
    simpa [pathOf] using fun _ => pathOf_ne_nil (s :: rest) args (by simp)
  | .capture _ .nat :: _, (n, _), _, _ => by
    intro h
    have : (toString n).toNat? = some n := Nat.toNat?_repr n
    simp_all [pathOf]
  | .capture _ .string :: _, (_, _), ⟨_, _⟩, _ => by
    simp_all [pathOf, unlinkable]

private theorem pathOf_head_ne_dot : ∀ (segs : List PathSeg) (args : Args segs),
    Linkable segs args → (pathOf segs args).head? ≠ some "."
  | [], _, _ => by simp [pathOf]
  | .lit s h :: _, _, _ => by
    simp only [pathOf, List.head?_cons, ne_eq, Option.some.injEq]
    rintro rfl
    simp [dotSegment] at h
  | .capture _ .nat :: _, (n, _), _ => by
    simp only [pathOf, List.head?_cons, ne_eq, Option.some.injEq]
    intro h
    have := toUTF8_repr n 46 (by rw [show toString n = "." from h]; decide)
    simp at this
  | .capture _ .string :: _, (_, _), ⟨hs, _⟩ => by
    simp only [pathOf, List.head?_cons, ne_eq, Option.some.injEq]
    rintro rfl
    simp [unlinkable, dotSegment] at hs

/-- A request for a link that `linkFor` builds reaches the route's handler with the values passed to
`linkFor`. The route `[.lit ""]` is left out because its link `/` reads back as `[]`. -/
theorem requestSegments_linkFor (hr : ReadsBack) (segs : List PathSeg)
    (h : HandlerType segs r) (args : Args segs) (hl : Linkable segs args)
    (hn : ∀ h, segs ≠ [.lit "" h]) (hfits : fits (pathOf segs args)) :
    (requestSegments (applyLink segs (linkFor segs) args)).bind (dispatch segs h) =
      some (applyHandler segs h args) := by
  rw [applyLink_linkFor,
    requestSegments_joinEncoded hr _ (pathOf_ne_singleton_empty segs args hl hn)
      (fun h => pathOf_head_ne_dot segs args hl (by
        match hp : pathOf segs args, h with
        | _ :: _ :: _, h => simp_all)) hfits,
    Option.bind_some, dispatch_pathOf segs h args hl]

end Routing

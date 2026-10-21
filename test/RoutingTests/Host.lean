/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Router
import RoutingTests.RoundTrip

/-!
Links and slash redirects stay on the host that served the page, including under a route whose
first segment is empty (#9).
-/

namespace Routing

open Std Async
open Std Http Server

/-- The host that `ref` points to from a page on host `base`: RFC 3986 §5.2.2, applied as the
WHATWG URL standard applies it to an `http` URL, which first strips leading spaces and controls,
removes tabs and newlines, and reads `\` as `/`. `none` for a reference that may carry a scheme. -/
def resolvedHost (base ref : String) : Option String :=
  let cs := (ref.toList.dropWhile (·.toNat ≤ 0x20)).filterMap fun c =>
    if c == '\t' || c == '\n' || c == '\r' then none else some (if c == '\\' then '/' else c)
  let ends (c : Char) := c == '/' || c == '?' || c == '#'
  match cs with
  | '/' :: '/' :: rest => some (String.ofList (rest.takeWhile (!ends ·)))
  | _ => if (cs.takeWhile (!ends ·)).contains ':' then none else some base

private def base : String := "app.example"

private def keepsHost (ref : String) : Bool :=
  resolvedHost base ref == some base

-- The model finds a host where a browser does.
#guard resolvedHost base "//evil.example/x" = some "evil.example"
#guard resolvedHost base "/\\evil.example" = some "evil.example"
#guard resolvedHost base "/\t/evil.example" = some "evil.example"
#guard resolvedHost base "https://evil.example" = none
#guard keepsHost "/.//evil.example" && keepsHost ".//evil.example" && keepsHost "/?x"

#guard linkFor [.lit "", .capture "s" .string] "evil.example" = "/.//evil.example"
#guard linkFor [.lit ""] = "/"
#guard mountLink ["", "admin"] = "/.//admin" && mountLink [""] = "/"

/-! ## Proof

Once a reference starts with `/`, `resolvedHost` reads only its next character, and an encoded
segment never starts with one a browser reads as a separator or removes. -/

/-- The characters a browser reads as `/`, or removes, right after a link's leading `/`. -/
private def opensHost (c : Char) : Bool :=
  c == '/' || c == '\\' || c == '\t' || c == '\n' || c == '\r'

private theorem resolvedHost_of_toList (b s : String) (cs : List Char) (h : s.toList = '/' :: cs)
    (hc : ∀ c rest, cs = c :: rest → opensHost c = false) : resolvedHost b s = some b := by
  unfold resolvedHost
  rw [h]
  cases cs with
  | nil => simp
  | cons c rest =>
    have hc := hc c rest rfl
    simp only [opensHost, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hc
    simp [List.dropWhile, List.filterMap, hc]

private theorem opensHost_byte : ∀ n, n < 256 → opensHost (Char.ofNat n) = true →
    URI.isEncodedChar Internal.Char.isPChar (UInt8.ofNat n) = false := by
  decide +kernel

private theorem encoded_head (e : URI.EncodedSegment) (c : Char) (cs : List Char)
    (h : (toString e).toList = c :: cs) : opensHost c = false := by
  cases hcase : opensHost c
  · rfl
  · exfalso
    have hc1 : c.utf8Size = 1 := by
      simp only [opensHost, Bool.or_eq_true, beq_iff_eq] at hcase
      rcases hcase with (((h | h) | h) | h) | h <;> subst h <;> decide
    have hb := String.utf8Encode_toList (b := toString e)
    rw [h, List.utf8Encode_cons, List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton hc1] at hb
    have hv : e.toByteArray.data.all (URI.isEncodedChar Internal.Char.isPChar) := e.valid
    have hd : e.toByteArray.data.toList = c.val.toUInt8 :: cs.utf8Encode.data.toList := by
      rw [← show (toString e).toByteArray = e.toByteArray from rfl, ← hb]
      simp
    have hmem : c.val.toUInt8 ∈ e.toByteArray.data.toList := by rw [hd]; simp
    have hok := Array.all_eq_true_iff_forall_mem.mp hv _ (Array.mem_toList_iff.mp hmem)
    have hlt : c.toNat < 128 := by
      have := Char.utf8Size_eq_one_iff.mp hc1
      simp [UInt32.le_iff_toNat_le] at this
      omega
    have := opensHost_byte c.toNat (by omega) (by rw [Char.ofNat_toNat]; exact hcase)
    rw [show UInt8.ofNat c.toNat = c.val.toUInt8 from rfl] at this
    simp_all

private theorem resolvedHost_encodedPath (b : String) (parts : List String) (q : String)
    (hq : q = "" ∨ ∃ rest, q.toList = '?' :: rest)
    (hp : ∀ p rest c cs, parts = p :: rest → p.toList = c :: cs → opensHost c = false) :
    resolvedHost b (encodedPath parts ++ q) = some b := by
  have hq' : ∀ c rest, q.toList = c :: rest → opensHost c = false := by
    rintro c rest h
    rcases hq with rfl | ⟨r, hr⟩
    · simp at h
    · rw [hr] at h; cases h; decide
  match parts, hp with
  | [], _ => exact resolvedHost_of_toList b _ q.toList (by simp [encodedPath]) hq'
  | p :: rest, hp =>
    by_cases h0 : p = ""
    · subst h0
      cases rest with
      | nil => exact resolvedHost_of_toList b _ q.toList (by simp [encodedPath]) hq'
      | cons p' rest' =>
        refine resolvedHost_of_toList b _ ('.' :: _) (by simp [encodedPath]; rfl) ?_
        rintro c rest h; cases h; decide
    · obtain ⟨c, cs, hpc⟩ : ∃ c cs, p.toList = c :: cs := by
        cases h : p.toList with
        | nil => exact absurd (String.toList_eq_nil_iff.mp h) h0
        | cons c cs => exact ⟨c, cs, rfl⟩
      have he : encodedPath (p :: rest) = "/" ++ String.intercalate "/" (p :: rest) := by
        unfold encodedPath
        split <;> simp_all
      have hi : ∃ t, (String.intercalate "/" (p :: rest)).toList = p.toList ++ t := by
        cases rest with
        | nil => exact ⟨[], by simp⟩
        | cons p' rest' =>
          exact ⟨'/' :: (String.intercalate "/" (p' :: rest')).toList,
            by rw [String.intercalate_cons_cons]; simp⟩
      obtain ⟨t, ht⟩ := hi
      refine resolvedHost_of_toList b _ (c :: (cs ++ t ++ q.toList)) (by simp [he, ht, hpc]) ?_
      rintro c' rest' h
      cases h
      exact hp p rest c cs rfl hpc

private theorem encoded_parts (xs : List String) :
    ∀ p rest c cs, xs.map (fun x => toString (URI.EncodedSegment.encode x)) = p :: rest →
      p.toList = c :: cs → opensHost c = false := by
  intro p rest c cs h hc
  cases xs with
  | nil => simp at h
  | cons x xs =>
    simp only [List.map_cons, List.cons.injEq] at h
    exact encoded_head _ c cs (h.1 ▸ hc)

/-- A link that `linkFor` builds stays on the host of the page it is on. -/
theorem resolvedHost_linkFor (b : String) (segs : List PathSeg) (args : Args segs) :
    resolvedHost b (applyLink segs (linkFor segs) args) = some b := by
  rw [applyLink_linkFor, joinEncoded]
  simpa using resolvedHost_encodedPath b _ "" (.inl rfl) (encoded_parts _)

/-- A mount's link stays on the host of the page it is on. -/
theorem resolvedHost_mountLink (b : String) (segs : List String) :
    resolvedHost b (mountLink segs) = some b := by
  simpa [mountLink] using resolvedHost_encodedPath b _ "" (.inl rfl) (encoded_parts segs)

/-- A slash redirect stays on the host that served the request. `slashRedirect?` passes this through
`Header.Value.ofString?`, which trims ASCII whitespace; core has no lemmas about `trimAscii`, so the
redirect checks below read the header itself. -/
theorem resolvedHost_slashLocation (b : String) (target : RequestTarget) :
    resolvedHost b (slashLocation target) = some b := by
  refine resolvedHost_encodedPath b _ _ ?_ ?_
  · by_cases hq : target.query.isEmpty
    · simp [hq]
    · exact .inr ⟨_, by simp only [hq]; show (if _ then _ else "?" ++ _).toList = _; simp [hq]; rfl⟩
  · intro p rest c cs h hc
    cases hs : target.path.segments.toList with
    | nil =>
      simp only [hs, List.map_nil, List.nil_append, List.cons.injEq, List.nil_eq] at h
      rw [← h.1] at hc
      simp at hc
    | cons e es =>
      simp only [hs, List.map_cons, List.cons_append, List.cons.injEq] at h
      exact encoded_head e c cs (h.1 ▸ hc)

-- `decodedPath` drops only the `.` that a link writes.
#guard requestSegments "/.//admin" = some ["", "admin"]
#guard requestSegments "/./admin" = some [".", "admin"]
#guard requestSegments "/admin/./x" = some ["admin", ".", "x"]

private def ok (body : String) : Result := fun _ => Response.ok.text body

private def emptyRoot : MountPoint := ⟨[""], by decide⟩

private def router : Router :=
  { routes := [.mount emptyRoot
      [ .mount ⟨["admin"], by decide⟩ [.get [] (ok "admin")],
        .get [.capture "s" .string, .lit ""] ok ] ] }

private def run (target : String) : IO (Status × Option String) :=
  Async.block <| ContextAsync.run do
    let some uri := RequestTarget.parse? target
      | throw (IO.userError s!"test target {target.quote} is not a valid request target")
    let body ← Body.empty
    let response ← router.toHandler.onRequest ((Request.get uri).body body)
    return (response.line.status, (response.line.headers.get? Header.Name.location).map toString)

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

#eval show IO Unit from do
  for (target, location) in
      [("//admin", "/.//admin/"), ("//admin?q=1", "/.//admin/?q=1"),
        ("//evil.example", "/.//evil.example/")] do
    let result ← run target
    check s!"{target} should redirect to {location}, got {repr result}"
      (result == (.permanentRedirect, some location) && keepsHost location)
  -- A client that sends a link as written, without removing the `.`, reaches the same route.
  for target in ["/.//admin/", "//admin/", "/.//evil.example/"] do
    let result ← run target
    check s!"{target} should be served, got {repr result}" (result == (.ok, none))

end Routing

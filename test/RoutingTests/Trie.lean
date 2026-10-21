/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Routing.Trie

namespace Routing.Internal

open Std.Http (Method)

/-- `segs` would match `path` if each capture accepted any segment. -/
def Fits : List PathSeg → List String → Prop
  | [], [] => True
  | [], [""] => True
  | .lit s _ :: rest, p :: ps => s = p ∧ Fits rest ps
  | .capture _ _ :: rest, _ :: ps => Fits rest ps
  | _, _ => False

theorem fits_of_dispatch : ∀ (segs : List PathSeg) (h : HandlerType segs r) (path : List String),
    (dispatch segs h path).isSome → Fits segs path
  | [], _, [], _ => trivial
  | [], _, [""], _ => trivial
  | [], _, p :: q :: ps, hd => by simp [dispatch] at hd
  | [], _, [p], hd => by
    by_cases hp : p = ""
    · subst hp; trivial
    · simp [dispatch, hp] at hd
  | .lit s _ :: rest, h, [], hd => by simp [dispatch] at hd
  | .lit s _ :: rest, h, p :: ps, hd => by
    by_cases hs : s = p
    · subst hs
      simp only [dispatch, BEq.rfl, ite_true] at hd
      exact ⟨rfl, fits_of_dispatch rest h ps hd⟩
    · simp [dispatch, hs] at hd
  | .capture _ .nat :: rest, h, [], hd => by simp [dispatch] at hd
  | .capture _ .nat :: rest, h, p :: ps, hd => by
    simp only [dispatch] at hd
    cases hn : p.toNat? with
    | none => simp [hn] at hd
    | some n =>
      simp only [hn, Option.bind_some] at hd
      exact fits_of_dispatch rest (h n) ps hd
  | .capture _ .string :: rest, h, [], hd => by simp [dispatch] at hd
  | .capture _ .string :: rest, h, p :: ps, hd => by
    simp only [dispatch] at hd
    split at hd
    · simp at hd
    · exact fits_of_dispatch rest (h p) ps hd

/-- Following `segs` from `node` leads to a node where route `i` ends. -/
def Reaches (t : Trie) (node i : Nat) : List PathSeg → Prop
  | [] => i ∈ t.routes.getD node []
  | .lit s _ :: rest => ∃ child, t.lits[(node, s)]? = some child ∧ Reaches t child i rest
  | .capture _ _ :: rest => ∃ child, t.captures[node]? = some child ∧ Reaches t child i rest

theorem mem_candidates : ∀ (segs : List PathSeg) (t : Trie) (node i : Nat) (path : List String),
    Reaches t node i segs → Fits segs path → i ∈ t.candidates node path
  | [], t, node, i, [], hr, _ => by simpa [Trie.candidates, Reaches] using hr
  | [], t, node, i, [p], hr, hf => by
    by_cases hp : p = ""
    · subst hp
      simp only [Reaches] at hr
      simp [Trie.candidates, hr]
    · simp [Fits, hp] at hf
  | [], _, _, _, _ :: _ :: _, _, hf => by simp [Fits] at hf
  | .lit _ _ :: _, _, _, _, [], _, hf => by simp [Fits] at hf
  | .lit s _ :: rest, t, node, i, p :: ps, ⟨child, hc, hr⟩, ⟨hs, hf⟩ => by
    subst hs
    simp only [Trie.candidates, hc, List.mem_append]
    exact Or.inl (Or.inr (mem_candidates rest t child i ps hr hf))
  | .capture _ _ :: _, _, _, _, [], _, hf => by simp [Fits] at hf
  | .capture _ _ :: rest, t, node, i, p :: ps, ⟨child, hc, hr⟩, hf => by
    simp only [Trie.candidates, hc, List.mem_append]
    exact Or.inr (mem_candidates rest t child i ps hr hf)

theorem Trie.lits_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat) {k : Nat × String}
    {v : Nat}, t.lits[k]? = some v → (t.insert i node segs).lits[k]? = some v
  | [], _, _, _, _, _, h => h
  | .lit s _ :: rest, t, i, node, k, v, h => by
    simp only [Trie.insert]
    split
    · exact lits_insert rest t i _ h
    · rename_i hnone
      apply lits_insert rest
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i heq
        rw [eq_of_beq heq] at hnone
        simp [hnone] at h
      · exact h
  | .capture _ _ :: rest, t, i, node, k, v, h => by
    simp only [Trie.insert]
    split
    · exact lits_insert rest t i _ h
    · exact lits_insert rest _ i _ h

theorem Trie.captures_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat) {k v : Nat},
    t.captures[k]? = some v → (t.insert i node segs).captures[k]? = some v
  | [], _, _, _, _, _, h => h
  | .lit s _ :: rest, t, i, node, k, v, h => by
    simp only [Trie.insert]
    split
    · exact captures_insert rest t i _ h
    · exact captures_insert rest _ i _ h
  | .capture _ _ :: rest, t, i, node, k, v, h => by
    simp only [Trie.insert]
    split
    · exact captures_insert rest t i _ h
    · rename_i hnone
      apply captures_insert rest
      rw [Std.HashMap.getElem?_insert]
      split
      · rename_i heq
        rw [eq_of_beq heq] at hnone
        simp [hnone] at h
      · exact h

theorem Trie.routes_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat) {n j : Nat},
    j ∈ t.routes.getD n [] → j ∈ (t.insert i node segs).routes.getD n []
  | [], t, i, node, n, j, h => by
    simp only [Trie.insert, Std.HashMap.getD_alter]
    split
    · rename_i heq
      rw [eq_of_beq heq, ← Std.HashMap.getD_eq_getD_getElem?] at *
      simp [h]
    · exact h
  | .lit s _ :: rest, t, i, node, n, j, h => by
    simp only [Trie.insert]
    split
    · exact routes_insert rest t i _ h
    · exact routes_insert rest _ i _ h
  | .capture _ _ :: rest, t, i, node, n, j, h => by
    simp only [Trie.insert]
    split
    · exact routes_insert rest t i _ h
    · exact routes_insert rest _ i _ h

theorem Reaches.insert : ∀ (segs' : List PathSeg) {t : Trie} {node' j : Nat},
    Reaches t node' j segs' →
    ∀ (segs : List PathSeg) (i node : Nat), Reaches (t.insert i node segs) node' j segs'
  | [], _, _, _, h, segs, i, node => Trie.routes_insert segs _ i node h
  | .lit _ _ :: rest, _, _, _, ⟨child, hc, hr⟩, segs, i, node =>
    ⟨child, Trie.lits_insert segs _ i node hc, Reaches.insert rest hr segs i node⟩
  | .capture _ _ :: rest, _, _, _, ⟨child, hc, hr⟩, segs, i, node =>
    ⟨child, Trie.captures_insert segs _ i node hc, Reaches.insert rest hr segs i node⟩

theorem reaches_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat),
    Reaches (t.insert i node segs) node i segs
  | [], t, i, node => by simp [Trie.insert, Reaches]
  | .lit s _ :: rest, t, i, node => by
    simp only [Trie.insert]
    split
    · rename_i child hc
      exact ⟨child, Trie.lits_insert rest t i child hc, reaches_insert rest t i child⟩
    · exact ⟨t.size, Trie.lits_insert rest _ i _ (by simp), reaches_insert rest _ i _⟩
  | .capture _ _ :: rest, t, i, node => by
    simp only [Trie.insert]
    split
    · rename_i child hc
      exact ⟨child, Trie.captures_insert rest t i child hc, reaches_insert rest t i child⟩
    · exact ⟨t.size, Trie.captures_insert rest _ i _ (by simp), reaches_insert rest _ i _⟩

theorem Reaches.insertAll : ∀ (routes : List (Route result)) {t : Trie} {node j : Nat}
    {segs : List PathSeg} (i : Nat), Reaches t node j segs →
      Reaches (t.insertAll i routes) node j segs
  | [], _, _, _, _, _, h => h
  | r :: rs, _, _, _, _, i, h => Reaches.insertAll rs (i + 1) (Reaches.insert _ h r.segs i 0)

theorem reaches_insertAll : ∀ (routes : List (Route result)) (t : Trie) (i k : Nat)
    (hk : k < routes.length), Reaches (t.insertAll i routes) 0 (i + k) routes[k].segs
  | r :: rs, t, i, 0, _ => Reaches.insertAll rs (i + 1) (reaches_insert r.segs t i 0)
  | r :: rs, t, i, k + 1, hk => by
    have := reaches_insertAll rs (t.insert i 0 r.segs) (i + 1) k (by simpa using hk)
    simpa [Trie.insertAll, Nat.add_assoc, Nat.add_comm 1 k] using this

/-- On a sorted list that holds `m`, the least `k` where `f k` is `some`, `findSome?` finds it. -/
theorem findSome?_sorted {f : Nat → Option β} {b : β} {m : Nat} (hb : f m = some b)
    (hmin : ∀ j < m, f j = none) :
    ∀ {cs : List Nat}, cs.Pairwise (· ≤ ·) → m ∈ cs → cs.findSome? f = some b
  | c :: cs, hs, hm => by
    rw [List.pairwise_cons] at hs
    by_cases hc : c = m
    · subst hc
      simp [hb]
    · have hm' : m ∈ cs := by simpa [Ne.symm hc] using hm
      have hcm : c < m := Nat.lt_of_le_of_ne (hs.1 m hm') hc
      simp only [List.findSome?_cons, hmin c hcm]
      exact findSome?_sorted hb hmin hs.2 hm'

theorem findSome?_eq_range : ∀ (l : List α) (g : α → Option β),
    l.findSome? g = (List.range l.length).findSome? fun k => l[k]?.bind g
  | [], _ => rfl
  | a :: l, g => by
    rw [List.length_cons, List.range_succ_eq_map, List.findSome?_cons, List.findSome?_cons,
      List.findSome?_map, findSome?_eq_range l g]
    rfl

/-- The least `m` where `f m` is `some`, from where `findSome?` stops on `List.range n`. -/
theorem least_of_findSome?_range {f : Nat → Option β} {b : β} {n : Nat}
    (h : (List.range n).findSome? f = some b) :
    ∃ m, m < n ∧ f m = some b ∧ ∀ j < m, f j = none := by
  obtain ⟨l₁, m, l₂, hl, hb, hpre⟩ := List.findSome?_eq_some_iff.1 h
  have hsorted := List.pairwise_lt_range (n := n)
  rw [hl, List.pairwise_append, List.pairwise_cons] at hsorted
  refine ⟨m, List.mem_range.1 (hl ▸ by simp), hb, fun j hj => hpre j ?_⟩
  have hjn : j ∈ List.range n := List.mem_range.2 (by
    have := List.mem_range.1 (hl ▸ (by simp : m ∈ l₁ ++ m :: l₂))
    omega)
  rw [hl, List.mem_append, List.mem_cons] at hjn
  rcases hjn with h₁ | rfl | h₂
  · exact h₁
  · omega
  · have := hsorted.2.1.1 j h₂
    omega

theorem dispatch_of_tryMatch {r : Route result} {method : Method} {path : List String}
    (h : (r.tryMatch method path).isSome) : (dispatch r.segs r.handler path).isSome := by
  simp only [Route.tryMatch, Route.tryDispatch] at h
  split at h
  · cases hd : dispatch r.segs r.handler path <;> simp_all
  · simp at h

theorem fits_append_slash : ∀ (segs : List PathSeg) (path : List String),
    Fits segs path → path.getLast? ≠ some "" → Fits segs (path ++ [""])
  | [], [], _, _ => trivial
  | [], [p], hf, hl => by
    by_cases hp : p = ""
    · subst hp; simp at hl
    · simp [Fits, hp] at hf
  | [], _ :: _ :: _, hf, _ => by simp [Fits] at hf
  | .lit _ _ :: _, [], hf, _ => by simp [Fits] at hf
  | .lit _ _ :: rest, p :: ps, ⟨hs, hf⟩, hl =>
    ⟨hs, fits_append_slash rest ps hf (by cases ps <;> simp_all)⟩
  | .capture _ _ :: _, [], hf, _ => by simp [Fits] at hf
  | .capture _ _ :: rest, p :: ps, hf, hl =>
    fits_append_slash rest ps hf (by cases ps <;> simp_all)

theorem candidates_sorted (index : RouteIndex result) (path : List String) :
    (index.candidates path).Pairwise (· ≤ ·) :=
  (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun _ _ _ hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp (by simp)

theorem mem_candidates_of_fits (routes : List (Route result)) {k : Nat} (hk : k < routes.length)
    {path : List String} (hf : Fits routes[k].segs path) :
    k ∈ (RouteIndex.of routes).trie.candidates 0 path := by
  have hr : Reaches (RouteIndex.of routes).trie 0 k routes[k].segs := by
    simpa [RouteIndex.of] using reaches_insertAll routes {} 0 k hk
  exact mem_candidates _ _ 0 k path hr hf

/-- Trying the routes `cs` in order finds what `matchTable` finds, when `cs` is sorted and holds
every route matching `path`. -/
theorem findSome?_eq_matchTable (routes : List (Route result)) (cs : List Nat) (method : Method)
    (path : List String) (hs : cs.Pairwise (· ≤ ·))
    (hc : ∀ k (hk : k < routes.length), (routes[k].tryMatch method path).isSome → k ∈ cs) :
    (cs.findSome? fun i => (RouteIndex.of routes).routes[i]?.bind (·.tryMatch method path)) =
      Routing.matchTable routes method path := by
  have hf :
      (fun (k : Nat) => (RouteIndex.of routes).routes[k]?.bind (Route.tryMatch · method path)) =
        fun (k : Nat) => routes[k]?.bind (Route.tryMatch · method path) := by
    funext k
    simp [RouteIndex.of]
  simp only [hf]
  rw [Routing.matchTable, findSome?_eq_range routes]
  cases h : (List.range routes.length).findSome?
      fun (k : Nat) => routes[k]?.bind (Route.tryMatch · method path) with
  | none =>
    rw [List.findSome?_eq_none_iff] at h ⊢
    intro k _
    by_cases hk : k < routes.length
    · exact h k (List.mem_range.2 hk)
    · simp [List.getElem?_eq_none (Nat.le_of_not_lt hk)]
  | some b =>
    obtain ⟨m, hm, hb, hmin⟩ := least_of_findSome?_range h
    refine findSome?_sorted hb hmin hs (hc m hm ?_)
    simp only [List.getElem?_eq_getElem hm, Option.bind_some] at hb
    simp [hb]

theorem Trie.edges_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat),
    t.lits.size + t.captures.size + 1 = t.size →
    (t.insert i node segs).lits.size + (t.insert i node segs).captures.size + 1 =
      (t.insert i node segs).size
  | [], _, _, _, h => h
  | .lit s _ :: rest, t, i, node, h => by
    simp only [Trie.insert]
    split
    · exact edges_insert rest t i _ h
    · rename_i hnone
      apply edges_insert rest
      simp only [Std.HashMap.size_insert, Std.HashMap.mem_iff_isSome_getElem?, hnone,
        Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      omega
  | .capture _ _ :: rest, t, i, node, h => by
    simp only [Trie.insert]
    split
    · exact edges_insert rest t i _ h
    · rename_i hnone
      apply edges_insert rest
      simp only [Std.HashMap.size_insert, Std.HashMap.mem_iff_isSome_getElem?, hnone,
        Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      omega

theorem Trie.size_insert : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat),
    (t.insert i node segs).size ≤ t.size + segs.length
  | [], _, _, _ => by simp [Trie.insert]
  | .lit s _ :: rest, t, i, node => by
    simp only [Trie.insert, List.length_cons]
    split
    · rename_i child _
      have := size_insert rest t i child; omega
    · have := size_insert rest
        { t with lits := t.lits.insert (node, s) t.size, size := t.size + 1 } i t.size
      simp only at this; omega
  | .capture _ _ :: rest, t, i, node => by
    simp only [Trie.insert, List.length_cons]
    split
    · rename_i child _
      have := size_insert rest t i child; omega
    · have := size_insert rest
        { t with captures := t.captures.insert node t.size, size := t.size + 1 } i t.size
      simp only at this; omega

/-- `insert` adds `i` to the list of one node and changes no other list. -/
theorem Trie.routes_insert_eq : ∀ (segs : List PathSeg) (t : Trie) (i node : Nat),
    ∃ last, ∀ n, (t.insert i node segs).routes.getD n [] =
      if n = last then i :: t.routes.getD n [] else t.routes.getD n []
  | [], t, i, node => ⟨node, fun n => by
      simp only [Trie.insert, Std.HashMap.getD_alter, beq_iff_eq]
      by_cases h : n = node
      · subst h
        simp [Std.HashMap.getD_eq_getD_getElem?]
      · simp [h, Ne.symm h]⟩
  | .lit s _ :: rest, t, i, node => by
    simp only [Trie.insert]
    split
    · exact routes_insert_eq rest t i _
    · exact routes_insert_eq rest _ i _
  | .capture _ _ :: rest, t, i, node => by
    simp only [Trie.insert]
    split
    · exact routes_insert_eq rest t i _
    · exact routes_insert_eq rest _ i _

/-- The route lists hold each index below `i` once, in one list, and nothing else. -/
structure Trie.Indexed (t : Trie) (i : Nat) : Prop where
  below : ∀ n j, j ∈ t.routes.getD n [] → j < i
  present : ∀ j < i, ∃ n, j ∈ t.routes.getD n []
  nodup : ∀ n, (t.routes.getD n []).Nodup
  unique : ∀ n n' j, j ∈ t.routes.getD n [] → j ∈ t.routes.getD n' [] → n = n'

theorem Trie.Indexed.insert {t : Trie} {i : Nat} (h : t.Indexed i) (node : Nat)
    (segs : List PathSeg) : (t.insert i node segs).Indexed (i + 1) := by
  obtain ⟨last, hl⟩ := Trie.routes_insert_eq segs t i node
  refine ⟨fun n j hj => ?_, fun j hj => ?_, fun n => ?_, fun n n' j hj hj' => ?_⟩
  · rw [hl] at hj
    split at hj
    · rcases List.mem_cons.1 hj with rfl | hj
      · omega
      · have := h.below n j hj; omega
    · have := h.below n j hj; omega
  · by_cases hji : j = i
    · subst hji
      exact ⟨last, by simp [hl]⟩
    · obtain ⟨n, hn⟩ := h.present j (by omega)
      exact ⟨n, by rw [hl]; split <;> simp [hn]⟩
  · rw [hl]
    split
    · exact List.nodup_cons.2 ⟨fun hi => by have := h.below n i hi; omega, h.nodup n⟩
    · exact h.nodup n
  · rw [hl] at hj hj'
    have fresh : ∀ m, i ∉ t.routes.getD m [] := fun m hi => by have := h.below m i hi; omega
    split at hj <;> split at hj'
    · subst_vars; rfl
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact absurd hj' (fresh n')
      · exact h.unique n n' j hj hj'
    · rcases List.mem_cons.1 hj' with rfl | hj'
      · exact absurd hj (fresh n)
      · exact h.unique n n' j hj hj'
    · exact h.unique n n' j hj hj'

theorem Trie.Indexed.insertAll : ∀ (routes : List (Route result)) {t : Trie} {i : Nat},
    t.Indexed i → (t.insertAll i routes).Indexed (i + routes.length)
  | [], _, _, h => h
  | r :: rs, _, i, h => by
    have := Trie.Indexed.insertAll rs (h.insert 0 r.segs)
    simpa [Trie.insertAll, Nat.add_assoc, Nat.add_comm 1] using this

theorem Trie.edges_insertAll : ∀ (routes : List (Route result)) (t : Trie) (i : Nat),
    t.lits.size + t.captures.size + 1 = t.size →
    (t.insertAll i routes).lits.size + (t.insertAll i routes).captures.size + 1 =
      (t.insertAll i routes).size
  | [], _, _, h => h
  | r :: rs, t, i, h => edges_insertAll rs _ (i + 1) (edges_insert r.segs t i 0 h)

theorem Trie.size_insertAll : ∀ (routes : List (Route result)) (t : Trie) (i : Nat),
    (t.insertAll i routes).size ≤ t.size + (routes.map (·.segs.length)).sum
  | [], _, _ => by simp [Trie.insertAll]
  | r :: rs, t, i => by
    have h₁ := size_insertAll rs (t.insert i 0 r.segs) (i + 1)
    have h₂ := size_insert r.segs t i 0
    simp only [Trie.insertAll, List.map_cons, List.sum_cons]
    omega

end Routing.Internal

namespace Routing

open Internal
open Std.Http (Method)

/-- The trie finds the route `matchTable` finds. -/
theorem RouteIndex.matchTable_of (routes : List (Route result)) (method : Method)
    (path : List String) :
    (RouteIndex.of routes).matchTable method path = Routing.matchTable routes method path := by
  refine findSome?_eq_matchTable routes _ method path (candidates_sorted _ path) fun k hk hm => ?_
  have hf := fits_of_dispatch _ _ _ (dispatch_of_tryMatch hm)
  simp only [RouteIndex.candidates, List.mem_mergeSort]
  split
  · exact mem_candidates_of_fits routes hk hf
  · rename_i hl
    exact mem_candidates_of_fits routes hk (fits_append_slash _ _ hf (by simpa using hl))

/-- Every `RouteIndex` finds the route `matchTable` finds on its table, since `trie_eq` ties its trie
to the one `RouteIndex.of` builds. -/
theorem RouteIndex.matchTable_eq (index : RouteIndex result) (method : Method)
    (path : List String) :
    index.matchTable method path = Routing.matchTable index.routes.toList method path := by
  obtain ⟨routes, trie, h⟩ := index
  subst h
  simpa [RouteIndex.of] using RouteIndex.matchTable_of routes.toList method path

/-- The trie's memory grows with the patterns' segments. Its `size`, the number of nodes, is at most
one per segment plus the root. Each node but the root has one edge into it, and each route's index
sits in one node's list, once. -/
theorem RouteIndex.memory_of (routes : List (Route result)) :
    (RouteIndex.of routes).trie.size ≤ 1 + (routes.map (·.segs.length)).sum ∧
      (RouteIndex.of routes).trie.lits.size + (RouteIndex.of routes).trie.captures.size + 1 =
        (RouteIndex.of routes).trie.size ∧
      (RouteIndex.of routes).trie.Indexed routes.length := by
  refine ⟨?_, Trie.edges_insertAll routes {} 0 (by simp), ?_⟩
  · simpa [RouteIndex.of] using Trie.size_insertAll routes {} 0
  · simpa [RouteIndex.of] using
      Trie.Indexed.insertAll routes (t := {}) (i := 0) ⟨by simp, by simp, by simp, by simp⟩

end Routing

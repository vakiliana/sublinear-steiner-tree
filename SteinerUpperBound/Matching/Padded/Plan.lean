module

public import SteinerUpperBound.Matching.Padded.CacheFacts

@[expose] public section

/-!
# A proof-only exposure plan

The plan is used to prove the law of `Cache.extend`. The implementation does not
construct it: its only calls to `Slots.test` are those in `selectedStep`.
-/

namespace SteinerUpperBound.Matching.Padded.Plan

open SteinerLowerBound
open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E}

structure Item (S : Slots G) where
  source : Slot S.length
  reverse : Slot S.length
  edge : E

def Item.entry {S : Slots G} {Q : ℕ} (x : Item S) (r : Fin Q) : Entry S Q :=
  ⟨x.source, x.reverse, x.edge, r⟩

variable (S : Slots G) (Q : ℕ)

theorem lower_test (s : Cache S Q) {source reverse : Slot S.length} {e : E}
    (ht : S.test source = some (e, reverse)) :
    Cache.lower S Q s e =
      max (Cache.boundary S Q s source.1) (Cache.boundary S Q s reverse.1) := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete source e reverse ht
  rw [← hd, ← hr, S.place_vertex, S.place_vertex, Padded.tail_reverse, ← he]
  cases d with | mk e b => cases b <;> simp [Cache.lower, Graph.tail, Graph.head, max_comm]

noncomputable def atIndex (s : Cache S Q) (v : V) (i : ℕ) : Option (Item S) :=
  if hi : i < S.length v then
    let source : Slot S.length := ⟨v, ⟨i, hi⟩⟩
    match S.test source with
    | none => none
    | some (e, reverse) =>
      if s.assigned e = none ∧
        Cache.boundary S Q s reverse.1 ≤ Cache.boundary S Q s v then
        some ⟨source, reverse, e⟩
      else none
  else none

theorem atIndex_some (s : Cache S Q) (v : V) (i : ℕ) (x : Item S)
    (hx : atIndex S Q s v i = some x) :
    x.source.1 = v ∧ x.source.2.val = i ∧
      S.test x.source = some (x.edge, x.reverse) ∧ s.assigned x.edge = none ∧
      Cache.lower S Q s x.edge = Cache.boundary S Q s v := by
  unfold atIndex at hx
  split_ifs at hx with hi
  · cases ht : S.test ⟨v, ⟨i, hi⟩⟩ with
    | none => simp only [ht] at hx; cases hx
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      simp only [ht] at hx
      split_ifs at hx with he
      · have hxx : x = ⟨⟨v, ⟨i, hi⟩⟩, reverse, e⟩ := Option.some.inj hx |>.symm
        subst x
        refine ⟨rfl, rfl, ht, he.1, ?_⟩
        rw [lower_test S Q s ht]
        exact max_eq_left he.2

noncomputable def items (s : Cache S Q) (v : V) : List (Item S) :=
  (List.range (S.length v)).filterMap (atIndex S Q s v)

noncomputable def keys (s : Cache S Q) (v : V) : Finset E :=
  ((items S Q s v).map Item.edge).toFinset

theorem item_injective (s : Cache S Q) (v : V) (i j : ℕ) (x y : Item S)
    (hi : atIndex S Q s v i = some x) (hj : atIndex S Q s v j = some y)
    (he : x.edge = y.edge) : i = j := by
  have hx := atIndex_some S Q s v i x hi
  have hy := atIndex_some S Q s v j y hj
  have hs : x.source = y.source := S.test_unique hx.2.2.1 (he ▸ hy.2.2.1)
    (hx.1.trans hy.1.symm)
  have hh := congrArg (fun z : Slot S.length => z.2.val) hs
  exact hx.2.1.symm.trans (hh.trans hy.2.1)

theorem nodup_filterMap {A B : Type*} (xs : List A) (f : A → Option B)
    (hn : xs.Nodup)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, ∀ z, f a = some z → f b = some z → a = b) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hna := (List.nodup_cons.mp hn).1
    have ht := ih (List.nodup_cons.mp hn).2
      (fun b hb c hc => hinj b (by simp [hb]) c (by simp [hc]))
    cases ha : f a with
    | none => simpa [ha] using ht
    | some z =>
      simp only [List.filterMap_cons, ha]
      apply List.nodup_cons.mpr
      refine ⟨?_, ht⟩
      intro hz
      obtain ⟨b, hb, hfb⟩ := List.mem_filterMap.mp hz
      have he := hinj a (by simp) b (by simp [hb]) z ha hfb
      exact hna (he ▸ hb)

theorem keys_nodup (s : Cache S Q) (v : V) : ((items S Q s v).map Item.edge).Nodup := by
  rw [items, List.map_filterMap]
  apply nodup_filterMap _ _ List.nodup_range
  intro i _ j _ e hi hj
  cases hx : atIndex S Q s v i with
  | none => simp [hx] at hi
  | some x =>
    cases hy : atIndex S Q s v j with
    | none => simp [hy] at hj
    | some y =>
      simp only [hx, hy, Option.map_some, Option.some.injEq] at hi hj
      exact item_injective S Q s v i j x y hx hy (hi.trans hj.symm)

theorem key_properties (s : Cache S Q) (v : V) (e : E) (he : e ∈ keys S Q s v) :
    s.assigned e = none ∧ G.Incident e v ∧
      Cache.lower S Q s e = Cache.boundary S Q s v := by
  obtain ⟨x, hx, hxe⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
  have hp := atIndex_some S Q s v i x hi
  have hinc := (S.test_incident hp.2.2.1).1
  rw [hp.1, hxe] at hinc
  simpa only [hxe] using And.intro hp.2.2.2.1 (And.intro hinc hp.2.2.2.2)

theorem key_of_incident (s : Cache S Q) (v : V) (e : E)
    (hn : s.assigned e = none) (hi : G.Incident e v)
    (hl : Cache.lower S Q s e = Cache.boundary S Q s v) :
    e ∈ keys S Q s v := by
  let d := G.away v e
  have hde : d.1 = e := rfl
  have hd : (S.place d).1 = v := (S.place_vertex d).trans (G.tail_away hi)
  cases hplace : S.place d with
  | mk u i =>
    have huv : u = v := by simpa only [hplace] using hd
    subst u
    have ht := S.test_place d
    rw [hplace] at ht
    rw [hde] at ht
    have hb : Cache.boundary S Q s (S.place (Padded.reverse d)).1 ≤ Cache.boundary S Q s v := by
      have hlow := Cache.lower_at_endpoint S Q s e (S.place (Padded.reverse d)).1
        (by simpa only [← S.place_vertex, Padded.reverse_edge, hde] using G.tail_incident (Padded.reverse d))
      exact hlow.trans_eq hl
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨⟨⟨v, i⟩, S.place (Padded.reverse d), e⟩, ?_, rfl⟩
    apply List.mem_filterMap.mpr
    refine ⟨i.val, List.mem_range.mpr i.isLt, ?_⟩
    simp only [atIndex, i.isLt, ↓reduceDIte, ht, hn, hb, and_self, ↓reduceIte]

end SteinerUpperBound.Matching.Padded.Plan

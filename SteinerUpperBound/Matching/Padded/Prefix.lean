module

public import SteinerUpperBound.Matching.Padded.Invariant
public import SteinerUpperBound.Matching.Padded.UniformOrder

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open scoped Classical

theorem filter_threshold_lookup {A : Type*} (xs : List A) (rank : A → ℕ) (a cursor : ℕ)
    (hs : xs.Pairwise (fun x y => rank x ≤ rank y)) :
    (xs.filter (fun x => rank x < a))[cursor]? =
      (xs[cursor]?).bind (fun x => if rank x < a then some x else none) := by
  induction xs generalizing cursor with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : rank x < a
    · cases cursor with
      | zero => simp [hx]
      | succ cursor => simpa [hx] using ih cursor hs.of_cons
    · have hnone : ∀ y ∈ x :: xs, ¬ rank y < a := by
        intro y hy
        rcases List.mem_cons.mp hy with hy | hy
        · simpa only [hy] using hx
        · have hh := List.rel_of_pairwise_cons hs hy
          omega
      have hf : (x :: xs).filter (fun y => rank y < a) = [] :=
        List.filter_eq_nil_iff.mpr (by simpa only [decide_eq_true_eq] using hnone)
      rw [hf]
      cases hg : (x :: xs)[cursor]? with
      | none => simp
      | some y =>
        have hy := hnone y (List.mem_of_getElem? hg)
        simp [hy]

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

def lowEntries (s : Cache S Q) (v : V) : List (Entry S Q) :=
  (s.ready v).toList.filter (fun x => x.rank.val < boundary S Q s v)

noncomputable def probe (s : Cache S Q) (v : V) (cursor : ℕ) : Option E :=
  (((s.ready v).toList)[cursor]?).bind
    (fun x => if x.rank.val < boundary S Q s v then some x.edge else none)

theorem probe_lowEntries (s : Cache S Q) (hs : Ready S Q s) (v : V) (cursor : ℕ) :
    probe S Q s v cursor = ((lowEntries S Q s v).map Entry.edge)[cursor]? := by
  unfold probe lowEntries
  rw [List.getElem?_map, filter_threshold_lookup _ _ _ _ (hs.ordered v)]
  cases hg : ((s.ready v).toList)[cursor]? with
  | none => rfl
  | some x => by_cases hx : x.rank.val < boundary S Q s v <;> simp [hx]

theorem ready_rank_ordered [Fintype E] (s : Cache S Q) (hs : Ready S Q s)
    (ranks : E → Fin Q) (hc : Consistent S Q s ranks) (hn : Function.Injective ranks) (v : V) :
    (s.ready v).toList.Pairwise
      (fun x y => (UniformOrder.order ranks).index x.edge < (UniformOrder.order ranks).index y.edge) := by
  have hu := hs.unique v
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hu
  apply (hu.and (hs.ordered v)).imp_of_mem
  intro x y hx hy hxy
  have hxrank := hc.1 x.edge x.rank (hs.valid v x hx).2.2
  have hyrank := hc.1 y.edge y.rank (hs.valid v y hy).2.2
  have hne : x.rank.val ≠ y.rank.val := by
    intro he
    have hr : ranks x.edge = ranks y.edge := by rw [hxrank, hyrank]; exact Fin.ext he
    exact hxy.1 (hn hr)
  have hlt : ranks x.edge < ranks y.edge := by
    rw [hxrank, hyrank]
    change x.rank.val < y.rank.val
    omega
  exact (UniformOrder.order_lt ranks hn x.edge y.edge).mpr hlt

theorem lowEntries_eq [Fintype E] (s : Cache S Q) (hs : Invariant S Q s)
    (ranks : E → Fin Q) (hc : Consistent S Q s ranks) (hn : Function.Injective ranks) (v : V) :
    (lowEntries S Q s v).map Entry.edge =
      (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).filter
        (fun e => (ranks e).val < boundary S Q s v) := by
  classical
  let ρ := UniformOrder.order ranks
  let : Std.Antisymm (fun e f : E => ρ.index e < ρ.index f) :=
    ⟨fun _ _ h h' => (lt_asymm h h').elim⟩
  let : Std.Irrefl (fun e f : E => ρ.index e < ρ.index f) := ⟨fun _ => lt_irrefl _⟩
  have hl : ((lowEntries S Q s v).map Entry.edge).Pairwise (fun e f => ρ.index e < ρ.index f) :=
    List.pairwise_map.mpr ((ready_rank_ordered S Q s hs.ready ranks hc hn v).filter _)
  have hr := (G.candidates_pairwise ρ (Fintype.card E) v).filter
    (fun e => (ranks e).val < boundary S Q s v)
  apply List.Pairwise.eq_of_mem_iff hl hr
  intro e
  constructor
  · intro he
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp he
    obtain ⟨hxready, hxlow⟩ := List.mem_filter.mp hx
    have hp := hs.ready.valid v x hxready
    have hi := (S.test_incident hp.2.1).1
    rw [hp.1, hxe] at hi
    have hxrank := hc.1 x.edge x.rank hp.2.2
    refine List.mem_filter.mpr ⟨(G.mem_candidates ρ _ v e).mpr ⟨ρ.index_lt e, hi⟩, ?_⟩
    simpa only [decide_eq_true_eq, ← hxrank, hxe] using hxlow
  · intro he
    obtain ⟨hinc, hlow⟩ := List.mem_filter.mp he
    have hi := ((G.mem_candidates ρ _ v e).mp hinc).2
    have hlt : (ranks e).val < boundary S Q s v := of_decide_eq_true hlow
    have ha := hc.2 e v hi hlt
    have hm := (hs.records.complete v e).mpr ⟨by rw [ha]; exact Option.some_ne_none _, hi⟩
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hm
    have hxrank := hc.1 x.edge x.rank (hs.records.valid v x hx).2.2
    have hxlow : x.rank.val < boundary S Q s v := by
      simpa only [← hxrank, hxe] using hlt
    obtain ⟨y, hy, hye⟩ := hs.ready.covers v x hx hxlow
    have hyedge : y.edge = e := hye.trans hxe
    have hyrank := hc.1 y.edge y.rank (hs.ready.valid v y hy).2.2
    have hylow : y.rank.val < boundary S Q s v := by
      simpa only [← hyrank, hyedge] using hlt
    exact List.mem_map.mpr ⟨y, List.mem_filter.mpr ⟨hy, by simpa using hylow⟩, hyedge⟩

end Cache

end SteinerUpperBound.Matching.Padded

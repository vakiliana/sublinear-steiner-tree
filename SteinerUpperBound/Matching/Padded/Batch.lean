module

public import SteinerUpperBound.Matching.Padded.Ready

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

namespace Cache

structure Batch (s : Cache S Q) (xs : List (Entry S Q)) : Prop where
  unique : (xs.map Entry.edge).Nodup
  valid : ∀ x ∈ xs, EntryValid S Q x ∧ s.assigned x.edge = none ∧ lower S Q s x.edge ≤ x.rank.val

theorem batch_commit (s : Cache S Q) (xs : List (Entry S Q)) (hb : Batch S Q s xs)
    (hr : Records S Q s) (hy : Ready S Q s) :
    Records S Q (commit S Q s xs) ∧ Ready S Q (commit S Q s xs) := by
  classical
  induction xs generalizing s with
  | nil => exact ⟨hr, hy⟩
  | cons x xs ih =>
    have hp := hb.valid x (by simp)
    have hnd := List.nodup_cons.mp hb.unique
    let t := assign S Q s x.source x.reverse x.edge x.rank
    have ht : Batch S Q t xs := by
      refine ⟨hnd.2, ?_⟩
      intro y hmem
      have hpy := hb.valid y (by simp [hmem])
      have hne : y.edge ≠ x.edge := by
        intro he
        apply hnd.1
        exact List.mem_map.mpr ⟨y, hmem, he⟩
      refine ⟨hpy.1, ?_, hpy.2.2⟩
      simpa only [t, assign, Function.update_of_ne hne] using hpy.2.1
    exact ih t ht (assign_records S Q s hr x.rank hp.1 hp.2.1)
      (assign_ready S Q s hy x.rank hp.1 hp.2.1 hp.2.2)

end Cache

namespace Plan

theorem observations_edges (xs : List (Item S)) (obs : E → Option (Fin Q)) :
    (observations xs obs).map Entry.edge =
      (xs.map Item.edge).filter (fun e => (obs e).isSome) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases ho : obs x.edge <;> simpa [observations, ho, Item.entry] using ih

theorem observations_batch (s : Cache S Q) (xs : List (Item S)) (obs : E → Option (Fin Q))
    (hn : (xs.map Item.edge).Nodup)
    (ht : ∀ x ∈ xs, S.test x.source = some (x.edge, x.reverse) ∧ s.assigned x.edge = none)
    (hr : ∀ x ∈ xs, ∀ r, obs x.edge = some r → Cache.lower S Q s x.edge ≤ r.val) :
    Cache.Batch S Q s (observations xs obs).reverse := by
  constructor
  · simpa only [List.map_reverse, List.nodup_reverse, observations_edges] using
      hn.filter (fun e => (obs e).isSome)
  · intro x hx
    have hm : x ∈ observations xs obs := List.mem_reverse.mp hx
    obtain ⟨item, hi, he⟩ := List.mem_filterMap.mp hm
    cases ho : obs item.edge with
    | none => simp only [ho, Option.map_none] at he; cases he
    | some r =>
      have hix : item.entry r = x := Option.some.inj (by simpa only [ho, Option.map_some] using he)
      subst x
      exact ⟨(ht item hi).1, (ht item hi).2, hr item hi r ho⟩

theorem ideal_batch (s : Cache S Q) (v : V) (ranks : E → Fin Q)
    (hc : Cache.Consistent S Q s ranks) :
    Cache.Batch S Q s
      (observations (items S Q s v) (fun e => Kernel.observe S Q s v e (ranks e))).reverse := by
  have hitem (x : Item S) (hx : x ∈ items S Q s v) :
      S.test x.source = some (x.edge, x.reverse) ∧ s.assigned x.edge = none := by
    obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp hx
    have hp := atIndex_some S Q s v i x hi
    exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  apply observations_batch S Q s _ _ (keys_nodup S Q s v) hitem
  intro x hx r ho
  unfold Kernel.observe at ho
  split_ifs at ho
  · have he := Option.some.inj ho
    rw [← he]
    exact Cache.consistent_unknown_lower S Q s ranks hc x.edge (hitem x hx).2

end Plan

namespace Posterior

theorem ideal_records_ready [Fintype E] (height : ℕ) (s : Cache S Q) (v : V)
    (ranks : E → Fin Q) (hc : Cache.Consistent S Q s ranks)
    (hr : Cache.Records S Q s) (hy : Cache.Ready S Q s)
    (hlen : Fintype.card E ≤ 2 ^ height) :
    Cache.Records S Q (ideal S Q height s v ranks) ∧
      Cache.Ready S Q (ideal S Q height s v ranks) := by
  let entries := (Plan.observations (Plan.items S Q s v)
    (fun e => Kernel.observe S Q s v e (ranks e))).reverse
  let t := Cache.commit S Q s entries
  have ht := Cache.batch_commit S Q s entries (Plan.ideal_batch S Q s v ranks hc) hr hy
  have hl : (t.known v).length ≤ 2 ^ height :=
    (Cache.known_length_le S Q t ht.1 v).trans hlen
  have hh := Cache.rebuild_ready S Q height v (s.level v + 1) t ht.2 ht.1 hl
  exact ⟨⟨ht.1.unique, ht.1.valid, ht.1.complete⟩, hh⟩

end Posterior

end SteinerUpperBound.Matching.Padded

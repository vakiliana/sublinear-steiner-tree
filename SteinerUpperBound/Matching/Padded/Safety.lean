module

public import SteinerUpperBound.Matching.Padded.OracleCoupling

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

namespace Cache

theorem empty_consistent (ranks : E → Fin Q) : Consistent S Q (empty S Q) ranks := by
  constructor
  · intro e r hr
    cases hr
  · intro e v _ hr
    change (ranks e).val < 0 at hr
    omega

structure SafeAnswer (ranks : E → Fin Q) (v : V)
    (answer : Option (Entry S Q) × Cache S Q) : Prop where
  invariant : Invariant S Q answer.2
  consistent : Consistent S Q answer.2 ranks
  valid : ∀ x, answer.1 = some x →
    x.source.1 = v ∧ EntryValid S Q x ∧ ranks x.edge = x.rank

theorem idealNextLoop_safe [Fintype E] (height : ℕ) (v : V) (cursor fuel : ℕ)
    (s : Cache S Q) (ranks : E → Fin Q) (hs : Invariant S Q s)
    (hc : Consistent S Q s ranks) (hlen : Fintype.card E ≤ 2 ^ height) :
    SafeAnswer S Q ranks v (idealNextLoop S Q height v cursor fuel s ranks) := by
  induction fuel generalizing s with
  | zero => exact ⟨hs, hc, fun _ h => by cases h⟩
  | succ fuel ih =>
    rw [idealNextLoop]
    cases ha : available S Q v cursor s with
    | some x =>
      refine ⟨hs, hc, ?_⟩
      intro y hy
      have he := Option.some.inj hy
      subst y
      have hp := available_spec S Q s hs.ready v cursor x ha
      exact ⟨hp.1, hp.2.1, hc.1 x.edge x.rank hp.2.2⟩
    | none =>
      split_ifs
      · have ht := idealExtend_invariant S Q height v s ranks hs hc hlen
        exact ih _ ht.1 ht.2
      · exact ⟨hs, hc, fun _ h => by cases h⟩

theorem idealNext_safe [Fintype V] [Fintype E] (P : Parameters S)
    (v : V) (cursor : ℕ) (s : Cache S P.rankCard) (ranks : E → Fin P.rankCard)
    (hs : Invariant S P.rankCard s) (hc : Consistent S P.rankCard s ranks) :
    SafeAnswer S P.rankCard ranks v
      (idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks) := by
  unfold idealNext
  cases hp : s.prepared v with
  | true =>
    simp only [↓reduceIte]
    exact idealNextLoop_safe S P.rankCard P.sortHeight v cursor (P.rankExponent + 2)
      _ ranks (administrative_invariant S P.rankCard s hs _ _) hc
      (Parameters.copies_le_sortCapacity S P)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact idealNextLoop_safe S P.rankCard P.sortHeight v cursor (P.rankExponent + 2)
      _ ranks (administrative_invariant S P.rankCard s hs _ _) hc
      (Parameters.copies_le_sortCapacity S P)

end Cache

structure RunSafe {A : Type*} (ranks : E → Fin Q) (r : LocalRun S Q A) : Prop where
  invariant : Cache.Invariant S Q r.cache
  consistent : Cache.Consistent S Q r.cache ranks

namespace Oracle

variable [Fintype V] [Fintype E] (P : Parameters S)

theorem idealScan_safe
    (call : Entry S P.rankCard → Cache S P.rankCard → Memo E →
      (E → Fin P.rankCard) → LocalRun S P.rankCard Bool)
    (ranks : E → Fin P.rankCard)
    (hcall : ∀ x s μ, Cache.Invariant S P.rankCard s → Cache.Consistent S P.rankCard s ranks →
      RunSafe S P.rankCard ranks (call x s μ ranks))
    (v : V) (cutoff cursor fuel : ℕ) (s : Cache S P.rankCard) (μ : Memo E)
    (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks) :
    RunSafe S P.rankCard ranks (idealScan S P call v cutoff cursor fuel s μ ranks) := by
  induction fuel generalizing cursor s μ with
  | zero => exact ⟨hs, hc⟩
  | succ fuel ih =>
    rw [idealScan]
    have hn := Cache.idealNext_safe S P v cursor s ranks hs hc
    cases ha : (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).1 with
    | none => exact ⟨hn.invariant, hn.consistent⟩
    | some x =>
      dsimp only
      by_cases hk : x.rank.val < cutoff
      · simp only [hk, ↓reduceIte]
        have hr := hcall x _ μ hn.invariant hn.consistent
        cases hv : (call x
            (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
            μ ranks).value with
        | true =>
          simp only [↓reduceIte]
          exact ⟨hr.invariant, hr.consistent⟩
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have ht := ih (cursor + 1)
            (call x
              (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
              μ ranks).cache
            (call x
              (Cache.idealNext S P.rankCard P.sortHeight (P.rankExponent + 1) v cursor s ranks).2
              μ ranks).memo hr.invariant hr.consistent
          exact ⟨ht.invariant, ht.consistent⟩
      · simp only [hk, ↓reduceIte]
        exact ⟨hn.invariant, hn.consistent⟩

theorem idealEdge_safe (d : Directed E) (rank : Fin P.rankCard) (ancestors : List (Directed E))
    (s : Cache S P.rankCard) (μ : Memo E) (ranks : E → Fin P.rankCard)
    (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks) :
    RunSafe S P.rankCard ranks (idealEdge S P d rank ancestors s μ ranks) := by
  rw [idealEdge]
  cases hm : μ d with
  | some b => exact ⟨hs, hc⟩
  | none =>
    let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
        (world : E → Fin P.rankCard) =>
      if _h : x.rank.val < rank.val then
        idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
      else ⟨false, ν, t, []⟩
    have hr := idealScan_safe S P call ranks (fun x t ν ht hct => by
      dsimp only [call]
      split_ifs with h
      · exact idealEdge_safe (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν ranks ht hct
      · exact ⟨ht, hct⟩) (G.head d) rank.val 0 (P.Nstar + 1) s μ hs hc
    exact ⟨hr.invariant, hr.consistent⟩
termination_by rank.val
decreasing_by exact h

theorem idealVertex_safe (v : V) (ranks : E → Fin P.rankCard) :
    RunSafe S P.rankCard ranks (idealVertex S P v ranks) := by
  have hcall (x : Entry S P.rankCard) (s : Cache S P.rankCard) (μ : Memo E)
      (hs : Cache.Invariant S P.rankCard s) (hc : Cache.Consistent S P.rankCard s ranks) :
      RunSafe S P.rankCard ranks (idealRootCall S P v x s μ ranks) := by
    change RunSafe S P.rankCard ranks (idealEdge S P (G.away v x.edge) x.rank [] s μ ranks)
    exact idealEdge_safe S P (G.away v x.edge) x.rank [] s μ ranks hs hc
  have hr := idealScan_safe S P (idealRootCall S P v) ranks hcall
    v P.rankCard 0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
    (Cache.empty_invariant S P.rankCard P.rankCard_pos) (Cache.empty_consistent S P.rankCard ranks)
  constructor
  · rw [idealVertex_cache]
    exact hr.invariant
  · rw [idealVertex_cache]
    exact hr.consistent

end Oracle

end SteinerUpperBound.Matching.Padded

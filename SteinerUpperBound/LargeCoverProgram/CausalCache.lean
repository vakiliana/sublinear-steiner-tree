module

public import SteinerUpperBound.LargeCoverProgram.Concrete
public import SteinerUpperBound.LargeCoverProgram.Cache

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical

variable {M Q U : Type*}

theorem scores_cache_ensures (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U)
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures m bits (Mean.scores callback s labels c) (fun reply => Cache.Correct bits reply.2) := by
  induction s generalizing c with
  | zero =>
    apply Support.ensures_tick
    exact Support.ensures_pure m bits _ _ hc
  | succ s ih =>
    unfold Mean.scores
    apply Support.ensures_tick
    apply Support.ensures_bind m bits _ _ (fun reply => Cache.Correct bits reply.2) _ (hcb _ c hc)
    intro head hh
    apply Support.ensures_bind m bits _ _ (fun reply => Cache.Correct bits reply.2) _
      (ih (Fin.tail labels) head.2 hh)
    intro tail ht
    apply Support.ensures_tick
    exact Support.ensures_pure m bits _ _ ht

theorem mean_cache_ensures {k : ℕ} (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1)))
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c) (xi : ℝ) :
    Causal.Ensures m bits (Mean.program query root C s B c xi callback)
      (fun r => Cache.Correct bits r.cache) := by
  unfold Mean.program
  apply Support.ensures_bind m bits _ _ (fun r => Cache.Correct bits r.store.cache) _
    (Support.ensures_of_runs m bits _ _ (Mean.sampler_cache_correct m bits query root C s B c hc))
  intro r hr
  unfold Mean.afterSample
  apply Support.ensures_tick
  cases hl : r.labels with
  | none =>
    apply Support.ensures_tick
    exact Support.ensures_pure m bits _ _ hr
  | some labels =>
    cases hs : r.successful
    · simp only [hs, Bool.false_eq_true, ite_false]
      apply Support.ensures_tick
      exact Support.ensures_pure m bits _ _ hr
    · simp only [hs, ite_true]
      apply Support.ensures_bind m bits _ _ (fun reply => Cache.Correct bits reply.2) _
        (scores_cache_ensures m bits callback hcb s labels r.store.cache hr)
      intro reply hc'
      apply Support.ensures_tick
      exact Support.ensures_pure m bits _ _ hc'

variable {Q : Type} {n k : ℕ}

def CanonicalVOBuilderEnsures (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) : Prop :=
  ∀ D d, CanonicalVOEnsures I bits ⟨key, a, terminals, D⟩ d p.cutoff (vo D d)

theorem afterCovered_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderEnsures I bits p terminals key a vo)
    (gm gp : ℚ) (selected : Selection (Fin n)) (c : Cache Q)
    (hc : Cache.Correct bits c) (D : Vector Bool n) :
    Causal.Ensures I.weight bits (afterCovered p terminals root key a vo gm gp selected c D)
      (fun r => Cache.Correct bits r.cache) := by
  unfold afterCovered
  apply Support.ensures_tick
  apply Support.ensures_bind I.weight bits _ _ (fun r => Cache.Correct bits r.cache) _
    (mean_cache_ensures I.weight bits _
      (fun u c hc => point_cache_ensures I bits ⟨key, a, terminals, D⟩ hT hnd _ (hvo D _) u c hc)
      _ root p.meanRowCap p.meanSamples p.meanProposals c hc (p.xi : ℝ))
  intro r hr
  apply Support.ensures_tick
  exact Support.ensures_pure I.weight bits _ _ hr

theorem large_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderEnsures I bits p terminals key a vo)
    (gm gp : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits (large p terminals root key a vo gm gp c)
      (fun r => Cache.Correct bits r.cache) := by
  unfold large
  apply Support.ensures_bind I.weight bits _ _ (fun r => Cache.Correct bits r.cache) _
    (Support.ensures_of_runs I.weight bits _ _
      (fun o ho => (deletion_cache_resources I.weight bits p terminals root key a c hc o ho).1))
  intro r hr
  apply Support.ensures_tick
  cases hv : r.value with
  | none => exact Support.ensures_pure I.weight bits _ _ hr
  | some val => exact afterCovered_cache_ensures I bits p terminals root key a hT hnd vo hvo gm gp val.1 r.cache hr val.2

theorem program_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (hvo : CanonicalVOBuilderEnsures I bits p terminals key a vo)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits (program p terminals root key a vo c)
      (fun r => Cache.Correct bits r.cache) := by
  unfold program
  apply Support.ensures_bind I.weight bits _ _ (fun r => Cache.Correct bits r.store.cache) _
    (Support.ensures_of_runs I.weight bits _ _
      (Mean.sampler_cache_correct I.weight bits _ root _ _ _ c hc))
  intro r hr
  unfold afterCalibration
  apply Support.ensures_tick
  dsimp only
  cases hl : r.labels with
  | none => exact Support.ensures_pure I.weight bits _ _ hr
  | some labels =>
    cases hs : r.successful
    · simp only [hs, Bool.false_eq_true, ite_false]
      exact Support.ensures_pure I.weight bits _ _ hr
    · simp only [hs, ite_true]
      split_ifs
      · exact Support.ensures_of_runs I.weight bits _ _ (small_cache I.weight bits p terminals key a _ _ _ hr)
      · exact large_cache_ensures I bits p terminals root key a hT hnd vo hvo _ _ _ hr

theorem program_concrete_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits
      (program p terminals root key a (PortGraph.RuntimeAdapter.builder key a terminals p.cutoff) c)
      (fun r => Cache.Correct bits r.cache) :=
  program_cache_ensures I bits p terminals root key a hT hnd _
    (fun D d => concrete_builder_cache_ensures I bits ⟨key, a, terminals, D⟩ hT hnd) c hc

theorem program_concrete_cache_failure_zero (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (program p terminals root key a (PortGraph.RuntimeAdapter.builder key a terminals p.cutoff) c).evaluate
      I.weight bits (fun o => if Cache.Correct bits o.value.cache then 0 else 1) = 0 :=
  program_concrete_cache_ensures I bits p terminals root key a hT hnd c hc
    (fun r => if Cache.Correct bits r.cache then 0 else 1) (fun r hr => by simp [hr])

end SteinerUpperBound.LargeCoverProgram

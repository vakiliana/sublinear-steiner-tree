module

public import SteinerUpperBound.Covers.OracleProgramSamplerLaw

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Sampler

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q : Type*} {k : ℕ}

noncomputable def completed (b : Fin (k + 1) → Bool) (root : Fin (k + 1)) (C s B P : ℕ)
    (rows : Fin s → Fin C → Fin (k + 1)) : Observation k s :=
  ⟨some (Rejection.labels b root C s rows), fun j => Rejection.waiting b C (rows j),
    decide (Rejection.Successful b C s rows),
    P + Rejection.proposals b C s rows, B - Rejection.proposals b C s rows⟩

theorem completed_prepend (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin (s + 1) → Fin C → Fin (k + 1)) :
    Observation.prepend root (Rejection.first b C (rows 0)) (Rejection.waiting b C (rows 0))
      (completed b root C s (B - Rejection.waiting b C (rows 0))
        (P + Rejection.waiting b C (rows 0)) (Fin.tail rows)) =
      completed b root C (s + 1) B P rows := by
  have hsum : Rejection.proposals b C (s + 1) rows =
      Rejection.waiting b C (rows 0) + Rejection.proposals b C s (Fin.tail rows) :=
    Fin.sum_univ_succ _
  have hs : Rejection.Successful b C (s + 1) rows ↔
      Rejection.first b C (rows 0) ≠ none ∧ Rejection.Successful b C s (Fin.tail rows) := by
    simp only [Rejection.Successful, Fin.forall_fin_succ]
    rfl
  simp only [Observation.prepend, completed, Option.map_some]
  congr 1
  · congr 1
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl
  · cases h : Rejection.first b C (rows 0) <;>
      by_cases ht : Rejection.Successful b C s (Fin.tail rows) <;> simp [hs, h, ht]
  · rw [hsum]
    omega
  · rw [hsum]
    omega

theorem replayPool_complete (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin s → Fin C → Fin (k + 1))
    (h : Rejection.proposals b C s rows ≤ B) :
    replayPool b root C s B P rows = completed b root C s B P rows := by
  induction s generalizing B P with
  | zero =>
    simp only [replayPool, completed, Rejection.proposals, Finset.univ_eq_empty,
      Finset.sum_empty, Nat.add_zero, Nat.sub_zero]
    congr 1
    · exact congrArg some (Subsingleton.elim _ _)
    · exact Subsingleton.elim _ _
    · simp [Rejection.Successful]
  | succ s ih =>
    have hsum : Rejection.proposals b C (s + 1) rows =
        Rejection.waiting b C (rows 0) + Rejection.proposals b C s (Fin.tail rows) :=
      Fin.sum_univ_succ _
    have hh : Rejection.waiting b C (rows 0) ≤ B := by omega
    have ht : Rejection.proposals b C s (Fin.tail rows) ≤ B - Rejection.waiting b C (rows 0) := by omega
    rw [replayPool, replayRow_complete b C 0 B P (rows 0) _ _ hh]
    simp only [Nat.zero_add]
    rw [ih _ _ (Fin.tail rows) ht, completed_prepend]

theorem replayPool_abort (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin s → Fin C → Fin (k + 1))
    (h : B < Rejection.proposals b C s rows) :
    (replayPool b root C s B P rows).labels = none ∧
      (replayPool b root C s B P rows).successful = false ∧
      (replayPool b root C s B P rows).proposals = P + B := by
  induction s generalizing B P with
  | zero => simp [Rejection.proposals] at h
  | succ s ih =>
    have hsum : Rejection.proposals b C (s + 1) rows =
        Rejection.waiting b C (rows 0) + Rejection.proposals b C s (Fin.tail rows) :=
      Fin.sum_univ_succ _
    by_cases hh : B < Rejection.waiting b C (rows 0)
    · rw [replayPool, replayRow_abort b C 0 B P (rows 0) _ _ hh]
      simp [Observation.failure]
    · have hhead : Rejection.waiting b C (rows 0) ≤ B := le_of_not_gt hh
      have ht : B - Rejection.waiting b C (rows 0) < Rejection.proposals b C s (Fin.tail rows) := by omega
      rw [replayPool, replayRow_complete b C 0 B P (rows 0) _ _ hhead]
      obtain ⟨hl, hs, hp⟩ := ih (B - Rejection.waiting b C (rows 0))
        (P + Rejection.waiting b C (rows 0)) (Fin.tail rows) ht
      simp only [Observation.prepend, hl, hs, Option.map_none, Bool.and_false]
      simp only [true_and]
      rw [hp]
      omega

theorem replayPool_labels (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) :
    (replayPool b root C s B P rows).labels = (Rejection.cappedPoolTree root C s B rows).output b := by
  by_cases h : Rejection.proposals b C s rows ≤ B
  · rw [replayPool_complete b root C s B P rows h, Rejection.cappedPoolTree_output b root C s B rows h]
    rfl
  · have hh := (replayPool_abort b root C s B P rows (Nat.lt_of_not_ge h)).1
    rw [hh, Rejection.cappedPoolTree, DecisionTree.output_map]
    have hn : ((Rejection.sampleTree C s rows).truncate B).output b = none :=
      (DecisionTree.truncate_none_iff b (Rejection.sampleTree C s rows) B).mpr
        (by rw [Rejection.sampleTree_queries]; omega)
    rw [hn]
    rfl

/-- Exact output law of the capped, cached, on-demand sampler. The oracle can
be any fixed bit vector; later factory composition averages this equation
through finite-seed compilation rather than conditioning on calibration. -/
theorem program_output_evaluate (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (cache : Q → Option Bool) (hc : Cache.Correct b cache)
    (F : Option (Fin s → Fin (k + 1)) → ℝ) :
    (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
      (fun o => F o.value.labels) =
      (Rejection.poolLaw C s).expect (fun rows =>
        F ((Rejection.cappedPoolTree root C s B rows).output (fun y => b (query y)))) := by
  have h := pool_evaluate_replay m b query root C s (Store.initial cache B) hc
    (fun obs => F obs.labels)
  simpa only [program, Observation.ofRecords, Store.initial, replayPool_labels] using h

def CalibratedRecord (b : Fin (k + 1) → Bool) (s : ℕ) (ξ : ℝ) (r : Observation k s) : Prop :=
  (1 - ξ) * (Rejection.retained b).card ≤
      Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s r.proposals ξ ∧
    Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s r.proposals ξ ≤
      (Rejection.retained b).card ∧
    ((Rejection.retained b).card : ℝ) ≤
      Rejection.upperEstimate (Fintype.card (Fin (k + 1))) s r.proposals ξ ∧
    Rejection.upperEstimate (Fintype.card (Fin (k + 1))) s r.proposals ξ ≤
      (1 + ξ) * (Rejection.retained b).card

def GoodRecord (b : Fin (k + 1) → Bool) (s : ℕ) (ξ : ℝ) (r : Observation k s) : Prop :=
  r.labels ≠ none ∧ r.successful = true ∧ CalibratedRecord b s ξ r

theorem replayPool_good (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) (ξ : ℝ)
    (hB : Rejection.proposals b C s rows ≤ B) (hs : Rejection.Successful b C s rows)
    (hcal : Rejection.Calibrated b C s ξ rows) :
    GoodRecord b s ξ (replayPool b root C s B 0 rows) := by
  rw [replayPool_complete b root C s B 0 rows hB]
  refine ⟨by simp [completed], by simp [completed, hs], ?_⟩
  simpa only [CalibratedRecord, completed, Nat.zero_add, Rejection.Calibrated] using hcal

end SteinerUpperBound.Covers.OracleProgram.Sampler

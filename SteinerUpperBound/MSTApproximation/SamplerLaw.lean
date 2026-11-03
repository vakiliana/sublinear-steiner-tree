module

public import SteinerUpperBound.Covers.OracleProgramSamplerLaw
public import SteinerUpperBound.MSTApproximation.SamplingLaw

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open Covers.Rejection
open Covers.OracleProgram.Sampler

variable {k : ℕ}

noncomputable def fullObservation (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) : Observation k s :=
  ⟨some (labels b root C s rows), fun j => waiting b C (rows j), decide (Successful b C s rows),
    P + proposals b C s rows, B - proposals b C s rows⟩

theorem replayPool_full (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B P : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) (hbudget : s * C ≤ B) :
    replayPool b root C s B P rows = fullObservation b root C s B P rows := by
  induction s generalizing B P with
  | zero =>
    simp only [replayPool, fullObservation, proposals, Fin.sum_univ_zero, Nat.add_zero,
      Nat.sub_zero, Successful, Fin.forall_fin_zero, decide_true]
    congr 1
    · apply congrArg some
      funext j
      exact Fin.elim0 j
    · funext j
      exact Fin.elim0 j
  | succ s ih =>
    have hw := waiting_le b C (rows 0)
    have hwB : waiting b C (rows 0) ≤ B := by nlinarith
    rw [replayPool, replayRow_complete b C 0 B P (rows 0) _ _ hwB]
    have hnext : s * C ≤ B - waiting b C (rows 0) := by
      have hsum : s * C + waiting b C (rows 0) ≤ B := by nlinarith
      omega
    rw [ih (B - waiting b C (rows 0)) (P + waiting b C (rows 0)) (Fin.tail rows) hnext]
    simp only [fullObservation, Observation.prepend, Option.map_some, Nat.zero_add]
    have hlabels : labels b root C (s + 1) rows =
        Fin.cons ((first b C (rows 0)).getD root) (labels b root C s (Fin.tail rows)) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    have htimes : (fun j => waiting b C (rows j)) =
        Fin.cons (waiting b C (rows 0)) (fun j => waiting b C (Fin.tail rows j)) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j <;> rfl
    have hp : proposals b C (s + 1) rows =
        waiting b C (rows 0) + proposals b C s (Fin.tail rows) := by
      unfold proposals
      rw [Fin.sum_univ_succ]
      rfl
    have hs : Successful b C (s + 1) rows ↔
        first b C (rows 0) ≠ none ∧ Successful b C s (Fin.tail rows) := by
      simp only [Successful, Fin.forall_fin_succ, Fin.tail]
    rw [hlabels, htimes, hp]
    congr 1
    · cases h : first b C (rows 0) <;> simp [h, hs]
    · omega
    · omega

theorem sampler_observation_law {M Q : Type*} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s : ℕ) (cache : Cache Q)
    (hc : Cache.Correct b cache) (F : Observation k s → ℝ) :
    (Covers.OracleProgram.Sampler.program query root C s (s * C) cache : Code M Q (Records Q k s)).evaluate
      m b (fun o => F (Observation.ofRecords o.value)) =
        (poolLaw C s).expect (fun rows =>
          F (fullObservation (fun y => b (query y)) root C s (s * C) 0 rows)) := by
  rw [Covers.OracleProgram.Sampler.program, pool_evaluate_replay m b query root C s _ hc]
  apply congrArg (poolLaw C s).expect
  funext rows
  change F (replayPool (fun y => b (query y)) root C s (s * C) 0 rows) = _
  rw [replayPool_full _ root C s (s * C) 0 rows le_rfl]

theorem first_getD_retained (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (hroot : b root = true) (C : ℕ) (row : Fin C → Fin (k + 1)) :
    b ((first b C row).getD root) = true := by
  induction C with
  | zero => exact hroot
  | succ C ih =>
    cases hb : b (row 0) with
    | true => simp [first, hb]
    | false => simpa only [first, hb, Bool.false_eq_true, ite_false] using ih (Fin.tail row)

theorem labels_retained (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (hroot : b root = true) (C s : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) (j : Fin s) :
    b (labels b root C s rows j) = true :=
  first_getD_retained b root hroot C (rows j)

end SteinerUpperBound.MSTApproximation

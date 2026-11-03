module

public import SteinerUpperBound.LargeCoverProgram.Basic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {M Q : Type*} {k : ℕ}

theorem lowerObserved_cast (k s proposals : ℕ) (xi : ℚ) :
    (lowerObserved k s proposals xi : ℝ) = Covers.Rejection.lowerEstimate k s proposals xi := by
  simp [lowerObserved, Covers.Rejection.lowerEstimate]

theorem upperObserved_cast (k s proposals : ℕ) (xi : ℚ) :
    (upperObserved k s proposals xi : ℝ) = Covers.Rejection.upperEstimate k s proposals xi := by
  simp [upperObserved, Covers.Rejection.upperEstimate]

/-- A public `s*C` proposal allowance eliminates global overrun; row failures
retain their proved exponential bound. No unknown retained size is used. -/
theorem sampler_cap_error (b : Fin (k + 1) → Bool) (hb : (Covers.Rejection.retained b).Nonempty)
    (C s B : ℕ) (hB : s * C ≤ B) :
    Mean.capError b C s B ≤ (s : ℝ) * Real.exp (-(C : ℝ) / (k + 1)) := by
  have he : {rows : Fin s → Fin C → Fin (k + 1) | B < Covers.Rejection.proposals b C s rows} = ∅ := by
    ext rows
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (Covers.Rejection.proposals_le b C s rows).trans hB
  rw [Mean.capError, he, Law.prob_empty, zero_add]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using Covers.Rejection.pool_failure_exp b hb C s

/-- Marginal calibration/abort probability for arbitrary integer budgets.
The hypotheses are numerical tests on public counts, accuracy, and caps. -/
theorem sampler_calibration_failure (m : M → ℝ) (bits : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun u => bits (query u))).Nonempty)
    (hB : s * C ≤ B) (hs : 0 < s) (xi : ℝ) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hcap : Real.exp (-(C : ℝ) / (k + 1)) ≤ xi / 8) :
    (Sampler.program query root C s B c : Code M Q _).evaluate m bits
      (fun o => if Sampler.GoodRecord (fun u => bits (query u)) s xi
        (Sampler.Observation.ofRecords o.value) then 0 else 1) ≤
      (s : ℝ) * Real.exp (-(C : ℝ) / (k + 1)) + 8 / ((xi / 4) ^ 2 * s) := by
  let bu := fun u => bits (query u)
  let Bad : Set (Fin s → Fin C → Fin (k + 1)) :=
    {rows | ¬ Covers.Rejection.Successful bu C s rows ∨ ¬ Covers.Rejection.Calibrated bu C s xi rows}
  have hsurvival : (1 - Covers.Rejection.hitRate bu) ^ C ≤ xi / 8 := by
    have he := Covers.Rejection.first_failure_exp bu hb C
    rw [Covers.Rejection.first_failure bu hb] at he
    exact he.trans (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hcap)
  have hcal := Covers.Rejection.calibration_failure bu hb C s hs xi hxi hxi1 hsurvival
  have hpoint (rows : Fin s → Fin C → Fin (k + 1)) :
      (if Sampler.GoodRecord bu s xi (Sampler.replayPool bu root C s B 0 rows) then (0 : ℝ) else 1) ≤
        if rows ∈ Bad then 1 else 0 := by
    by_cases hbad : rows ∈ Bad
    · split_ifs <;> norm_num
    · have hnot : ¬ (¬ Covers.Rejection.Successful bu C s rows ∨
          ¬ Covers.Rejection.Calibrated bu C s xi rows) := hbad
      have hgood := Sampler.replayPool_good bu root C s B rows xi
        ((Covers.Rejection.proposals_le bu C s rows).trans hB)
        (by tauto) (by tauto)
      simp [hgood, hbad]
  calc
    _ = (Covers.Rejection.poolLaw C s).expect (fun rows =>
        if Sampler.GoodRecord bu s xi (Sampler.replayPool bu root C s B 0 rows) then 0 else 1) := by
      exact Sampler.pool_evaluate_replay m bits query root C s (Sampler.Store.initial c B) hc
        (fun obs => if Sampler.GoodRecord bu s xi obs then 0 else 1)
    _ ≤ (Covers.Rejection.poolLaw C s).prob Bad := by
      rw [Law.prob_eq_expect]
      apply Law.expect_mono
      intro rows
      by_cases hg : rows ∈ Bad
      · simpa only [hg, ite_true] using hpoint rows
      · simpa only [hg, ite_false] using hpoint rows
    _ ≤ (Covers.Rejection.poolLaw C s).prob {rows | ¬ Covers.Rejection.Successful bu C s rows} +
        (Covers.Rejection.poolLaw C s).prob {rows | ¬ Covers.Rejection.Calibrated bu C s xi rows} :=
      Law.prob_union_le _ _ _
    _ ≤ _ := add_le_add (by simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      Covers.Rejection.pool_failure_exp bu hb C s) hcal

theorem calibration_values {n : ℕ} (p : Parameters) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q)
    (r : Sampler.Records Q k p.calibrationSamples)
    (hgood : Sampler.GoodRecord (fun u => bits (key (terminals.get u))) p.calibrationSamples
      (p.xi : ℝ) (Sampler.Observation.ofRecords r)) :
    let g : ℝ := (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card
    let gm : ℝ := lowerObserved (k + 1) p.calibrationSamples r.store.proposals p.xi
    let gp : ℝ := upperObserved (k + 1) p.calibrationSamples r.store.proposals p.xi
    (1 - (p.xi : ℝ)) * g ≤ gm ∧ gm ≤ g ∧ g ≤ gp ∧ gp ≤ (1 + (p.xi : ℝ)) * g := by
  have hcal := hgood.2.2
  simpa only [Sampler.CalibratedRecord, Sampler.Observation.ofRecords, Fintype.card_fin,
    lowerObserved_cast, upperObserved_cast] using hcal

end SteinerUpperBound.LargeCoverProgram

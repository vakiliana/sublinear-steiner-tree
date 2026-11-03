module

public import SteinerUpperBound.BandEstimator.Tuning

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {M Q : Type*} {k : ℕ}

theorem calibration_public (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (n : ℕ) (c : Cache Q)
    (hc : Cache.Correct b c)
    (hb : (Covers.Rejection.retained (fun y => b (query y))).Nonempty)
    (callback : Mean.Callback M Q (Fin (k + 1))) :
    let d := publicData n (Fintype.card (Fin (k + 1)))
    (Mean.program query root d.rowCap d.samples d.totalCap c (accuracy d) callback).evaluate m b
      (fun o => if Sampler.GoodRecord (fun y => b (query y)) d.samples (accuracy d)
        (Sampler.Observation.ofRecords o.value.sample) then 0 else 1) ≤
      (17 / 16 : ℝ) * EstimatorParameters.beta n := by
  dsimp only
  let d := publicData n (Fintype.card (Fin (k + 1)))
  let bu := fun y => b (query y)
  let Bad : Set (Fin d.samples → Fin d.rowCap → Fin (k + 1)) := {rows |
    d.totalCap < Covers.Rejection.proposals bu d.rowCap d.samples rows ∨
      ¬ Covers.Rejection.Successful bu d.rowCap d.samples rows ∨
      ¬ Covers.Rejection.Calibrated bu d.rowCap d.samples (accuracy d) rows}
  have hp :
      (Covers.Rejection.poolLaw d.rowCap d.samples).prob
        {rows | d.totalCap < Covers.Rejection.proposals bu d.rowCap d.samples rows} ≤
          EstimatorParameters.beta n / 2 := proposals_public bu hb n
  have hs :
      (Covers.Rejection.poolLaw d.rowCap d.samples).prob
          {rows | ¬ Covers.Rejection.Successful bu d.rowCap d.samples rows} ≤
            EstimatorParameters.beta n / 16 ∧
        (Covers.Rejection.poolLaw d.rowCap d.samples).prob
          {rows | ¬ Covers.Rejection.Calibrated bu d.rowCap d.samples (accuracy d) rows} ≤
            EstimatorParameters.beta n / 2 := sampling_public bu hb n
  have hsc :
      (Covers.Rejection.poolLaw d.rowCap d.samples).prob
        {rows | ¬ Covers.Rejection.Successful bu d.rowCap d.samples rows ∨
          ¬ Covers.Rejection.Calibrated bu d.rowCap d.samples (accuracy d) rows} ≤
          EstimatorParameters.beta n / 16 + EstimatorParameters.beta n / 2 :=
    (Law.prob_union_le _ _ _).trans (add_le_add hs.1 hs.2)
  have hbad : (Covers.Rejection.poolLaw d.rowCap d.samples).prob Bad ≤
      (17 / 16 : ℝ) * EstimatorParameters.beta n := by
    exact (Law.prob_union_le _ _ _).trans ((add_le_add hp hsc).trans (by ring_nf; rfl))
  rw [Mean.program_sample m b query root d.rowCap d.samples d.totalCap c (accuracy d) callback
    (fun r => if Sampler.GoodRecord bu d.samples (accuracy d)
      (Sampler.Observation.ofRecords r) then 0 else 1)]
  have hpoint (rows : Fin d.samples → Fin d.rowCap → Fin (k + 1)) :
      (if Sampler.GoodRecord bu d.samples (accuracy d)
        (Sampler.replayPool bu root d.rowCap d.samples d.totalCap 0 rows) then (0 : ℝ) else 1) ≤
          if rows ∈ Bad then 1 else 0 := by
    by_cases h : rows ∈ Bad
    · split_ifs <;> norm_num
    · have hnot : ¬ (d.totalCap < Covers.Rejection.proposals bu d.rowCap d.samples rows ∨
          ¬ Covers.Rejection.Successful bu d.rowCap d.samples rows ∨
          ¬ Covers.Rejection.Calibrated bu d.rowCap d.samples (accuracy d) rows) := h
      have hB := le_of_not_gt (fun h => hnot (Or.inl h))
      have hsuccess : Covers.Rejection.Successful bu d.rowCap d.samples rows :=
        by_contra (fun hn => hnot (Or.inr (Or.inl hn)))
      have hcal : Covers.Rejection.Calibrated bu d.rowCap d.samples (accuracy d) rows :=
        by_contra (fun hn => hnot (Or.inr (Or.inr hn)))
      have hg := Sampler.replayPool_good bu root d.rowCap d.samples d.totalCap rows
        (accuracy d) hB hsuccess hcal
      simp [h, hg]
  calc
    _ = (Covers.Rejection.poolLaw d.rowCap d.samples).expect
        (fun rows => if Sampler.GoodRecord bu d.samples (accuracy d)
          (Sampler.replayPool bu root d.rowCap d.samples d.totalCap 0 rows) then 0 else 1) := by
      convert Sampler.pool_evaluate_replay m b query root d.rowCap d.samples
        (Sampler.Store.initial c d.totalCap) hc
        (fun obs => if Sampler.GoodRecord bu d.samples (accuracy d) obs then (0 : ℝ) else 1)
          using 1 <;> congr 1
    _ ≤ (Covers.Rejection.poolLaw d.rowCap d.samples).prob Bad := by
      rw [Law.prob_eq_expect]
      apply Law.expect_mono
      intro rows
      by_cases hg : Sampler.GoodRecord bu d.samples (accuracy d)
          (Sampler.replayPool bu root d.rowCap d.samples d.totalCap 0 rows) <;>
        by_cases he : rows ∈ Bad <;> simpa only [hg, he, ite_true, ite_false] using hpoint rows
    _ ≤ _ := hbad

variable {A : Type*} [Fintype A]

theorem lowerCount_public {callback : Mean.Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : Mean.KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (n : ℕ) (c : Cache Q)
    (hc : Cache.Correct b c)
    (hb : (Covers.Rejection.retained (fun y => b (query y))).Nonempty)
    (hf₀ : ∀ u a, 0 ≤ score u a) (hf₁ : ∀ u a, score u a ≤ 1) :
    let d := publicData n (Fintype.card (Fin (k + 1)))
    let μ := Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => b (query y)) hb) kernel
    let g : ℝ := (Covers.Rejection.retained (fun y => b (query y))).card
    (Mean.program query root d.rowCap d.samples d.totalCap c (accuracy d) callback).probability m b
      {o | ¬ Mean.CorrectLower g (μ.expect (fun p => score p.1 p.2)) (accuracy d) o.value} ≤
        3 * EstimatorParameters.beta n := by
  dsimp only
  let d := publicData n (Fintype.card (Fin (k + 1)))
  let ξ := accuracy d
  let β := EstimatorParameters.beta n
  let μ := Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => b (query y)) hb) kernel
  let f := fun p : Fin (k + 1) × A => score p.1 p.2
  let g : ℝ := (Covers.Rejection.retained (fun y => b (query y))).card
  let p := Mean.program query root d.rowCap d.samples d.totalCap c ξ callback
  have hξ := accuracy_bounds n (Fintype.card (Fin (k + 1)))
  have hbudget : 1 ≤ β * ((d.samples : ℝ) * ξ ^ 2) := by
    rw [samples_budget]
    norm_num
  have hm := ScoreSampling.mean_bounds μ f (fun p => hf₀ p.1 p.2) (fun p => hf₁ p.1 p.2)
  have hmean := Mean.program_confidence h query root d.rowCap d.samples d.totalCap c hc hb
    ξ ξ β hf₀ hf₁ (samples_positive n _) hξ.1 hbudget
  have hcap : Mean.capError (fun y => b (query y)) d.rowCap d.samples d.totalCap ≤ (9 / 16 : ℝ) * β :=
    capError_public (fun y => b (query y)) hb n
  have hcal := calibration_public m b query root n c hc hb callback
  have hbound :
      p.probability m b {o | ¬ Mean.CorrectLower g (μ.expect f) ξ o.value} ≤
        p.evaluate m b (fun o => if Sampler.GoodRecord (fun y => b (query y)) d.samples ξ
          (Sampler.Observation.ofRecords o.value.sample) then 0 else 1) +
        p.probability m b {o | Mean.BadMean (μ.expect f) ξ o.value.value} := by
    unfold Code.probability
    rw [← Code.evaluate_add]
    apply Mean.evaluate_mono_runs
    intro o ho
    by_cases hg : Sampler.GoodRecord (fun y => b (query y)) d.samples ξ
        (Sampler.Observation.ofRecords o.value.sample)
    · by_cases he : Mean.BadMean (μ.expect f) ξ o.value.value
      · by_cases hl : Mean.CorrectLower g (μ.expect f) ξ o.value <;> simp [hg, he, hl]
      · have hlower := (Mean.program_fields m b query root d.rowCap d.samples d.totalCap c ξ callback o ho).1
        have hl := Mean.lowerCount_of_good (fun y => b (query y)) (μ.expect f) ξ o.value
          hg hlower hm.1 hm.2 hξ.1.le hξ.2 he
        simp [hg, he, hl, g]
    · by_cases he : Mean.BadMean (μ.expect f) ξ o.value.value <;>
        by_cases hl : Mean.CorrectLower g (μ.expect f) ξ o.value <;> simp [hg, he, hl]
  apply hbound.trans
  have hβ : 0 ≤ β := (EstimatorParameters.beta_bounds n).1.le
  linarith

end SteinerUpperBound.BandEstimator

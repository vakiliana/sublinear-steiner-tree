module

public import SteinerUpperBound.Covers.OracleProgramMeanSampling

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q A : Type*} [Fintype A]

def BadMean (mean accuracy : ℝ) (value : Option ℝ) : Prop :=
  value.elim True (fun z => accuracy < |z - mean|)

theorem program_confidence {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Rejection.retained (fun y => b (query y))).Nonempty) (ξ accuracy δ : ℝ)
    (hf₀ : ∀ u a, 0 ≤ score u a) (hf₁ : ∀ u a, score u a ≤ 1)
    (hs : 0 < s) (ha : 0 < accuracy) (hbudget : 1 ≤ δ * ((s : ℝ) * accuracy ^ 2)) :
    let μ := pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel
    (program query root C s B c ξ callback).probability m b
      {o | BadMean (μ.expect (fun p => score p.1 p.2)) accuracy o.value.value} ≤
      capError (fun y => b (query y)) C s B + δ := by
  classical
  dsimp only
  let μ := pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel
  let f := fun p : Fin (k + 1) × A => score p.1 p.2
  let F : Option ℝ → ℝ := fun value => if BadMean (μ.expect f) accuracy value then 1 else 0
  have he := program_value_close h query root C s B c hc hb ξ F
    (fun z => by dsimp [F]; split_ifs <;> norm_num)
    (fun z => by dsimp [F]; split_ifs <;> norm_num)
  have hi :
      (tape μ s).expect (fun w => F (some (ScoreSampling.empirical f s w))) =
        (tape μ s).prob {w | accuracy < |ScoreSampling.empirical f s w - μ.expect f|} := by
    rw [Law.prob_eq_expect]
    rfl
  rw [hi] at he
  have ht := ScoreSampling.empirical_deviation_of_budget μ f
    (fun p => hf₀ p.1 p.2) (fun p => hf₁ p.1 p.2) s hs accuracy δ ha hbudget
  change (program query root C s B c ξ callback).evaluate m b
    (fun o => F o.value.value) ≤ _
  linarith [(abs_le.mp he).2]

theorem calibration_mean_budget (β ξ : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) :
    1 ≤ β * ((Rejection.calibrationSamples (β / 2) ξ : ℝ) * ξ ^ 2) := by
  have hpos : 0 < (β / 2) * ξ ^ 2 := by positivity
  have hs := Nat.le_ceil (256 / ((β / 2) * ξ ^ 2))
  change 256 / ((β / 2) * ξ ^ 2) ≤ (Rejection.calibrationSamples (β / 2) ξ : ℝ) at hs
  have hm := (div_le_iff₀ hpos).mp hs
  nlinarith

theorem program_confidence_budget {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (c : Cache Q)
    (hc : Cache.Correct b c) (hb : (Rejection.retained (fun y => b (query y))).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hf₀ : ∀ u a, 0 ≤ score u a) (hf₁ : ∀ u a, score u a ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    let μ := pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel
    (program query root C s B c ξ callback).probability m b
      {o | BadMean (μ.expect (fun p => score p.1 p.2)) ξ o.value.value} ≤ 2 * β := by
  dsimp only
  apply (program_confidence h query root _ _ _ c hc hb ξ ξ β hf₀ hf₁
    (Rejection.calibrationSamples_pos (β / 2) ξ (by positivity) hξ) hξ
    (calibration_mean_budget β ξ hβ hξ)).trans
  have he := capError_budget (fun y => b (query y)) hb β ξ hβ hβ1 hξ hξ1
  linarith

theorem afterSample_sample {k s : ℕ} (m : M → ℝ) (b : Q → Bool) (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s)
    (F : Sampler.Records Q k s → ℝ) :
    (afterSample ξ callback r).evaluate m b (fun o => F o.value.sample) = F r := by
  cases he : r.labels with
  | none => simp [afterSample, he, Code.evaluate, Outcome.add, Outcome.pure, finish]
  | some labels =>
    cases hs : r.successful with
    | false => simp [afterSample, he, hs, Code.evaluate, Outcome.add, Outcome.pure, finish]
    | true =>
      simp only [afterSample, he, hs, ite_true, Code.evaluate, Outcome.add]
      rw [Code.evaluate_bind]
      simp only [Code.evaluate, Outcome.add, Outcome.pure, Outcome.combine, finish,
        Code.evaluate_const]

theorem program_sample {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (ξ : ℝ) (callback : Callback M Q (Fin (k + 1)))
    (F : Sampler.Records Q k s → ℝ) :
    (program query root C s B c ξ callback).evaluate m b (fun o => F o.value.sample) =
      (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
        (fun o => F o.value) := by
  rw [program, Code.evaluate_bind]
  apply congrArg ((Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b)
  funext o
  exact afterSample_sample m b ξ callback o.value F

/-- Calibration is a separate marginal of the same execution. In particular,
this statement does not condition the iid score law on successful calibration. -/
theorem program_calibration_budget {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (c : Cache Q)
    (hc : Cache.Correct b c) (hb : (Rejection.retained (fun y => b (query y))).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (callback : Callback M Q (Fin (k + 1))) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    (program query root C s B c ξ callback).evaluate m b
      (fun o => if Sampler.GoodRecord (fun y => b (query y)) s ξ
        (Sampler.Observation.ofRecords o.value.sample) then 0 else 1) ≤ β := by
  dsimp only
  rw [program_sample m b query root _ _ _ c ξ callback
    (fun r => if Sampler.GoodRecord (fun y => b (query y))
      (Rejection.calibrationSamples (β / 2) ξ) ξ (Sampler.Observation.ofRecords r) then 0 else 1)]
  exact Sampler.program_calibration_budget m b query root c hc hb β ξ hβ hβ1 hξ hξ1

theorem afterSample_fields {k s : ℕ} (m : M → ℝ) (b : Q → Bool) (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s) :
    ∀ o, Runs m b (afterSample ξ callback r) o →
      o.value.sample = r ∧
      o.value.lower = Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s r.store.proposals ξ ∧
      o.value.upper = Rejection.upperEstimate (Fintype.card (Fin (k + 1))) s r.store.proposals ξ := by
  intro o ho
  rw [afterSample] at ho
  cases ho with
  | tick ho =>
    cases he : r.labels with
    | none =>
      simp only [he] at ho
      cases ho with
      | tick ho => cases ho; exact ⟨rfl, rfl, rfl⟩
    | some labels =>
      simp only [he] at ho
      cases hs : r.successful with
      | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at ho
        cases ho with
        | tick ho => cases ho; exact ⟨rfl, rfl, rfl⟩
      | true =>
        simp only [hs, ite_true] at ho
        obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (scores callback s labels r.store.cache) _ _ ho
        cases hz with
        | tick hz => cases hz; exact ⟨rfl, rfl, rfl⟩

theorem program_fields {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (ξ : ℝ) (callback : Callback M Q (Fin (k + 1))) :
    ∀ o, Runs m b (program query root C s B c ξ callback) o →
      o.value.lower = Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s
        o.value.sample.store.proposals ξ ∧
      o.value.upper = Rejection.upperEstimate (Fintype.card (Fin (k + 1))) s
        o.value.sample.store.proposals ξ := by
  intro o ho
  obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (Sampler.program query root C s B c) _ _ ho
  have hf := afterSample_fields m b ξ callback a.value z hz
  simpa only [Outcome.combine, hf.1] using hf.2

def CorrectLower {k s : ℕ} (g mean ξ : ℝ) (r : Result Q k s) : Prop :=
  ∃ empirical, r.value = some empirical ∧
    0 ≤ Estimation.lowerCount r.lower empirical ξ ∧
    Estimation.lowerCount r.lower empirical ξ ≤ g * mean ∧
    g * mean - Estimation.lowerCount r.lower empirical ξ ≤ 3 * ξ * g

theorem lowerCount_of_good {k s : ℕ} (b : Fin (k + 1) → Bool) (mean ξ : ℝ)
    (r : Result Q k s) (hg : Sampler.GoodRecord b s ξ (Sampler.Observation.ofRecords r.sample))
    (hlower : r.lower = Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s
      r.sample.store.proposals ξ)
    (hm : 0 ≤ mean) (hm1 : mean ≤ 1) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (he : ¬ BadMean mean ξ r.value) :
    CorrectLower ((Rejection.retained b).card : ℝ) mean ξ r := by
  cases hv : r.value with
  | none => exact (he (by simp [BadMean, hv])).elim
  | some empirical =>
    have herr : |empirical - mean| ≤ ξ := le_of_not_gt (by simpa only [BadMean, hv, Option.elim_some] using he)
    have hcal := hg.2.2
    change (1 - ξ) * (Rejection.retained b).card ≤
        Rejection.lowerEstimate (Fintype.card (Fin (k + 1))) s r.sample.store.proposals ξ ∧ _ at hcal
    refine ⟨empirical, hv, ?_⟩
    rw [hlower]
    exact Estimation.lowerCount_bounds _ _ mean empirical ξ
      (Nat.cast_nonneg _) hξ hξ1 hm hm1 hcal.1 hcal.2.1 herr

/-- The two marginal failure bounds are combined by a union bound, not by an
independence claim. On success the actual clipped lower count is honest and
loses at most `3*ξ*g`. -/
theorem program_lowerCount_budget {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (c : Cache Q)
    (hc : Cache.Correct b c) (hb : (Rejection.retained (fun y => b (query y))).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hf₀ : ∀ u a, 0 ≤ score u a) (hf₁ : ∀ u a, score u a ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    let μ := pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel
    let g : ℝ := (Rejection.retained (fun y => b (query y))).card
    (program query root C s B c ξ callback).probability m b
      {o | ¬ CorrectLower g (μ.expect (fun p => score p.1 p.2)) ξ o.value} ≤ 3 * β := by
  classical
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
  let μ := pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel
  let f := fun p : Fin (k + 1) × A => score p.1 p.2
  let g : ℝ := (Rejection.retained (fun y => b (query y))).card
  let p := program query root C s B c ξ callback
  have hm := ScoreSampling.mean_bounds μ f (fun p => hf₀ p.1 p.2) (fun p => hf₁ p.1 p.2)
  have hmean := program_confidence_budget h query root c hc hb β ξ hβ hβ1 hξ hξ1 hf₀ hf₁
  have hcal := program_calibration_budget m b query root c hc hb β ξ hβ hβ1 hξ hξ1 callback
  have hbound :
      p.probability m b {o | ¬ CorrectLower g (μ.expect f) ξ o.value} ≤
        p.evaluate m b (fun o => if Sampler.GoodRecord (fun y => b (query y)) s ξ
          (Sampler.Observation.ofRecords o.value.sample) then 0 else 1) +
        p.probability m b {o | BadMean (μ.expect f) ξ o.value.value} := by
    unfold Code.probability
    rw [← Code.evaluate_add]
    apply evaluate_mono_runs
    intro o ho
    by_cases hgood : Sampler.GoodRecord (fun y => b (query y)) s ξ
        (Sampler.Observation.ofRecords o.value.sample)
    · by_cases hbad : BadMean (μ.expect f) ξ o.value.value
      · by_cases hlow : CorrectLower g (μ.expect f) ξ o.value <;> simp [hgood, hbad, hlow]
      · have hlower := (program_fields m b query root C s B c ξ callback o ho).1
        have hlow := lowerCount_of_good (fun y => b (query y)) (μ.expect f) ξ o.value
          hgood hlower hm.1 hm.2 hξ.le hξ1 hbad
        simp [hgood, hbad, hlow, g]
    · by_cases hbad : BadMean (μ.expect f) ξ o.value.value <;>
        by_cases hlow : CorrectLower g (μ.expect f) ξ o.value <;> simp [hgood, hbad, hlow]
  exact hbound.trans (by linarith)

end SteinerUpperBound.Covers.OracleProgram.Mean

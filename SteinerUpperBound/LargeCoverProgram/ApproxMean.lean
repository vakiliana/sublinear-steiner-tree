module

public import SteinerUpperBound.Covers.OracleProgramMean
public import SteinerUpperBound.LargeCoverProgram.Support

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical BigOperators
open Covers.FiniteSampling

variable {M Q U A : Type*} [Fintype A]

/-- Per-call TV/value refinement, not a certificate for an empirical mean.
It allows an actual matching call to abort on its explicitly budgeted bad event. -/
structure ApproxKernelSpec (callback : Mean.Callback M Q U)
    (m : M → ℝ) (bits : Q → Bool) (kernel : U → Law A)
    (score : U → A → ℝ) (delta : ℝ) : Prop where
  cache_correct : ∀ u c, Cache.Correct bits c →
    Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2)
  value_law : ∀ u c, Cache.Correct bits c → ∀ F : ℝ → ℝ,
    (∀ z, 0 ≤ F z) → (∀ z, F z ≤ 1) →
    |(callback u c).evaluate m bits (fun o => F o.value.1) -
      (kernel u).expect (fun a => F (score u a))| ≤ delta

theorem evaluate_close_runs {R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (F G : Outcome R → ℝ) (delta : ℝ)
    (h : ∀ o, Runs m bits p o → |F o - G o| ≤ delta) :
    |p.evaluate m bits F - p.evaluate m bits G| ≤ delta := by
  rw [abs_le]
  have hlo := Mean.evaluate_mono_runs m bits p G (fun o => F o + delta)
    (fun o ho => by linarith [(abs_le.mp (h o ho)).1])
  have hhi := Mean.evaluate_mono_runs m bits p F (fun o => G o + delta)
    (fun o ho => by linarith [(abs_le.mp (h o ho)).2])
  rw [Code.evaluate_add, Code.evaluate_const] at hlo hhi
  constructor <;> linarith

theorem scores_value_step (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U) (s : ℕ) (labels : Fin (s + 1) → U)
    (c : Cache Q) (F : ℝ → ℝ) :
    (Mean.scores callback (s + 1) labels c).evaluate m bits (fun o => F o.value.1) =
      (callback (labels 0) c).evaluate m bits (fun o =>
        (Mean.scores callback s (Fin.tail labels) o.value.2).evaluate m bits
          (fun z => F (o.value.1 + z.value.1))) := by
  simp only [Mean.scores, Code.evaluate, Code.evaluate_bind, Outcome.add, Outcome.combine,
    Outcome.pure]

theorem scores_approx {callback : Mean.Callback M Q U}
    {m : M → ℝ} {bits : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    {delta : ℝ} (h : ApproxKernelSpec callback m bits kernel score delta) (hd : 0 ≤ delta)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct bits c)
    (F : ℝ → ℝ) (hF₀ : ∀ z, 0 ≤ F z) (hF₁ : ∀ z, F z ≤ 1) :
    |(Mean.scores callback s labels c).evaluate m bits (fun o => F o.value.1) -
      Mean.sumValue kernel score s labels F| ≤ s * delta := by
  induction s generalizing c F with
  | zero => simp [Mean.scores, Mean.sumValue, Code.evaluate, Outcome.add, Outcome.pure]
  | succ s ih =>
      rw [scores_value_step]
      let G : ℝ → ℝ := fun z =>
        Mean.sumValue kernel score s (Fin.tail labels) (fun v => F (z + v))
      have hG₀ : ∀ z, 0 ≤ G z := fun z =>
        (Mean.sumValue_bounds kernel score s (Fin.tail labels) _ (fun v => hF₀ _) (fun v => hF₁ _)).1
      have hG₁ : ∀ z, G z ≤ 1 := fun z =>
        (Mean.sumValue_bounds kernel score s (Fin.tail labels) _ (fun v => hF₀ _) (fun v => hF₁ _)).2
      have htail := Support.expect_close m bits (callback (labels 0) c)
        (fun reply => Cache.Correct bits reply.2) (h.cache_correct (labels 0) c hc)
        (fun reply => (Mean.scores callback s (Fin.tail labels) reply.2).evaluate m bits
          (fun z => F (reply.1 + z.value.1)))
        (fun reply => G reply.1) (s * delta) (by
          intro reply hr
          exact ih (Fin.tail labels) reply.2 hr
            (fun v => F (reply.1 + v)) (fun v => hF₀ _) (fun v => hF₁ _))
      dsimp only [Causal.expect] at htail
      have hhead := h.value_law (labels 0) c hc G hG₀ hG₁
      have he : Mean.sumValue kernel score (s + 1) labels F =
          (kernel (labels 0)).expect (fun a => G (score (labels 0) a)) := rfl
      rw [he]
      have ht := abs_sub_le
        ((callback (labels 0) c).evaluate m bits (fun o =>
          (Mean.scores callback s (Fin.tail labels) o.value.2).evaluate m bits
            (fun z => F (o.value.1 + z.value.1))))
        ((callback (labels 0) c).evaluate m bits (fun o => G o.value.1))
        ((kernel (labels 0)).expect (fun a => G (score (labels 0) a)))
      push_cast
      linarith

theorem afterSample_approx {k s : ℕ} {callback : Mean.Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {bits : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} {delta : ℝ}
    (h : ApproxKernelSpec callback m bits kernel score delta) (hd : 0 ≤ delta)
    (xi : ℝ) (r : Sampler.Records Q k s) (hc : Cache.Correct bits r.store.cache)
    (F : Option ℝ → ℝ) (hF₀ : ∀ z, 0 ≤ F z) (hF₁ : ∀ z, F z ≤ 1) :
    |(Mean.afterSample xi callback r).evaluate m bits (fun o => F o.value.value) -
      Mean.observedValue kernel score (Sampler.Observation.ofRecords r) F| ≤ s * delta := by
  cases hl : r.labels with
  | none =>
      simpa [Mean.afterSample, Mean.observedValue, Mean.selected, Sampler.Observation.ofRecords,
        hl, Code.evaluate, Outcome.add, Outcome.pure, Mean.finish] using
        mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hd
  | some labels =>
      cases hs : r.successful
      · simpa [Mean.afterSample, Mean.observedValue, Mean.selected, Sampler.Observation.ofRecords,
          hl, hs, Code.evaluate, Outcome.add, Outcome.pure, Mean.finish] using
          mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hd
      · simp only [Mean.afterSample, hl, hs, ite_true, Code.evaluate, Outcome.add,
          Code.evaluate_bind, Outcome.combine, Outcome.pure, Mean.finish,
          Mean.observedValue, Mean.selected, Sampler.Observation.ofRecords, Option.elim_some]
        exact scores_approx h hd s labels r.store.cache hc (fun z => F (some (z / s)))
          (fun z => hF₀ _) (fun z => hF₁ _)

theorem mean_value_close {k : ℕ} {callback : Mean.Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {bits : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} {delta : ℝ}
    (h : ApproxKernelSpec callback m bits kernel score delta) (hd : 0 ≤ delta)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun y => bits (query y))).Nonempty) (xi : ℝ)
    (F : Option ℝ → ℝ) (hF₀ : ∀ z, 0 ≤ F z) (hF₁ : ∀ z, F z ≤ 1) :
    |(Mean.program query root C s B c xi callback).evaluate m bits (fun o => F o.value.value) -
      (tape (Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) kernel) s).expect
        (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w)))| ≤
      Mean.capError (fun y => bits (query y)) C s B + s * delta := by
  let phi : Option (Fin s → Fin (k + 1)) → ℝ := fun value =>
    value.elim (F none) (fun labels =>
      Mean.sumValue kernel score s labels (fun z => F (some (z / s))))
  have hp₀ : ∀ value, 0 ≤ phi value := by
    intro v
    cases v
    · exact hF₀ _
    · exact (Mean.sumValue_bounds _ _ _ _ _ (fun z => hF₀ _) (fun z => hF₁ _)).1
  have hp₁ : ∀ value, phi value ≤ 1 := by
    intro v
    cases v
    · exact hF₁ _
    · exact (Mean.sumValue_bounds _ _ _ _ _ (fun z => hF₀ _) (fun z => hF₁ _)).2
  let sample : Code M Q (Sampler.Records Q k s) := Sampler.program query root C s B c
  have ha := evaluate_close_runs m bits sample
    (fun o => (Mean.afterSample xi callback o.value).evaluate m bits (fun z => F z.value.value))
    (fun o => Mean.observedValue kernel score (Sampler.Observation.ofRecords o.value) F)
    (s * delta) (fun o ho => afterSample_approx h hd xi o.value
      (Mean.sampler_cache_correct m bits query root C s B c hc o ho) F hF₀ hF₁)
  have he :
      sample.evaluate m bits
        (fun o => Mean.observedValue kernel score (Sampler.Observation.ofRecords o.value) F) =
      ((Covers.Rejection.poolLaw C s).map
        (Mean.cappedAccepted (fun y => bits (query y)) root C s B)).expect phi := by
    change (Sampler.pool query root C s (Sampler.Store.initial c B)).evaluate m bits
      (fun o => Mean.observedValue kernel score (Sampler.Observation.ofRecords o.value) F) = _
    rw [Sampler.pool_evaluate_replay m bits query root C s (Sampler.Store.initial c B) hc
      (fun obs => Mean.observedValue kernel score obs F),
      Law.expect_map]
    apply congrArg (Covers.Rejection.poolLaw C s).expect
    funext rows
    simp only [Mean.observedValue, Sampler.Store.initial, Mean.selected_replay, phi]
    all_goals cases Mean.cappedAccepted (fun y => bits (query y)) root C s B rows <;> rfl
  rw [he] at ha
  have ht := (Mean.cappedAccepted_uniform_close (fun y => bits (query y)) hb root C s B).expect_bound
    phi hp₀ hp₁
  have hi :
      ((tape (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) s).map some).expect phi =
      (tape (Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) kernel) s).expect
        (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w))) := by
    rw [Law.expect_map]
    exact Mean.iid_empirical_value _ kernel score s (fun z => F (some z))
  rw [hi] at ht
  rw [Mean.program, Code.evaluate_bind]
  simp only [Outcome.combine]
  have htri := abs_sub_le
    (sample.evaluate m bits
      (fun o => (Mean.afterSample xi callback o.value).evaluate m bits (fun z => F z.value.value)))
    (((Covers.Rejection.poolLaw C s).map
      (Mean.cappedAccepted (fun y => bits (query y)) root C s B)).expect phi)
    ((tape (Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) kernel) s).expect
      (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w))))
  linarith

theorem mean_confidence {k : ℕ} {callback : Mean.Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {bits : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} {delta : ℝ}
    (h : ApproxKernelSpec callback m bits kernel score delta) (hd : 0 ≤ delta)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun y => bits (query y))).Nonempty)
    (xi accuracy beta : ℝ) (hf₀ : ∀ u a, 0 ≤ score u a) (hf₁ : ∀ u a, score u a ≤ 1)
    (hs : 0 < s) (ha : 0 < accuracy) (hbudget : 1 ≤ beta * ((s : ℝ) * accuracy ^ 2)) :
    let mu := Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) kernel
    (Mean.program query root C s B c xi callback).probability m bits
      {o | Mean.BadMean (mu.expect (fun p => score p.1 p.2)) accuracy o.value.value} ≤
      Mean.capError (fun y => bits (query y)) C s B + s * delta + beta := by
  dsimp only
  let mu := Mean.pointKernel (Covers.Rejection.uniformRetained (fun y => bits (query y)) hb) kernel
  let F : Option ℝ → ℝ := fun z => if Mean.BadMean (mu.expect (fun p => score p.1 p.2)) accuracy z then 1 else 0
  have he := mean_value_close h hd query root C s B c hc hb xi F
    (fun z => by dsimp [F]; split_ifs <;> norm_num)
    (fun z => by dsimp [F]; split_ifs <;> norm_num)
  have ht := ScoreSampling.empirical_deviation_of_budget mu (fun p => score p.1 p.2)
    (fun p => hf₀ p.1 p.2) (fun p => hf₁ p.1 p.2) s hs accuracy beta ha hbudget
  rw [Law.prob_eq_expect] at ht
  change (Mean.program query root C s B c xi callback).evaluate m bits (fun o => F o.value.value) ≤ _
  change (tape mu s).expect (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w))) ≤ beta at ht
  linarith [(abs_le.mp he).2]

end SteinerUpperBound.LargeCoverProgram

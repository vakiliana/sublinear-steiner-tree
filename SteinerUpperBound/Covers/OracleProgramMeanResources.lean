module

public import SteinerUpperBound.Covers.OracleProgramMeanConfidence

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q R S U A : Type*}

theorem evaluate_const_mul (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (c : ℝ) (F : Outcome R → ℝ) :
    p.evaluate m b (fun o => c * F o) = c * p.evaluate m b F := by
  rw [← Code.compile_expect, ← Code.compile_expect]
  exact Law.expect_const_mul _ _ _

theorem work_tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (n : ℕ) :
    (Code.tick n p).evaluate m b (fun o => (o.work : ℝ)) =
      ((n + 1 : ℕ) : ℝ) + p.evaluate m b (fun o => (o.work : ℝ)) := by
  simp only [Code.evaluate, Outcome.add, Nat.cast_add, Code.evaluate_add, Code.evaluate_const]

theorem positive_tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (n : ℕ) :
    (Code.tick n p).evaluate m b (fun o => (o.positiveReplies : ℝ)) =
      p.evaluate m b (fun o => (o.positiveReplies : ℝ)) := by
  simp only [Code.evaluate, Outcome.add, Nat.zero_add]

theorem work_bind_tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (f : R → S) (n : ℕ) :
    (p.bind (fun r => .tick n (.pure (f r)))).evaluate m b (fun o => (o.work : ℝ)) =
      p.evaluate m b (fun o => (o.work : ℝ)) + ((n + 1 : ℕ) : ℝ) := by
  rw [Code.evaluate_work_bind]
  simp only [Code.evaluate, Outcome.add, Outcome.pure, Nat.add_zero,
    Code.evaluate_add, Code.evaluate_const]

theorem positive_bind_tick (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (f : R → S) (n : ℕ) :
    (p.bind (fun r => .tick n (.pure (f r)))).evaluate m b (fun o => (o.positiveReplies : ℝ)) =
      p.evaluate m b (fun o => (o.positiveReplies : ℝ)) := by
  rw [Code.evaluate_positive_bind]
  simp only [Code.evaluate, Outcome.add, Outcome.pure,
    Nat.cast_zero, add_zero]

theorem scores_work_succ (m : M → ℝ) (b : Q → Bool) (callback : Callback M Q U)
    (s : ℕ) (labels : Fin (s + 1) → U) (c : Cache Q) :
    (scores callback (s + 1) labels c).evaluate m b (fun o => (o.work : ℝ)) =
      6 + (callback (labels 0) c).evaluate m b (fun o => (o.work : ℝ) +
        (scores callback s (Fin.tail labels) o.value.2).evaluate m b (fun z => (z.work : ℝ))) := by
  rw [scores, work_tick, Code.evaluate_work_bind]
  simp_rw [work_bind_tick]
  have hf :
      (fun o : Outcome (ℝ × Cache Q) => (o.work : ℝ) +
        ((scores callback s (Fin.tail labels) o.value.2).evaluate m b (fun z => (z.work : ℝ)) +
          ((2 + 1 : ℕ) : ℝ))) =
      (fun o => (o.work : ℝ) +
        (scores callback s (Fin.tail labels) o.value.2).evaluate m b (fun z => (z.work : ℝ)) + 3) := by
    funext o
    norm_num
    ring
  rw [hf, Code.evaluate_add, Code.evaluate_const]
  norm_num
  ring

theorem scores_positive_succ (m : M → ℝ) (b : Q → Bool) (callback : Callback M Q U)
    (s : ℕ) (labels : Fin (s + 1) → U) (c : Cache Q) :
    (scores callback (s + 1) labels c).evaluate m b (fun o => (o.positiveReplies : ℝ)) =
      (callback (labels 0) c).evaluate m b (fun o => (o.positiveReplies : ℝ) +
        (scores callback s (Fin.tail labels) o.value.2).evaluate m b
          (fun z => (z.positiveReplies : ℝ))) := by
  rw [scores, positive_tick, Code.evaluate_positive_bind]
  simp_rw [positive_bind_tick]

theorem scores_expected [Fintype A] {callback : Callback M Q U}
    {m : M → ℝ} {b : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    (h : KernelSpec callback m b kernel score) (work positive : U → ℝ)
    (hw : ∀ u c, Cache.Correct b c →
      (callback u c).evaluate m b (fun o => (o.work : ℝ)) ≤ work u)
    (hp : ∀ u c, Cache.Correct b c →
      (callback u c).evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤ positive u)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct b c) :
    (scores callback s labels c).evaluate m b (fun o => (o.work : ℝ)) ≤
        6 * s + 2 + ∑ j, work (labels j) ∧
      (scores callback s labels c).evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤
        ∑ j, positive (labels j) := by
  induction s generalizing c with
  | zero => simp [scores, Code.evaluate, Outcome.add, Outcome.pure]
  | succ s ih =>
    have hw' :
        (callback (labels 0) c).evaluate m b (fun o => (o.work : ℝ) +
          (scores callback s (Fin.tail labels) o.value.2).evaluate m b (fun z => (z.work : ℝ))) ≤
        work (labels 0) + (6 * s + 2 + ∑ j, work (Fin.tail labels j)) := by
      calc
        _ ≤ (callback (labels 0) c).evaluate m b
            (fun o => (o.work : ℝ) + (6 * s + 2 + ∑ j, work (Fin.tail labels j))) := by
          apply evaluate_mono_runs
          intro o ho
          exact add_le_add le_rfl
            (ih (Fin.tail labels) o.value.2 (h.cache_correct (labels 0) c hc o ho)).1
        _ = (callback (labels 0) c).evaluate m b (fun o => (o.work : ℝ)) +
            (6 * s + 2 + ∑ j, work (Fin.tail labels j)) := by
          rw [Code.evaluate_add, Code.evaluate_const]
        _ ≤ _ := add_le_add (hw (labels 0) c hc) le_rfl
    have hp' :
        (callback (labels 0) c).evaluate m b (fun o => (o.positiveReplies : ℝ) +
          (scores callback s (Fin.tail labels) o.value.2).evaluate m b
            (fun z => (z.positiveReplies : ℝ))) ≤
        positive (labels 0) + ∑ j, positive (Fin.tail labels j) := by
      calc
        _ ≤ (callback (labels 0) c).evaluate m b
            (fun o => (o.positiveReplies : ℝ) + ∑ j, positive (Fin.tail labels j)) := by
          apply evaluate_mono_runs
          intro o ho
          exact add_le_add le_rfl
            (ih (Fin.tail labels) o.value.2 (h.cache_correct (labels 0) c hc o ho)).2
        _ = (callback (labels 0) c).evaluate m b (fun o => (o.positiveReplies : ℝ)) +
            ∑ j, positive (Fin.tail labels j) := by
          rw [Code.evaluate_add, Code.evaluate_const]
        _ ≤ _ := add_le_add (hp (labels 0) c hc) le_rfl
    rw [scores_work_succ, scores_positive_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    constructor
    · have htail : (∑ j : Fin s, work (Fin.tail labels j)) =
          ∑ j : Fin s, work (labels j.succ) := rfl
      rw [htail] at hw'
      push_cast
      linarith
    · exact hp'

theorem afterSample_work {k s : ℕ} (m : M → ℝ) (b : Q → Bool) (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s) :
    (afterSample ξ callback r).evaluate m b (fun o => (o.work : ℝ)) =
      40 + (selected (Sampler.Observation.ofRecords r)).elim 0
        (fun labels => (scores callback s labels r.store.cache).evaluate m b (fun o => (o.work : ℝ))) := by
  cases he : r.labels with
  | none => simp [afterSample, he, selected, Sampler.Observation.ofRecords, Code.evaluate, Outcome.add, Outcome.pure]
  | some labels =>
    cases hs : r.successful <;>
      simp [afterSample, he, hs, selected, Sampler.Observation.ofRecords, work_tick,
        work_bind_tick, Code.evaluate, Outcome.add, Outcome.pure, add_comm] <;> ring

theorem afterSample_positive {k s : ℕ} (m : M → ℝ) (b : Q → Bool) (ξ : ℝ)
    (callback : Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s) :
    (afterSample ξ callback r).evaluate m b (fun o => (o.positiveReplies : ℝ)) =
      (selected (Sampler.Observation.ofRecords r)).elim 0
        (fun labels => (scores callback s labels r.store.cache).evaluate m b
          (fun o => (o.positiveReplies : ℝ))) := by
  cases he : r.labels with
  | none => simp [afterSample, he, selected, Sampler.Observation.ofRecords, Code.evaluate, Outcome.add, Outcome.pure]
  | some labels =>
    cases hs : r.successful <;>
      simp [afterSample, he, hs, selected, Sampler.Observation.ofRecords, positive_tick,
        positive_bind_tick, Code.evaluate, Outcome.add, Outcome.pure]

theorem tape_sum_expect [Fintype U] (μ : Law U) (f : U → ℝ) (s : ℕ) :
    (tape μ s).expect (fun labels => ∑ j, f (labels j)) = (s : ℝ) * μ.expect f := by
  induction s with
  | zero => simp [tape]
  | succ s ih =>
    rw [expect_tape_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Law.expect_add, Law.expect_const, ih]
    push_cast
    ring

theorem sampler_expected {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (c : Cache Q) :
    (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
        (fun o => (o.work : ℝ)) ≤
        16 * ((Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
          (fun o => (o.value.store.proposals : ℝ)) + s + 1) ∧
      (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
        (fun o => (o.positiveReplies : ℝ)) ≤ s := by
  constructor
  · calc
      _ ≤ (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
          (fun o => 16 * ((o.value.store.proposals : ℝ) + s + 1)) := by
        apply evaluate_mono_runs
        intro o ho
        have hr := Sampler.pool_resources m b query root C s (Sampler.Store.initial c B) o ho
        simp only [Sampler.Store.initial, Nat.sub_zero] at hr
        exact_mod_cast hr.2.2.2.2.1
      _ = _ := by
        rw [evaluate_const_mul, Code.evaluate_add, Code.evaluate_add, Code.evaluate_const,
          Code.evaluate_const]
  · apply le_trans _ (Code.evaluate_const m b (Sampler.program query root C s B c) (s : ℝ)).le
    apply evaluate_mono_runs
    intro o ho
    have hr := Sampler.pool_resources m b query root C s (Sampler.Store.initial c B) o ho
    exact_mod_cast hr.2.2.2.1

theorem sampler_selected_expect {k : ℕ} (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (c : Cache Q)
    (hc : Cache.Correct b c) (F : Option (Fin s → Fin (k + 1)) → ℝ) :
    (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
      (fun o => F (selected (Sampler.Observation.ofRecords o.value))) =
      (Rejection.poolLaw C s).expect (fun rows =>
        F (cappedAccepted (fun y => b (query y)) root C s B rows)) := by
  have h := Sampler.pool_evaluate_replay m b query root C s (Sampler.Store.initial c B) hc
    (fun r => F (selected r))
  simpa only [Sampler.program, Sampler.Store.initial, selected_replay] using h

/-- Expected costs use the uniform-retained average of genuine per-label
callback accounts. Capped acceptance is dominated by the iid label law for
nonnegative costs, so there is no cap-error times a worst-case cost penalty. -/
theorem program_expected [Fintype A] {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (work positive : Fin (k + 1) → ℝ) (hw₀ : ∀ u, 0 ≤ work u) (hp₀ : ∀ u, 0 ≤ positive u)
    (hw : ∀ u c, Cache.Correct b c →
      (callback u c).evaluate m b (fun o => (o.work : ℝ)) ≤ work u)
    (hp : ∀ u c, Cache.Correct b c →
      (callback u c).evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤ positive u)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Rejection.retained (fun y => b (query y))).Nonempty) (ξ : ℝ) :
    let μ := Rejection.uniformRetained (fun y => b (query y)) hb
    let p := program query root C s B c ξ callback
    p.evaluate m b (fun o => (o.work : ℝ)) ≤
        64 * (p.evaluate m b (fun o => (o.value.sample.store.proposals : ℝ)) + s + 1) +
          (s : ℝ) * μ.expect work ∧
      p.evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤
        s + (s : ℝ) * μ.expect positive := by
  dsimp only
  let μ := Rejection.uniformRetained (fun y => b (query y)) hb
  let sample : Code M Q (Sampler.Records Q k s) := Sampler.program query root C s B c
  let W : (Fin s → Fin (k + 1)) → ℝ := fun labels => 6 * s + 2 + ∑ j, work (labels j)
  let P : (Fin s → Fin (k + 1)) → ℝ := fun labels => ∑ j, positive (labels j)
  have hW : ∀ labels, 0 ≤ W labels := by
    intro labels
    dsimp [W]
    exact add_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hw₀ _))
  have hP : ∀ labels, 0 ≤ P labels := fun labels => Finset.sum_nonneg (fun j _ => hp₀ _)
  have hWa (r : Sampler.Records Q k s) (hr : Cache.Correct b r.store.cache) :
      (afterSample ξ callback r).evaluate m b (fun o => (o.work : ℝ)) ≤
        40 + (selected (Sampler.Observation.ofRecords r)).elim 0 W := by
    rw [afterSample_work]
    apply add_le_add le_rfl
    cases he : selected (Sampler.Observation.ofRecords r) with
    | none => exact le_rfl
    | some labels => exact (scores_expected h work positive hw hp s labels r.store.cache hr).1
  have hPa (r : Sampler.Records Q k s) (hr : Cache.Correct b r.store.cache) :
      (afterSample ξ callback r).evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤
        (selected (Sampler.Observation.ofRecords r)).elim 0 P := by
    rw [afterSample_positive]
    cases he : selected (Sampler.Observation.ofRecords r) with
    | none => exact le_rfl
    | some labels => exact (scores_expected h work positive hw hp s labels r.store.cache hr).2
  have hWsample :
      sample.evaluate m b (fun o => (selected (Sampler.Observation.ofRecords o.value)).elim 0 W) ≤
        6 * s + 2 + (s : ℝ) * μ.expect work := by
    rw [sampler_selected_expect m b query root C s B c hc (fun value => value.elim 0 W)]
    apply (cappedAccepted_expect_le (fun y => b (query y)) hb root C s B W hW).trans_eq
    dsimp only [W]
    rw [Law.expect_add, Law.expect_const, tape_sum_expect]
  have hPsample :
      sample.evaluate m b (fun o => (selected (Sampler.Observation.ofRecords o.value)).elim 0 P) ≤
        (s : ℝ) * μ.expect positive := by
    rw [sampler_selected_expect m b query root C s B c hc (fun value => value.elim 0 P)]
    exact (cappedAccepted_expect_le (fun y => b (query y)) hb root C s B P hP).trans_eq
      (tape_sum_expect μ positive s)
  have hwork :
      (program query root C s B c ξ callback).evaluate m b (fun o => (o.work : ℝ)) ≤
        sample.evaluate m b (fun o => (o.work : ℝ)) + 40 +
          (6 * s + 2 + (s : ℝ) * μ.expect work) := by
    rw [program, Code.evaluate_work_bind]
    calc
      _ ≤ sample.evaluate m b (fun o => (o.work : ℝ) +
          (40 + (selected (Sampler.Observation.ofRecords o.value)).elim 0 W)) := by
        apply evaluate_mono_runs
        intro o ho
        exact add_le_add le_rfl (hWa o.value (sampler_cache_correct m b query root C s B c hc o ho))
      _ = sample.evaluate m b (fun o => (o.work : ℝ)) + 40 +
          sample.evaluate m b (fun o => (selected (Sampler.Observation.ofRecords o.value)).elim 0 W) := by
        rw [Code.evaluate_add, Code.evaluate_add, Code.evaluate_const]
        ring
      _ ≤ _ := add_le_add le_rfl hWsample
  have hpos :
      (program query root C s B c ξ callback).evaluate m b (fun o => (o.positiveReplies : ℝ)) ≤
        sample.evaluate m b (fun o => (o.positiveReplies : ℝ)) + (s : ℝ) * μ.expect positive := by
    rw [program, Code.evaluate_positive_bind]
    calc
      _ ≤ sample.evaluate m b (fun o => (o.positiveReplies : ℝ) +
          (selected (Sampler.Observation.ofRecords o.value)).elim 0 P) := by
        apply evaluate_mono_runs
        intro o ho
        exact add_le_add le_rfl (hPa o.value (sampler_cache_correct m b query root C s B c hc o ho))
      _ = sample.evaluate m b (fun o => (o.positiveReplies : ℝ)) +
          sample.evaluate m b (fun o => (selected (Sampler.Observation.ofRecords o.value)).elim 0 P) :=
        Code.evaluate_add m b sample _ _
      _ ≤ _ := add_le_add le_rfl hPsample
  have hsamp := sampler_expected m b query root C s B c
  constructor
  · have he := program_sample m b query root C s B c ξ callback (fun r => (r.store.proposals : ℝ))
    rw [he]
    have hn := Code.evaluate_nonneg m b sample (fun o => (Nat.cast_nonneg o.value.store.proposals : (0 : ℝ) ≤ _))
    have hsR : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith [hsamp.1]
  · exact hpos.trans (add_le_add hsamp.2 le_rfl)

end SteinerUpperBound.Covers.OracleProgram.Mean

module

public import SteinerUpperBound.Covers.OracleProgramMeanCache

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q U A : Type*} [Fintype A]

noncomputable def sumValue (kernel : U → Law A) (score : U → A → ℝ) :
    (s : ℕ) → (Fin s → U) → (ℝ → ℝ) → ℝ
  | 0, _, F => F 0
  | s + 1, labels, F => (kernel (labels 0)).expect (fun a =>
      sumValue kernel score s (Fin.tail labels) (fun z => F (score (labels 0) a + z)))

theorem sumValue_bounds (kernel : U → Law A) (score : U → A → ℝ)
    (s : ℕ) (labels : Fin s → U) (F : ℝ → ℝ)
    (hF₀ : ∀ z, 0 ≤ F z) (hF₁ : ∀ z, F z ≤ 1) :
    0 ≤ sumValue kernel score s labels F ∧ sumValue kernel score s labels F ≤ 1 := by
  induction s generalizing F with
  | zero => exact ⟨hF₀ 0, hF₁ 0⟩
  | succ s ih =>
    refine ⟨(kernel (labels 0)).expect_nonneg
      (fun a => (ih (Fin.tail labels) _ (fun z => hF₀ _) (fun z => hF₁ _)).1), ?_⟩
    · apply le_trans _ (Law.expect_const (kernel (labels 0)) 1).le
      apply Law.expect_mono
      intro a
      exact (ih (Fin.tail labels) _ (fun z => hF₀ _) (fun z => hF₁ _)).2

theorem scores_value {callback : Callback M Q U}
    {m : M → ℝ} {b : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    (h : KernelSpec callback m b kernel score) (s : ℕ) (labels : Fin s → U)
    (c : Cache Q) (hc : Cache.Correct b c) (F : ℝ × Cache Q → ℝ) (G : ℝ → ℝ)
    (hFG : ∀ z d, Cache.Correct b d → F (z, d) = G z) :
    (scores callback s labels c).evaluate m b (fun o => F o.value) =
      sumValue kernel score s labels G := by
  induction s generalizing c F G with
  | zero => exact hFG 0 c hc
  | succ s ih =>
    change ((callback (labels 0) c).bind (fun head =>
      (scores callback s (Fin.tail labels) head.2).bind (fun tail =>
        .tick 2 (.pure (head.1 + tail.1, tail.2))))).evaluate m b (fun o => F o.value) = _
    simp only [evaluate_bind_value]
    exact h.continuation (labels 0) c hc
      (fun p => (scores callback s (Fin.tail labels) p.2).evaluate m b
        (fun o => F (p.1 + o.value.1, o.value.2)))
      (fun z => sumValue kernel score s (Fin.tail labels) (fun v => G (z + v)))
      (fun z d hd => ih (Fin.tail labels) d hd
        (fun p => F (z + p.1, p.2)) (fun v => G (z + v))
        (fun v e he => hFG (z + v) e he))

noncomputable def pointKernel [Fintype U] (μ : Law U) (kernel : U → Law A) :
    Law (U × A) :=
  μ.bind (fun u => (kernel u).map (fun a => (u, a)))

theorem pointKernel_expect [Fintype U] (μ : Law U) (kernel : U → Law A)
    (F : U × A → ℝ) :
    (pointKernel μ kernel).expect F =
      μ.expect (fun u => (kernel u).expect (fun a => F (u, a))) := by
  simp only [pointKernel, Law.expect_bind, Law.expect_map]

/-- Averaging the cache-independent conditional kernels over iid labels gives
an actual iid point/kernel law. No independence of cache updates is asserted. -/
theorem iid_sumValue [Fintype U] (μ : Law U) (kernel : U → Law A)
    (score : U → A → ℝ) (s : ℕ) (F : ℝ → ℝ) :
    (tape μ s).expect (fun labels => sumValue kernel score s labels F) =
      (tape (pointKernel μ kernel) s).expect
        (fun w => F (∑ j, score (w j).1 (w j).2)) := by
  induction s generalizing F with
  | zero => simp [tape, sumValue]
  | succ s ih =>
    rw [expect_tape_succ, expect_tape_succ]
    simp only [sumValue, Fin.cons_zero, Fin.tail_cons, Fin.sum_univ_succ,
      Fin.cons_succ]
    rw [pointKernel_expect]
    apply congrArg μ.expect
    funext u
    rw [expect_comm]
    apply congrArg (kernel u).expect
    funext a
    exact ih (fun z => F (score u a + z))

theorem iid_empirical_value [Fintype U] (μ : Law U) (kernel : U → Law A)
    (score : U → A → ℝ) (s : ℕ) (F : ℝ → ℝ) :
    (tape μ s).expect (fun labels =>
      sumValue kernel score s labels (fun z => F (z / s))) =
      (tape (pointKernel μ kernel) s).expect
        (fun w => F (ScoreSampling.empirical (fun p => score p.1 p.2) s w)) :=
  iid_sumValue μ kernel score s (fun z => F (z / s))

def selected {k s : ℕ} (r : Sampler.Observation k s) : Option (Fin s → Fin (k + 1)) :=
  if r.successful then r.labels else none

noncomputable def observedValue {k s : ℕ} (kernel : Fin (k + 1) → Law A)
    (score : Fin (k + 1) → A → ℝ) (r : Sampler.Observation k s) (F : Option ℝ → ℝ) : ℝ :=
  match selected r with
  | none => F none
  | some labels => sumValue kernel score s labels (fun z => F (some (z / s)))

theorem afterSample_value {k s : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (ξ : ℝ) (r : Sampler.Records Q k s) (hc : Cache.Correct b r.store.cache)
    (F : Option ℝ → Sampler.Observation k s → ℝ) :
    (afterSample ξ callback r).evaluate m b
      (fun o => F o.value.value (Sampler.Observation.ofRecords o.value.sample)) =
      observedValue kernel score (Sampler.Observation.ofRecords r)
        (fun z => F z (Sampler.Observation.ofRecords r)) := by
  cases he : r.labels with
  | none =>
    cases hs : r.successful <;>
      simp [afterSample, he, hs, selected, observedValue, Sampler.Observation.ofRecords,
        Code.evaluate, Outcome.add, Outcome.pure, finish]
  | some labels =>
    cases hs : r.successful with
    | false =>
      simp [afterSample, he, hs, selected, observedValue, Sampler.Observation.ofRecords,
        Code.evaluate, Outcome.add, Outcome.pure, finish]
    | true =>
      simp only [afterSample, he, hs, ite_true, Code.evaluate, Outcome.add,
        finish]
      rw [Code.evaluate_bind]
      change (scores callback s labels r.store.cache).evaluate m b
        (fun o => F (some (o.value.1 / s)) (Sampler.Observation.ofRecords r)) = _
      simpa only [observedValue, selected, Sampler.Observation.ofRecords, he, hs, ite_true] using
        scores_value h s labels r.store.cache hc
          (fun z => F (some (z.1 / s)) (Sampler.Observation.ofRecords r))
          (fun z => F (some (z / s)) (Sampler.Observation.ofRecords r))
          (fun _ _ _ => rfl)

/-- Joint value/observation law, retaining calibration data without exposing
private score seeds or assuming calibration-conditioned uniformity. -/
theorem program_value {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c) (ξ : ℝ)
    (F : Option ℝ → Sampler.Observation k s → ℝ) :
    (program query root C s B c ξ callback).evaluate m b
      (fun o => F o.value.value (Sampler.Observation.ofRecords o.value.sample)) =
      (Rejection.poolLaw C s).expect (fun rows =>
        observedValue kernel score
          (Sampler.replayPool (fun y => b (query y)) root C s B 0 rows)
          (fun z => F z (Sampler.replayPool (fun y => b (query y)) root C s B 0 rows))) := by
  rw [program, Code.evaluate_bind]
  calc
    _ = (Sampler.program query root C s B c : Code M Q (Sampler.Records Q k s)).evaluate m b
        (fun o => observedValue kernel score (Sampler.Observation.ofRecords o.value)
          (fun z => F z (Sampler.Observation.ofRecords o.value))) := by
      apply evaluate_congr_runs
      intro o ho
      exact afterSample_value h ξ o.value
        (sampler_cache_correct m b query root C s B c hc o ho) F
    _ = _ := Sampler.pool_evaluate_replay m b query root C s (Sampler.Store.initial c B) hc
      (fun r => observedValue kernel score r (fun z => F z r))

end SteinerUpperBound.Covers.OracleProgram.Mean

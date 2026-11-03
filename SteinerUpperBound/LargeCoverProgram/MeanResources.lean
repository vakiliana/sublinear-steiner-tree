module

public import SteinerUpperBound.LargeCoverProgram.Cache
public import SteinerUpperBound.LargeCoverProgram.Support

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical BigOperators
open Covers.FiniteSampling

variable {M Q U : Type*}

/-- Resource composition needs only actual cache correctness, not exactness of
the score value kernel. Thus it also applies to the explicitly TV-budgeted VO. -/
theorem scores_expected_cache (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U)
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (work positive : U → ℝ)
    (hw : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (fun o => (o.work : ℝ)) ≤ work u)
    (hp : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ positive u)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct bits c) :
    (Mean.scores callback s labels c).evaluate m bits (fun o => (o.work : ℝ)) ≤
        6 * s + 2 + ∑ j, work (labels j) ∧
      (Mean.scores callback s labels c).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤
        ∑ j, positive (labels j) := by
  induction s generalizing c with
  | zero => simp [Mean.scores, Code.evaluate, Outcome.add, Outcome.pure]
  | succ s ih =>
      have hW := Support.expect_mono m bits (callback (labels 0) c)
        (fun reply => Cache.Correct bits reply.2) (hcb _ c hc)
        (fun reply => (Mean.scores callback s (Fin.tail labels) reply.2).evaluate
          m bits (fun z => (z.work : ℝ)))
        (fun _ => 6 * s + 2 + ∑ j, work (Fin.tail labels j))
        (fun reply hr => (ih (Fin.tail labels) reply.2 hr).1)
      have hP := Support.expect_mono m bits (callback (labels 0) c)
        (fun reply => Cache.Correct bits reply.2) (hcb _ c hc)
        (fun reply => (Mean.scores callback s (Fin.tail labels) reply.2).evaluate m bits
          (fun z => (z.positiveReplies : ℝ)))
        (fun _ => ∑ j, positive (Fin.tail labels j))
        (fun reply hr => (ih (Fin.tail labels) reply.2 hr).2)
      dsimp only [Causal.expect] at hW hP
      simp only [Code.evaluate_add, Code.evaluate_const] at hW hP
      rw [Mean.scores_work_succ, Mean.scores_positive_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hw₁ := hw (labels 0) c hc
      have hp₁ := hp (labels 0) c hc
      simp only [Code.evaluate_add, Fin.tail_def, Nat.cast_add, Nat.cast_one] at hW hP ⊢
      constructor <;> linarith

theorem mean_expected_cache {k : ℕ} (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1)))
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (work positive : Fin (k + 1) → ℝ) (hw₀ : ∀ u, 0 ≤ work u) (hp₀ : ∀ u, 0 ≤ positive u)
    (hw : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (fun o => (o.work : ℝ)) ≤ work u)
    (hp : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ positive u)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun u => bits (query u))).Nonempty) (xi : ℝ) :
    let mu := Covers.Rejection.uniformRetained (fun u => bits (query u)) hb
    (Mean.program query root C s B c xi callback).evaluate m bits (fun o => (o.work : ℝ)) ≤
        64 * (B + s + 1) + s * mu.expect work ∧
      (Mean.program query root C s B c xi callback).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤
        s + s * mu.expect positive := by
  dsimp only
  let mu := Covers.Rejection.uniformRetained (fun u => bits (query u)) hb
  let sample : Code M Q (Sampler.Records Q k s) := Sampler.program query root C s B c
  let W : (Fin s → Fin (k + 1)) → ℝ := fun labels => 6 * s + 2 + ∑ j, work (labels j)
  let P : (Fin s → Fin (k + 1)) → ℝ := fun labels => ∑ j, positive (labels j)
  have hW₀ : ∀ labels, 0 ≤ W labels := fun labels => add_nonneg (by positivity)
    (Finset.sum_nonneg (fun j _ => hw₀ _))
  have hP₀ : ∀ labels, 0 ≤ P labels := fun labels => Finset.sum_nonneg (fun j _ => hp₀ _)
  have hWsample : sample.evaluate m bits
      (fun o => (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 W) ≤
        6 * s + 2 + s * mu.expect work := by
    rw [Mean.sampler_selected_expect m bits query root C s B c hc (fun v => v.elim 0 W)]
    exact (Mean.cappedAccepted_expect_le _ hb root C s B W hW₀).trans_eq (by
      dsimp [W]
      rw [Law.expect_add, Law.expect_const, Mean.tape_sum_expect])
  have hPsample : sample.evaluate m bits
      (fun o => (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 P) ≤
        s * mu.expect positive := by
    rw [Mean.sampler_selected_expect m bits query root C s B c hc (fun v => v.elim 0 P)]
    exact (Mean.cappedAccepted_expect_le _ hb root C s B P hP₀).trans_eq
      (Mean.tape_sum_expect mu positive s)
  have hsampleW : sample.evaluate m bits (fun o => (o.work : ℝ)) ≤ 16 * (B + s + 1) := by
    apply (Mean.evaluate_mono_runs m bits sample _ (fun _ => 16 * (B + s + 1)) ?_).trans_eq
      (Code.evaluate_const m bits sample _)
    intro o ho
    have hr := Sampler.pool_resources m bits query root C s (Sampler.Store.initial c B) o ho
    have hB : o.value.store.proposals ≤ B := by dsimp [Sampler.Store.initial] at hr; omega
    have hw' := hr.2.2.2.2.1
    dsimp [Sampler.Store.initial] at hw'
    exact_mod_cast hw'.trans (by omega)
  have hsampleP := (Mean.sampler_expected m bits query root C s B c).2
  have hafterW (r : Sampler.Records Q k s) (hr : Cache.Correct bits r.store.cache) :
      (Mean.afterSample xi callback r).evaluate m bits (fun o => (o.work : ℝ)) ≤
        40 + (Mean.selected (Sampler.Observation.ofRecords r)).elim 0 W := by
    rw [Mean.afterSample_work]
    apply add_le_add le_rfl
    cases he : Mean.selected (Sampler.Observation.ofRecords r) with
    | none => exact le_rfl
    | some labels => exact (scores_expected_cache m bits callback hcb work positive hw hp s labels _ hr).1
  have hafterP (r : Sampler.Records Q k s) (hr : Cache.Correct bits r.store.cache) :
      (Mean.afterSample xi callback r).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤
        (Mean.selected (Sampler.Observation.ofRecords r)).elim 0 P := by
    rw [Mean.afterSample_positive]
    cases he : Mean.selected (Sampler.Observation.ofRecords r) with
    | none => exact le_rfl
    | some labels => exact (scores_expected_cache m bits callback hcb work positive hw hp s labels _ hr).2
  constructor
  · rw [Mean.program, Code.evaluate_work_bind]
    have hh := Mean.evaluate_mono_runs m bits sample
      (fun o => (o.work : ℝ) + (Mean.afterSample xi callback o.value).evaluate m bits (fun z => (z.work : ℝ)))
      (fun o => (o.work : ℝ) + (40 + (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 W))
      (fun o ho => add_le_add le_rfl (hafterW o.value (Mean.sampler_cache_correct m bits query root C s B c hc o ho)))
    simp only [Code.evaluate_add, Code.evaluate_const] at hh
    simp only [Code.evaluate_add]
    have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    linarith
  · rw [Mean.program, Code.evaluate_positive_bind]
    have hh := Mean.evaluate_mono_runs m bits sample
      (fun o => (o.positiveReplies : ℝ) +
        (Mean.afterSample xi callback o.value).evaluate m bits (fun z => (z.positiveReplies : ℝ)))
      (fun o => (o.positiveReplies : ℝ) + (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 P)
      (fun o ho => add_le_add le_rfl (hafterP o.value (Mean.sampler_cache_correct m bits query root C s B c hc o ho)))
    simp only [Code.evaluate_add] at hh ⊢
    exact hh.trans (add_le_add hsampleP hPsample)

end SteinerUpperBound.LargeCoverProgram

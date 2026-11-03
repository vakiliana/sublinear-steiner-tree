module

public import SteinerUpperBound.MSTApproximation.Correctness

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection

variable {V Q : Type*} [Fintype V] {k : ℕ}

noncomputable def scaleBudget (terminals B C samples : ℕ) : ℕ :=
  16 * (samples * C + samples + 1) + continuationBudget terminals B samples

noncomputable def loopBudget (terminals B C samples : ℕ) (is : List ℕ) : ℕ :=
  (is.map (fun i => scaleBudget terminals B C samples + (2 * i + 13))).sum

theorem evaluate_tick_work {M R : Type*} (w : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (n : ℕ) :
    (Code.tick n p).evaluate w b (fun o => (o.work : ℝ)) =
      ((n + 1 : ℕ) : ℝ) + p.evaluate w b (fun o => (o.work : ℝ)) := by
  simp only [Code.evaluate, Outcome.add, Nat.cast_add, Code.evaluate_add, Code.evaluate_const]

theorem evaluate_tick_positive {M R : Type*} (w : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (n : ℕ) :
    (Code.tick n p).evaluate w b (fun o => (o.positiveReplies : ℝ)) =
      p.evaluate w b (fun o => (o.positiveReplies : ℝ)) := by
  simp only [Code.evaluate, Outcome.add, Nat.zero_add]

theorem frontendLoop_expected_resources (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hc : Cache.Correct b s.cache)
    (he : Finset.univ.image e = l.toFinset) (hr : ∀ i ∈ is, b (key i (e root)) = true) :
    (frontendLoop e key g xi B C samples l root is s).evaluate I.weight b (fun o => (o.work : ℝ)) ≤
        loopBudget l.length B C samples is ∧
      (frontendLoop e key g xi B C samples l root is s).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ (B + 1) * samples * is.length := by
  induction is generalizing s with
  | nil => simp [frontendLoop, loopBudget, Code.evaluate, Outcome.pure]
  | cons i is ih =>
    let FW : ScaleAnswer Q → ℝ := fun r =>
      (frontendLoop e key g xi B C samples l root is (recordScale g xi s i r)).evaluate I.weight b
        (fun o => (o.work : ℝ))
    let FP : ScaleAnswer Q → ℝ := fun r =>
      (frontendLoop e key g xi B C samples l root is (recordScale g xi s i r)).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ))
    have htail row := ih (recordScale g xi s i
        (scaleTrace I.weight b e (key i) (g.scale i) xi B C samples l root s.cache row))
      (scaleTrace_fields I b e (key i) (g.scale i) xi B C samples l root s.cache
        hc (hr i List.mem_cons_self) he row).2.2.2
      (fun j hj => hr j (List.mem_cons_of_mem _ hj))
    have hwfuture : (scaleProgram e (key i) (g.scale i) xi B C samples l root s.cache).evaluate
        I.weight b (fun o => FW o.value) ≤ loopBudget l.length B C samples is := by
      rw [scaleProgram_law I.weight b e (key i) (g.scale i) xi B C samples l root s.cache hc FW]
      have h := (Covers.Rejection.poolLaw C samples).expect_mono (fun row => (htail row).1)
      simpa only [Law.expect_const] using h
    have hpfuture : (scaleProgram e (key i) (g.scale i) xi B C samples l root s.cache).evaluate
        I.weight b (fun o => FP o.value) ≤ (B + 1) * samples * is.length := by
      rw [scaleProgram_law I.weight b e (key i) (g.scale i) xi B C samples l root s.cache hc FP]
      have h := (Covers.Rejection.poolLaw C samples).expect_mono (fun row => (htail row).2)
      simpa only [Law.expect_const] using h
    have hscale := scaleProgram_expected_resources I.weight b e (key i) (g.scale i) xi B C samples l root s.cache hc
    have hwscale : (scaleProgram e (key i) (g.scale i) xi B C samples l root s.cache).evaluate
        I.weight b (fun o => (o.work : ℝ)) ≤ (scaleBudget l.length B C samples : ℝ) := by
      simpa only [scaleBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hscale.2.2
    constructor
    · rw [frontendLoop, Code.evaluate_work_bind]
      simp_rw [evaluate_tick_work]
      rw [Code.evaluate_add, Code.evaluate_add, Code.evaluate_const]
      change _ ≤ ((scaleBudget l.length B C samples + (2 * i + 13) +
        loopBudget l.length B C samples is : ℕ) : ℝ)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      dsimp only [FW] at hwfuture
      nlinarith
    · rw [frontendLoop, Code.evaluate_positive_bind]
      simp_rw [evaluate_tick_positive]
      rw [Code.evaluate_add]
      dsimp only [FP] at hpfuture
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith [hscale.2.1]

theorem frontend_expected_resources (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (nu xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (he : Finset.univ.image e = l.toFinset)
    (hr : ∀ i < g.intervals, b (key i (e root)) = true) :
    (frontend e key g nu xi B C samples l root cache).evaluate I.weight b
        (fun o => (o.work : ℝ)) ≤ loopBudget l.length B C samples (List.range g.intervals) + 11 ∧
      (frontend e key g nu xi B C samples l root cache).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ (B + 1) * samples * g.intervals := by
  have h := frontendLoop_expected_resources I b e key g xi B C samples l root (List.range g.intervals)
    (initialState cache) hc he (fun i hi => hr i (List.mem_range.mp hi))
  constructor
  · rw [frontend, Code.evaluate_work_bind]
    have hfun : (fun a : Outcome (FrontendState Q) => (a.work : ℝ) +
        (Code.tick 10 (.pure (finish (k + 1) g nu a.value))).evaluate I.weight b (fun o => (o.work : ℝ))) =
        (fun a => (a.work : ℝ) + 11) := by
      funext a
      norm_num [Code.evaluate, Outcome.add, Outcome.pure]
    rw [hfun, Code.evaluate_add, Code.evaluate_const]
    exact add_le_add h.1 le_rfl
  · rw [frontend, Code.evaluate_positive_bind]
    have hfun : (fun a : Outcome (FrontendState Q) => (a.positiveReplies : ℝ) +
        (Code.tick 10 (.pure (finish (k + 1) g nu a.value))).evaluate I.weight b (fun o => (o.positiveReplies : ℝ))) =
        (fun a => (a.positiveReplies : ℝ)) := by
      funext a
      norm_num [Code.evaluate, Outcome.add, Outcome.pure]
    rw [hfun]
    simpa only [List.length_range] using h.2

theorem loopBudget_range_bound (terminals B C samples intervals fuel : ℕ) (hn : intervals ≤ fuel) :
    loopBudget terminals B C samples (List.range intervals) ≤
      (scaleBudget terminals B C samples + 2 * fuel + 13) * fuel := by
  have hmain : ∀ is : List ℕ, (∀ i ∈ is, i ≤ fuel) →
      (is.map (fun i => scaleBudget terminals B C samples + (2 * i + 13))).sum ≤
        (scaleBudget terminals B C samples + 2 * fuel + 13) * is.length := by
    intro is
    induction is with
    | nil => simp
    | cons i is ih =>
      intro hi
      have hhead : scaleBudget terminals B C samples + (2 * i + 13) ≤
          scaleBudget terminals B C samples + 2 * fuel + 13 := by
        have h := hi i List.mem_cons_self
        omega
      have ht := ih (fun j hj => hi j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith
  have h := hmain (List.range intervals) (fun i hi => (List.mem_range.mp hi).le.trans hn)
  simp only [List.length_range] at h
  exact h.trans (Nat.mul_le_mul_left _ hn)

end SteinerUpperBound.MSTApproximation

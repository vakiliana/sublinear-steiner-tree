module

public import SteinerUpperBound.MSTApproximation.ScaleProgram

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.OracleProgram.Sampler

variable {V Q : Type*} [Fintype V] {k : ℕ}

noncomputable def continuationBudget (terminals B samples : ℕ) : ℕ :=
  (80 * (terminals + 1) * (B + 2) ^ 2 + 7) * samples + 17

theorem continuationResult_resources (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B : ℕ) (l : List V) (samples : ℕ) (cache : Cache Q)
    (hc : Cache.Correct b cache) (obs : Observation k samples) :
    (continuationResult w b e key a xi B l samples cache obs).metricQueries ≤
        (B + 1) * l.length * samples ∧
      (continuationResult w b e key a xi B l samples cache obs).positiveReplies ≤ B * samples ∧
      (continuationResult w b e key a xi B l samples cache obs).work ≤
        continuationBudget l.length B samples := by
  cases hy : obs.labels with
  | none => simp [continuationResult, hy, continuationBudget]
  | some ys =>
    obtain ⟨hm, hp, hw⟩ := scoresResult_resources w b key a B l (List.ofFn (fun j => e (ys j))) cache hc
    simp only [List.length_ofFn] at hm hp hw
    simp only [continuationResult, hy, Outcome.add, Outcome.combine, Outcome.pure,
      Nat.add_zero, Nat.zero_add, continuationBudget]
    constructor
    · exact hm
    constructor
    · exact hp
    · nlinarith

theorem pool_expected_resources (w : Sym2 V → ℝ) (b : Q → Bool) (query : Fin (k + 1) → Q)
    (root : Fin (k + 1)) (C samples : ℕ) (cache : Cache Q) :
    let p : Code (Sym2 V) Q (Records Q k samples) :=
      Covers.OracleProgram.Sampler.program query root C samples (samples * C) cache
    p.evaluate w b (fun o => (o.metricQueries : ℝ)) = 0 ∧
      p.evaluate w b (fun o => (o.positiveReplies : ℝ)) ≤ samples ∧
      p.evaluate w b (fun o => (o.work : ℝ)) ≤ 16 * (samples * C + samples + 1) := by
  dsimp only
  let p : Code (Sym2 V) Q (Records Q k samples) :=
    Covers.OracleProgram.Sampler.program query root C samples (samples * C) cache
  have hpoint (seed : (p.compile w).Seed) :
      let o := (((p.compile w).tree seed).output b)
      o.metricQueries = 0 ∧ o.positiveReplies ≤ samples ∧
        o.work ≤ 16 * (samples * C + samples + 1) := by
    have h := program_resources w b query root C samples (samples * C) cache seed
    have hm : (((p.compile w).tree seed).output b).metricQueries = 0 := h.1
    have hp : (((p.compile w).tree seed).output b).positiveReplies ≤ samples := h.2.2.1
    have hw : (((p.compile w).tree seed).output b).work ≤
        16 * ((((p.compile w).tree seed).output b).value.store.proposals + samples + 1) := h.2.2.2.1
    have hcap : (((p.compile w).tree seed).output b).value.store.proposals ≤ samples * C := h.2.2.2.2
    exact ⟨hm, hp, by omega⟩
  constructor
  · rw [← Code.compile_expect]
    have hf : (fun seed : (p.compile w).Seed =>
        ((((p.compile w).tree seed).output b).metricQueries : ℝ)) = fun _ => 0 := by
      funext seed
      rw [(hpoint seed).1]
      norm_num
    change (p.compile w).law.expect
      (fun seed => (((p.compile w).tree seed).output b).metricQueries) = 0
    rw [hf, Law.expect_const]
  constructor
  · rw [← Code.compile_expect]
    change (p.compile w).law.expect
      (fun seed => ((((p.compile w).tree seed).output b).positiveReplies : ℝ)) ≤ _
    have hh := (p.compile w).law.expect_mono (fun seed =>
      (show (((((p.compile w).tree seed).output b).positiveReplies : ℕ) : ℝ) ≤ samples by
        exact_mod_cast (hpoint seed).2.1))
    simpa only [Law.expect_const] using hh
  · rw [← Code.compile_expect]
    change (p.compile w).law.expect
      (fun seed => ((((p.compile w).tree seed).output b).work : ℝ)) ≤ _
    have hbound (seed : (p.compile w).Seed) :
        (((((p.compile w).tree seed).output b).work : ℕ) : ℝ) ≤
          16 * ((samples : ℝ) * C + samples + 1) := by
      exact_mod_cast (hpoint seed).2.2
    have hh := (p.compile w).law.expect_mono hbound
    simpa only [Law.expect_const] using hh

theorem evaluate_metric_bind {M R S : Type*} (w : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) :
    (p.bind next).evaluate w b (fun o => (o.metricQueries : ℝ)) =
      p.evaluate w b (fun a =>
        (a.metricQueries : ℝ) + (next a.value).evaluate w b (fun o => (o.metricQueries : ℝ))) := by
  rw [Code.evaluate_bind]
  apply congrArg (p.evaluate w b)
  funext a
  simp only [Outcome.combine, Nat.cast_add, Code.evaluate_add, Code.evaluate_const]

theorem scaleProgram_expected_resources (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) :
    (scaleProgram e key a xi B C samples l root cache).evaluate w b
        (fun o => (o.metricQueries : ℝ)) ≤ (B + 1) * l.length * samples ∧
      (scaleProgram e key a xi B C samples l root cache).evaluate w b
        (fun o => (o.positiveReplies : ℝ)) ≤ (B + 1) * samples ∧
      (scaleProgram e key a xi B C samples l root cache).evaluate w b
        (fun o => (o.work : ℝ)) ≤
          16 * (samples * C + samples + 1) + continuationBudget l.length B samples := by
  obtain ⟨hmetric, hpositive, hwork⟩ := pool_expected_resources w b (fun j => key (e j)) root C samples cache
  have hcont (obs : Observation k samples) := continuationResult_resources w b e key a xi B l samples cache hc obs
  have hm (obs : Observation k samples) :
      (scaleContinuation e key a xi B l samples cache obs).evaluate w b (fun o => (o.metricQueries : ℝ)) ≤
        (B + 1) * l.length * samples := by
    rw [scaleContinuation_evaluates]
    exact_mod_cast (hcont obs).1
  have hp (obs : Observation k samples) :
      (scaleContinuation e key a xi B l samples cache obs).evaluate w b (fun o => (o.positiveReplies : ℝ)) ≤
        B * samples := by
    rw [scaleContinuation_evaluates]
    exact_mod_cast (hcont obs).2.1
  have hw (obs : Observation k samples) :
      (scaleContinuation e key a xi B l samples cache obs).evaluate w b (fun o => (o.work : ℝ)) ≤
        continuationBudget l.length B samples := by
    rw [scaleContinuation_evaluates]
    exact_mod_cast (hcont obs).2.2
  constructor
  · rw [scaleProgram, evaluate_metric_bind]
    apply (Code.evaluate_mono w b _ (fun o => add_le_add le_rfl (hm (Observation.ofRecords o.value)))).trans
    rw [Code.evaluate_add, Code.evaluate_const, hmetric, zero_add]
  constructor
  · rw [scaleProgram, Code.evaluate_positive_bind]
    apply (Code.evaluate_mono w b _ (fun o => add_le_add le_rfl (hp (Observation.ofRecords o.value)))).trans
    rw [Code.evaluate_add, Code.evaluate_const]
    nlinarith
  · rw [scaleProgram, Code.evaluate_work_bind]
    apply (Code.evaluate_mono w b _ (fun o => add_le_add le_rfl (hw (Observation.ofRecords o.value)))).trans
    rw [Code.evaluate_add, Code.evaluate_const]
    exact add_le_add hwork le_rfl

end SteinerUpperBound.MSTApproximation

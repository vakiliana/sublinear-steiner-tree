module

public import SteinerUpperBound.Covers.OracleProgramSamplerCorrectness

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Sampler

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q : Type*} {k : ℕ}

/-- Marginal iid-uniform coupling for the actual runtime sampler. The oracle is
fixed only in this analysis theorem; factory composition averages over its
actual bit law using the causal finite-seed theorem. -/
theorem program_uniform_budget (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (cache : Q → Option Bool) (hc : Cache.Correct b cache)
    (hb : (Rejection.retained (fun y => b (query y))).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    ∀ test : Option (Fin s → Fin (k + 1)) → Bool,
      |(program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
          (fun o => if test o.value.labels = true then 1 else 0) -
        (tape (Rejection.uniformRetained (fun y => b (query y)) hb) s).prob
          {labels | test (some labels) = true}| ≤ β := by
  classical
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
  intro test
  have hold := Rejection.capped_sampler_uniform_budget (fun y => b (query y)) hb root
    β ξ hβ hβ1 hξ hξ1
  have he := hold {labels | test labels = true}
  have ha :
      (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
        (fun o => if test o.value.labels = true then (1 : ℝ) else 0) =
      ((Rejection.poolLaw C s).map
        (fun rows => (Rejection.cappedPoolTree root C s B rows).output (fun y => b (query y)))).prob
          {labels | test labels = true} := by
    rw [program_output_evaluate m b query root C s B cache hc
      (fun labels => if test labels = true then 1 else 0), Law.prob_map, Law.prob_eq_expect]
    apply congrArg (Rejection.poolLaw C s).expect
    funext rows
    by_cases h : test ((Rejection.cappedPoolTree root C s B rows).output (fun y => b (query y))) = true <;>
      simp [h]
  have hi :
      ((tape (Rejection.uniformRetained (fun y => b (query y)) hb) s).map some).prob
        {labels | test labels = true} =
      (tape (Rejection.uniformRetained (fun y => b (query y)) hb) s).prob
        {labels | test (some labels) = true} := by
    rw [Law.prob_map]
    rfl
  rw [ha]
  rw [hi] at he
  exact he

/-- Calibration and cap errors are bounded marginally for actual recorded
proposal counts. This theorem does not condition the label law on calibration. -/
theorem program_calibration_budget (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (cache : Q → Option Bool) (hc : Cache.Correct b cache)
    (hb : (Rejection.retained (fun y => b (query y))).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
      (fun o => if GoodRecord (fun y => b (query y)) s ξ (Observation.ofRecords o.value)
        then 0 else 1) ≤ β := by
  classical
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
  let bu := fun y => b (query y)
  let Bad : Set (Fin s → Fin C → Fin (k + 1)) := {rows |
    B < Rejection.proposals bu C s rows ∨
      ¬ Rejection.Successful bu C s rows ∨ ¬ Rejection.Calibrated bu C s ξ rows}
  have hold := Rejection.capped_sampler_and_calibration bu hb β ξ hβ hβ1 hξ hξ1
  change (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
    (fun o => if GoodRecord bu s ξ (Observation.ofRecords o.value) then 0 else 1) ≤ β
  have hpoint (rows : Fin s → Fin C → Fin (k + 1)) :
      (if GoodRecord bu s ξ (replayPool bu root C s B 0 rows) then (0 : ℝ) else 1) ≤
        if rows ∈ Bad then 1 else 0 := by
    by_cases hbad : rows ∈ Bad
    · by_cases hg : GoodRecord bu s ξ (replayPool bu root C s B 0 rows) <;> simp [hbad, hg]
    · have hnot : ¬ (B < Rejection.proposals bu C s rows ∨
          ¬ Rejection.Successful bu C s rows ∨ ¬ Rejection.Calibrated bu C s ξ rows) := hbad
      have hB : Rejection.proposals bu C s rows ≤ B :=
        le_of_not_gt (fun h => hnot (Or.inl h))
      have hs : Rejection.Successful bu C s rows := by
        by_contra hn
        exact hnot (Or.inr (Or.inl hn))
      have hcal : Rejection.Calibrated bu C s ξ rows := by
        by_contra hn
        exact hnot (Or.inr (Or.inr hn))
      have hg := replayPool_good bu root C s B rows ξ hB hs hcal
      simp [hbad, hg]
  calc
    _ = (Rejection.poolLaw C s).expect
        (fun rows => if GoodRecord bu s ξ (replayPool bu root C s B 0 rows) then 0 else 1) := by
      convert pool_evaluate_replay m b query root C s (Store.initial cache B) hc
        (fun obs => if GoodRecord bu s ξ obs then (0 : ℝ) else 1) using 1 <;>
        congr 1 <;> funext x <;> split_ifs <;> rfl
    _ ≤ (Rejection.poolLaw C s).prob Bad := by
      rw [Law.prob_eq_expect]
      apply Law.expect_mono
      intro rows
      by_cases hg : GoodRecord bu s ξ (replayPool bu root C s B 0 rows) <;>
        by_cases hb : rows ∈ Bad <;> simpa only [hg, hb, ite_true, ite_false] using hpoint rows
    _ ≤ β := hold

end SteinerUpperBound.Covers.OracleProgram.Sampler

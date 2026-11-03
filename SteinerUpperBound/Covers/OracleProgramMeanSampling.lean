module

public import SteinerUpperBound.Covers.OracleProgramMeanKernel
public import SteinerLowerBound.FiniteVariation

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {M Q U : Type*} [Fintype U] [Nonempty U]

noncomputable def accepted (b : U → Bool) (root : U) (C s : ℕ)
    (rows : Fin s → Fin C → U) : Option (Fin s → U) :=
  if Rejection.Successful b C s rows then some (Rejection.labels b root C s rows) else none

noncomputable def cappedAccepted (b : U → Bool) (root : U) (C s B : ℕ)
    (rows : Fin s → Fin C → U) : Option (Fin s → U) :=
  if Rejection.proposals b C s rows ≤ B then accepted b root C s rows else none

noncomputable def capError (b : U → Bool) (C s B : ℕ) : ℝ :=
  (Rejection.poolLaw C s).prob {rows | B < Rejection.proposals b C s rows} +
    (Rejection.poolLaw C s).prob {rows | ¬ Rejection.Successful b C s rows}

theorem accepted_mass (b : U → Bool) (hb : (Rejection.retained b).Nonempty)
    (root : U) (C s : ℕ) (w : Fin s → U) :
    ((Rejection.poolLaw C s).map (accepted b root C s)).mass (some w) =
      (1 - (Rejection.poolLaw C s).prob {rows | ¬ Rejection.Successful b C s rows}) *
        (tape (Rejection.uniformRetained b hb) s).mass w := by
  classical
  rw [← CategoricalCoupling.probability_atom, Law.prob_map]
  have he :
      (accepted b root C s ⁻¹' ({some w} : Set (Option (Fin s → U)))) =
        {rows | Rejection.Successful b C s rows ∧ Rejection.labels b root C s rows = w} := by
    ext rows
    by_cases h : Rejection.Successful b C s rows <;> simp [accepted, h]
  rw [he, Rejection.pool_success_atom b hb, Rejection.pool_failure b hb]
  ring

theorem accepted_uniform_close (b : U → Bool) (hb : (Rejection.retained b).Nonempty)
    (root : U) (C s : ℕ) :
    Law.Close ((Rejection.poolLaw C s).map (accepted b root C s))
      ((tape (Rejection.uniformRetained b hb) s).map some)
      ((Rejection.poolLaw C s).prob {rows | ¬ Rejection.Successful b C s rows}) := by
  classical
  let α := 1 - (Rejection.poolLaw (U := U) C s).prob
    {rows | ¬ Rejection.Successful b C s rows}
  have hα : 0 ≤ α := sub_nonneg.mpr (Law.prob_le_one _ _)
  have hp := (Rejection.poolLaw (U := U) C s).prob_nonneg
    {rows | ¬ Rejection.Successful b C s rows}
  have hα1 : α ≤ 1 := by dsimp [α]; linarith
  have h := Rejection.close_of_mass_domination
    ((Rejection.poolLaw C s).map (accepted b root C s))
    ((tape (Rejection.uniformRetained b hb) s).map some) α hα hα1 (by
      intro value
      cases value with
      | none =>
        have hz : ((tape (Rejection.uniformRetained b hb) s).map some).mass none = 0 := by
          simp [Law.map]
        rw [hz, mul_zero]
        exact ((Rejection.poolLaw C s).map (accepted b root C s)).nonneg none
      | some w =>
        rw [accepted_mass b hb root C s w]
        simp [Law.map, α])
  have he : 1 - α =
      (Rejection.poolLaw (U := U) C s).prob {rows | ¬ Rejection.Successful b C s rows} := by
    dsimp [α]
    ring
  rw [he] at h
  exact h

theorem cappedAccepted_uniform_close (b : U → Bool) (hb : (Rejection.retained b).Nonempty)
    (root : U) (C s B : ℕ) :
    Law.Close ((Rejection.poolLaw C s).map (cappedAccepted b root C s B))
      ((tape (Rejection.uniformRetained b hb) s).map some) (capError b C s B) := by
  classical
  have hc := Law.close_maps (Rejection.poolLaw C s)
    (cappedAccepted b root C s B) (accepted b root C s)
  have hs : {rows | cappedAccepted b root C s B rows ≠ accepted b root C s rows} ⊆
      {rows | B < Rejection.proposals b C s rows} := by
    intro rows h
    change cappedAccepted b root C s B rows ≠ accepted b root C s rows at h
    by_contra hn
    change ¬ B < Rejection.proposals b C s rows at hn
    exact h (by simp [cappedAccepted, le_of_not_gt hn])
  exact (hc.mono (Law.prob_mono _ hs)).trans (accepted_uniform_close b hb root C s)

theorem cappedAccepted_expect_le (b : U → Bool) (hb : (Rejection.retained b).Nonempty)
    (root : U) (C s B : ℕ) (F : (Fin s → U) → ℝ) (hF : ∀ w, 0 ≤ F w) :
    (Rejection.poolLaw C s).expect
        (fun rows => (cappedAccepted b root C s B rows).elim 0 F) ≤
      (tape (Rejection.uniformRetained b hb) s).expect F := by
  classical
  have hcap :
      (Rejection.poolLaw C s).expect
          (fun rows => (cappedAccepted b root C s B rows).elim 0 F) ≤
      ((Rejection.poolLaw C s).map (accepted b root C s)).expect
        (fun value => value.elim 0 F) := by
    rw [Law.expect_map]
    apply Law.expect_mono
    intro rows
    by_cases h : Rejection.proposals b C s rows ≤ B
    · simp [cappedAccepted, h]
    · simp only [cappedAccepted, h, ite_false, Option.elim_none]
      cases accepted b root C s rows with
      | none => exact le_rfl
      | some w => exact hF w
  have hfull :
      ((Rejection.poolLaw C s).map (accepted b root C s)).expect
          (fun value => value.elim 0 F) ≤
      ((tape (Rejection.uniformRetained b hb) s).map some).expect
        (fun value => value.elim 0 F) := by
    unfold Law.expect
    apply Finset.sum_le_sum
    intro value _
    cases value with
    | none => simp
    | some w =>
      simp only [Option.elim_some, accepted_mass b hb root C s w]
      have hα : 1 - (Rejection.poolLaw (U := U) C s).prob
          {rows | ¬ Rejection.Successful b C s rows} ≤ 1 := by
        linarith [Law.prob_nonneg (Rejection.poolLaw (U := U) C s)
          {rows | ¬ Rejection.Successful b C s rows}]
      calc
        _ ≤ (1 * (tape (Rejection.uniformRetained b hb) s).mass w) * F w :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hα (Law.nonneg _ _)) (hF w)
        _ = _ := by simp [Law.map]
  simpa only [Law.expect_map, Option.elim_some] using hcap.trans hfull

theorem capError_budget (b : U → Bool) (hb : (Rejection.retained b).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card U) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card U) s β
    capError b C s B ≤ β := by
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card U) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card U) s β
  have hp := Rejection.proposals_budget b hb C s β hβ
  have hs := Rejection.sampler_and_calibration b hb (β / 2) ξ (by positivity)
    (by linarith) hξ hξ1
  have hr : (Rejection.poolLaw C s).prob {rows | ¬ Rejection.Successful b C s rows} ≤ β / 2 :=
    (Law.prob_mono _ (fun _ h => Or.inl h)).trans hs
  exact (add_le_add hp hr).trans (by ring_nf; rfl)

variable {A : Type*} [Fintype A]

theorem selected_replay {k : ℕ} (b : Fin (k + 1) → Bool) (root : Fin (k + 1))
    (C s B : ℕ) (rows : Fin s → Fin C → Fin (k + 1)) :
    selected (Sampler.replayPool b root C s B 0 rows) = cappedAccepted b root C s B rows := by
  classical
  by_cases hB : Rejection.proposals b C s rows ≤ B
  · rw [Sampler.replayPool_complete b root C s B 0 rows hB]
    by_cases hs : Rejection.Successful b C s rows <;>
      simp [selected, Sampler.completed, cappedAccepted, accepted, hB, hs]
  · have h := Sampler.replayPool_abort b root C s B 0 rows (Nat.lt_of_not_ge hB)
    simp [selected, h.2.1, cappedAccepted, hB]

/-- Total optional-score law, within the actual rejection/proposal cap error,
for genuinely stateful stochastic score callbacks. -/
theorem program_value_close {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Rejection.retained (fun y => b (query y))).Nonempty) (ξ : ℝ)
    (F : Option ℝ → ℝ) (hF₀ : ∀ z, 0 ≤ F z) (hF₁ : ∀ z, F z ≤ 1) :
    |(program query root C s B c ξ callback).evaluate m b (fun o => F o.value.value) -
      (tape (pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel) s).expect
        (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w)))| ≤
      capError (fun y => b (query y)) C s B := by
  classical
  let φ : Option (Fin s → Fin (k + 1)) → ℝ := fun value =>
    value.elim (F none) (fun labels =>
      sumValue kernel score s labels (fun z => F (some (z / s))))
  have hφ₀ : ∀ value, 0 ≤ φ value := by
    intro value
    cases value with
    | none => exact hF₀ none
    | some labels => exact (sumValue_bounds kernel score s labels _ (fun z => hF₀ _) (fun z => hF₁ _)).1
  have hφ₁ : ∀ value, φ value ≤ 1 := by
    intro value
    cases value with
    | none => exact hF₁ none
    | some labels => exact (sumValue_bounds kernel score s labels _ (fun z => hF₀ _) (fun z => hF₁ _)).2
  have ha :
      (program query root C s B c ξ callback).evaluate m b (fun o => F o.value.value) =
        ((Rejection.poolLaw C s).map (cappedAccepted (fun y => b (query y)) root C s B)).expect φ := by
    rw [program_value h query root C s B c hc ξ (fun z _ => F z), Law.expect_map]
    apply congrArg (Rejection.poolLaw C s).expect
    funext rows
    simp only [observedValue, selected_replay]
    cases cappedAccepted (fun y => b (query y)) root C s B rows <;> rfl
  have hr :
      ((tape (Rejection.uniformRetained (fun y => b (query y)) hb) s).map some).expect φ =
        (tape (pointKernel (Rejection.uniformRetained (fun y => b (query y)) hb) kernel) s).expect
          (fun w => F (some (ScoreSampling.empirical (fun p => score p.1 p.2) s w))) := by
    rw [Law.expect_map]
    exact iid_empirical_value _ kernel score s (fun z => F (some z))
  rw [ha, ← hr]
  exact (cappedAccepted_uniform_close (fun y => b (query y)) hb root C s B).expect_bound φ hφ₀ hφ₁

end SteinerUpperBound.Covers.OracleProgram.Mean

module

public import SteinerUpperBound.ConcreteEstimator.Correctness.Support
public import SteinerUpperBound.ConcreteEstimator.Step.Basic

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator.Correctness

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

theorem summed_clock_loss (n count : ℕ) (hcount : count ≤ heightBudget n) :
    (count : ℝ) * (5 / (EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1))) ≤
      1 / 20000 := by
  have hc : (count : ℝ) ≤ (heightBudget n : ℝ) + 1 := by exact_mod_cast (by omega)
  have hd : (0 : ℝ) < EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1) := by
    unfold EstimatorClocks.amplification
    positivity
  rw [← mul_div_assoc, div_le_iff₀ hd]
  norm_num only [EstimatorClocks.amplification, Nat.cast_ofNat]
  linarith

theorem failureLedger_le (n : ℕ) (tables : Tables) (δ : ℝ) (hδ : 0 ≤ δ)
    (hf : tables.fine.intervals ≤ heightBudget n)
    (hc : tables.coarse.intervals + 1 ≤ heightBudget n) :
    EstimatorFrontend.Analysis.failureLedger n tables (Step.error n δ) ≤
      58 / 1000000 + (heightBudget n : ℝ) * δ := by
  have hfb := beta_union n tables.fine.intervals hf
  have hcb := beta_union n (tables.coarse.intervals + 1) hc
  have hcd : ((tables.coarse.intervals + 1 : ℕ) : ℝ) * δ ≤ (heightBudget n : ℝ) * δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hδ
  have hclock := summed_clock_loss n (tables.coarse.intervals + 1) hc
  push_cast at hcb hcd hclock
  unfold EstimatorFrontend.Analysis.failureLedger Step.error
  push_cast
  nlinarith

theorem failureLedger_beta (n : ℕ) (tables : Tables) (δ : ℝ) (q : ℕ) (hδ : 0 ≤ δ)
    (hδq : δ ≤ q * beta n) (hf : tables.fine.intervals ≤ heightBudget n)
    (hc : tables.coarse.intervals + 1 ≤ heightBudget n) :
    EstimatorFrontend.Analysis.failureLedger n tables (Step.error n δ) ≤
      ((q : ℝ) + 58) / 1000000 := by
  have h := failureLedger_le n tables δ hδ hf hc
  have hδ' := mul_le_mul_of_nonneg_left hδq (Nat.cast_nonneg (heightBudget n) : (0 : ℝ) ≤ heightBudget n)
  have hb := mul_le_mul_of_nonneg_left (beta_union n (heightBudget n) (le_refl _))
    (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith

theorem failureLedger_small (n : ℕ) (tables : Tables) (δ : ℝ) (q : ℕ) (hδ : 0 ≤ δ)
    (hq : q ≤ 9000) (hδq : δ ≤ q * beta n)
    (hf : tables.fine.intervals ≤ heightBudget n)
    (hc : tables.coarse.intervals + 1 ≤ heightBudget n) :
    EstimatorFrontend.Analysis.failureLedger n tables (Step.error n δ) ≤ 1 / 100 := by
  have h := failureLedger_beta n tables δ q hδ hδq hf hc
  have hqR : (q : ℝ) ≤ 9000 := by exact_mod_cast hq
  linarith

theorem prepared_margin (count ordinary positive : ℕ) (hc : 0 < count)
    (sampleLoss : ℝ) (hs : sampleLoss ≤ 1 / 100) :
    (49 : ℝ) / 50 ≤ 1 - sampleLoss - 1 / 4000000 - 1 / 1000 -
      (ordinary : ℝ) / ((EstimatorClocks.factory count ordinary positive).clock.workBudget + 1 : ℕ) -
      (positive : ℝ) / (EstimatorClocks.factory count ordinary positive).positiveThreshold -
      Real.exp ((EstimatorClocks.factory count ordinary positive).positiveThreshold -
        ((EstimatorClocks.factory count ordinary positive).clock.disclosureBudget : ℝ) / (2 * count)) := by
  have h := EstimatorBudget.factory_real_cutoff_loss count ordinary positive hc
  linarith

end SteinerUpperBound.ConcreteEstimator.Correctness

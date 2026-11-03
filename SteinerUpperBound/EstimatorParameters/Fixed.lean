module

public import SteinerUpperBound.MSTApproximation.Grid
public import SteinerUpperBound.MSTApproximation.Mass
public import SteinerUpperBound.MSTApproximation.Parameters
public import SteinerUpperBound.EstimationAlgebra
public import SteinerUpperBound.FinitePhase.Spacing

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

open scoped Classical

def cQ : ℚ := 1 / 1000000000000
def nuQ : ℚ := cQ / 10
def zetaQ : ℚ := cQ / 100
def deltaCoarseQ : ℚ := 1 / 10000000000
def deltaFineQ : ℚ := nuQ / 10000
def tauQ : ℚ := 1 / 100000
def coarseRatioQ : ℚ := 101 / 100
def fineRatioQ : ℚ := 1 + nuQ / 100
def QS : ℕ := 32
def QQ : ℕ := 2000

noncomputable abbrev c : ℝ := (cQ : ℝ)
noncomputable abbrev nu : ℝ := (nuQ : ℝ)
noncomputable abbrev zeta : ℝ := (zetaQ : ℝ)
noncomputable abbrev deltaCoarse : ℝ := (deltaCoarseQ : ℝ)
noncomputable abbrev deltaFine : ℝ := (deltaFineQ : ℝ)
noncomputable abbrev tau : ℝ := (tauQ : ℝ)

theorem scalar_bounds :
    0 < c ∧ c ≤ Structural.e0 / (32000 * QS) ∧ c ≤ Structural.sigma0 / (1000 * QQ) ∧
      c ≤ Structural.e0 / 8 ∧ c ≤ 1 / 10 ∧ 0 < nu ∧ nu = c / 10 ∧ nu ≤ 1 ∧
      0 < zeta ∧ zeta = c / 100 ∧ zeta ≤ 1 := by
  norm_num [c, cQ, nu, nuQ, zeta, zetaQ, QS, QQ, Structural.e0, Structural.sigma0]

theorem ratio_casts :
    (coarseRatioQ : ℝ) = Structural.omega ∧
      (fineRatioQ : ℝ) = MSTApproximation.fineRatio nu ∧
      deltaFine = MSTApproximation.fineDelta nu ∧ tau = Structural.sigma0 / 100 := by
  norm_num [coarseRatioQ, Structural.omega, fineRatioQ, MSTApproximation.fineRatio,
    deltaFine, deltaFineQ, MSTApproximation.fineDelta, nu, nuQ, cQ,
    tau, tauQ, Structural.sigma0]

theorem coarse_doubling : (2 : ℝ) ≤ Structural.omega ^ 100 := by
  have h := one_add_mul_le_pow (a := (1 / 100 : ℝ)) (by norm_num) 100
  conv_lhs at h => norm_num
  rw [show (1 + 1 / 100 : ℝ) = Structural.omega by norm_num [Structural.omega]] at h
  exact h

theorem QQ_separation : 2 / tau < Structural.omega ^ QQ := by
  calc
    2 / tau < (2 : ℝ) ^ 20 := by norm_num [tau, tauQ]
    _ ≤ (Structural.omega ^ 100) ^ 20 :=
      pow_le_pow_left₀ (by norm_num) coarse_doubling _
    _ = _ := by rw [← pow_mul]; rfl

theorem metric_scale_constants :
    0 < deltaCoarse ∧ deltaCoarse < 1 / 100 ∧ 0 < deltaFine ∧ deltaFine < 1 / 100 ∧
      0 < tau ∧ tau < 1 ∧ (1 : ℝ) < fineRatioQ ∧ (fineRatioQ : ℝ) ≤ Structural.omega := by
  norm_num [deltaCoarse, deltaCoarseQ, deltaFine, deltaFineQ, tau, tauQ, fineRatioQ,
    nuQ, cQ, Structural.omega]

end SteinerUpperBound.EstimatorParameters

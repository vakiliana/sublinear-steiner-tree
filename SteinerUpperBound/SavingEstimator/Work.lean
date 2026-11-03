module

public import SteinerUpperBound.SavingEstimator.Program

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator

open EstimatorParameters QueryProgram Covers.OracleProgram

theorem configurationWork_exact (n count : ℕ) (p : PublicParameters) :
    configurationWork n count p =
      6 * (Nat.log2 (512 * p.threshold * p.confidenceDenominator) +
        Nat.log2 (128 * (n + 1) * p.threshold * p.confidenceDenominator) +
        Nat.log2 (16 * ReusableSample.integerSamples p.threshold
          (Nat.log2 (512 * p.threshold * p.confidenceDenominator) + 2)
          (Nat.log2 (128 * (n + 1) * p.threshold * p.confidenceDenominator) + 2) *
            p.confidenceDenominator + 1)) + 109 := by
  simp only [configurationWork, configurationPlan, Setup.mul, Setup.add, Setup.log,
    Bind.bind, Pure.pure, Setup.Plan.work, Setup.Plan.bind,
    Setup.Expr.work, Setup.Expr.value, ReusableSample.integerSamples]
  omega

def poolLogFactor : ℕ := 16 * poolFactor * betaFactor + 8
def configurationFactor : ℕ := 6 * (lFactor + mFactor + poolLogFactor) + 109

theorem pool_argument_bound (n : ℕ) :
    16 * NsPool n * betaDenom n + 1 ≤ (16 * poolFactor * betaFactor + 1) * (n + 2) ^ 6 := by
  have hp : NsPool n * betaDenom n ≤ poolFactor * betaFactor * (n + 2) ^ 6 := by
    calc
      _ ≤ (poolFactor * t n * ell n ^ 2) * (betaFactor * ell n ^ 3) :=
        Nat.mul_le_mul (reusablePool_polylog n) (betaDenom_polylog n)
      _ = poolFactor * betaFactor * t n * ell n ^ 5 := by ring
      _ ≤ poolFactor * betaFactor * (n + 2) * (n + 2) ^ 5 := by
        gcongr
        · exact (t_le n).trans (by omega)
        · exact ell_le n
      _ = _ := by ring
  have h := Nat.mul_le_mul_left 16 hp
  have h₁ : 1 ≤ (n + 2) ^ 6 := by
    have hh : 0 < (n + 2) ^ 6 := by positivity
    omega
  nlinarith

theorem configuration_work_polylog (n count : ℕ) :
    configurationWork n count (parameters n count) ≤ configurationFactor * ell n := by
  have hl : Nat.log2 (512 * t n * betaDenom n) ≤ lFactor * ell n := by
    have hh : Nat.log2 (512 * t n * betaDenom n) ≤ Lbar n := by unfold Lbar noiseK1; omega
    exact hh.trans (noise_polylog n).1
  have hm : Nat.log2 (128 * (n + 1) * t n * betaDenom n) ≤ mFactor * ell n := by
    have hh : Nat.log2 (128 * (n + 1) * t n * betaDenom n) ≤ Mbar n := by unfold Mbar noiseK2; omega
    exact hh.trans (noise_polylog n).2
  have hp := log_of_polynomial_bound n (16 * NsPool n * betaDenom n + 1)
    (16 * poolFactor * betaFactor + 1) 6 (pool_argument_bound n)
  have hp' : Nat.log2 (16 * NsPool n * betaDenom n + 1) ≤ poolLogFactor * ell n := by
    unfold poolLogFactor
    rw [show 16 * poolFactor * betaFactor + 1 + 6 + 1 = 16 * poolFactor * betaFactor + 8 by omega] at hp
    omega
  rw [configurationWork_exact]
  change 6 * (Nat.log2 (512 * t n * betaDenom n) +
      Nat.log2 (128 * (n + 1) * t n * betaDenom n) +
      Nat.log2 (16 * NsPool n * betaDenom n + 1)) + 109 ≤ _
  have he := ell_ge_one n
  unfold configurationFactor
  nlinarith

variable {Q : Type} {n k : ℕ}

theorem fromParameters_work (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : PublicParameters) (cache : Cache Q) :
    (fromParameters terminals root key a p cache).evaluate m bits (fun o => (o.work : ℝ)) =
      configurationWork n (k + 1) p + 12 +
        (LargeCoverProgram.program (configuration n (k + 1) p) terminals root key a
          (PortGraph.RuntimeAdapter.builder key a terminals (configuration n (k + 1) p).cutoff) cache).evaluate
            m bits (fun o => (o.work : ℝ)) := by
  rw [fromParameters, Code.evaluate_work_bind, configure_evaluates, Mean.work_tick]
  norm_num only [Nat.cast_ofNat]
  ring

theorem fromParameters_positive (m : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : PublicParameters) (cache : Cache Q) :
    (fromParameters terminals root key a p cache).evaluate m bits (fun o => (o.positiveReplies : ℝ)) =
      (LargeCoverProgram.program (configuration n (k + 1) p) terminals root key a
        (PortGraph.RuntimeAdapter.builder key a terminals (configuration n (k + 1) p).cutoff) cache).evaluate
          m bits (fun o => (o.positiveReplies : ℝ)) := by
  rw [fromParameters, Code.evaluate_positive_bind, configure_evaluates, Mean.positive_tick]
  simp

end SteinerUpperBound.SavingEstimator

module

public import SteinerUpperBound.EstimatorParameters.Setup.Language

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace SteinerUpperBound.EstimatorParameters

namespace Setup

open QueryProgram

theorem setupPlan_value (n k : ℕ) : (setupPlan n k).value = parameters n k := by
  simp [setupPlan, add, mul, log, sqrt, Bind.bind, Pure.pure, Plan.instMonad, Plan.value, Plan.bind, Expr.value,
    parameters, t, heightBudget, ell, betaDenom, coverTrials, privateCap, coverSlack, hopBudget, Hc,
    A, AM, B, BQ, BM, epsInv, xiSavingInv, xiBandInv, xiMInv, NsPool, Lbar, Mbar, noiseK1, noiseK2,
    coverClock, meanSamples, samplerCap, proposalClock, pow_succ, Nat.add_assoc, Nat.mul_assoc]

def workBudget (n : ℕ) : ℕ :=
  500 + integerSqrtWork n + 6 *
    (Nat.log2 (n + 2) + coverClock n + noiseK1 n + noiseK2 n +
      proposalClock n (xiSavingInv n) + proposalClock n (xiBandInv n) + proposalClock n (xiMInv n))

theorem setupPlan_work_le (n k : ℕ) : (setupPlan n k).work ≤ workBudget n := by
  simp only [setupPlan, add, mul, log, sqrt, Bind.bind, Pure.pure, Plan.instMonad,
    Plan.work, Plan.bind, Plan.value, Expr.work, Expr.value]
  unfold workBudget
  simp only [t, heightBudget, ell, betaDenom, coverTrials, coverSlack, hopBudget, Hc, A, AM,
    epsInv, xiSavingInv, xiBandInv, xiMInv, BM, meanSamples, coverClock, noiseK1, noiseK2, proposalClock,
    pow_succ, pow_zero, Nat.mul_one, Nat.one_mul, Nat.add_assoc, Nat.mul_assoc]
  omega

def setupFactor : ℕ :=
  617 + 6 * (1 + clockFactor + lFactor + mFactor +
    proposalFactor savingFactor + proposalFactor bandFactor + proposalFactor mstFactor)

theorem workBudget_polylog (n : ℕ) : workBudget n ≤ setupFactor * ell n := by
  have he := ell_ge_one n
  have hln : Nat.log2 (n + 2) ≤ ell n := by unfold ell; omega
  have hln0 : Nat.log2 n ≤ ell n := (log2_mono (show n ≤ n + 2 by omega)).trans hln
  have hroot := integerSqrtWork_bound n
  have hclock := coverClock_polylog n
  have hnoise := noise_polylog n
  have hl : noiseK1 n ≤ lFactor * ell n := by
    have h := hnoise.1
    unfold Lbar at h
    omega
  have hm : noiseK2 n ≤ mFactor * ell n := by
    have h := hnoise.2
    unfold Mbar at h
    omega
  have hden := score_budget_polylog n
  have hs := proposalClock_polylog n (xiSavingInv n) savingFactor hden.2.2.1
  have hb := proposalClock_polylog n (xiBandInv n) bandFactor hden.2.2.2.1
  have hM := proposalClock_polylog n (xiMInv n) mstFactor hden.2.2.2.2
  unfold workBudget setupFactor
  nlinarith

end Setup

open QueryProgram

def setupProgram {M Q : Type*} (n k : ℕ) : Code M Q PublicParameters :=
  (Setup.setupPlan n k).program

theorem setupProgram_evaluates {M Q : Type*} (m : M → ℝ) (bits : Q → Bool) (n k : ℕ) :
    Code.Evaluates m bits (setupProgram n k)
      ⟨parameters n k, (Setup.setupPlan n k).work, 0, 0, 0⟩ := by
  have h := Setup.Plan.evaluates m bits (Setup.setupPlan n k)
  rw [Setup.setupPlan_value] at h
  exact h

theorem setupProgram_work {M Q : Type*} (m : M → ℝ) (bits : Q → Bool) (n k : ℕ) :
    (setupProgram n k).evaluate m bits (fun o => (o.work : ℝ)) ≤ Setup.setupFactor * (ell n : ℝ) := by
  rw [setupProgram_evaluates]
  exact_mod_cast (Setup.setupPlan_work_le n k).trans (Setup.workBudget_polylog n)

theorem setupProgram_zero_queries {M Q : Type*} (m : M → ℝ) (bits : Q → Bool) (n k : ℕ) :
    (setupProgram n k).evaluate m bits (fun o => (o.metricQueries : ℝ)) = 0 ∧
      (setupProgram n k).evaluate m bits (fun o => (o.retentionQueries : ℝ)) = 0 ∧
      (setupProgram n k).evaluate m bits (fun o => (o.positiveReplies : ℝ)) = 0 := by
  constructor
  · rw [setupProgram_evaluates]
    norm_num
  constructor <;> rw [setupProgram_evaluates] <;> norm_num

end SteinerUpperBound.EstimatorParameters

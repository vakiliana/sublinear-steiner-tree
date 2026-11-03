module

public import SteinerUpperBound.EstimatorParameters.Sampling
public import SteinerUpperBound.EstimatorParameters.Reusable
public import SteinerUpperBound.EstimatorParameters.LargeBranch
public import SteinerUpperBound.EstimatorParameters.CoverFamily

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

def savingFactor : ℕ := 100000000000 * aFactor
def bandFactor : ℕ := 100000000 * aFactor
def mstFactor : ℕ := 1000000000000000 * amFactor

def coefficients : List ℕ :=
  [heightFactor, betaFactor, 2 * clockFactor, clockFactor, hcFactor, aFactor, amFactor,
    10000000000 * aFactor, 400 * aFactor, savingFactor, bandFactor, mstFactor,
    meanFactor savingFactor, meanFactor bandFactor, meanFactor mstFactor,
    proposalFactor savingFactor, proposalFactor bandFactor, proposalFactor mstFactor, poolFactor]

def publicFactor : ℕ := coefficients.sum + 1
def publicExponent : ℕ := 9

theorem member_le_sum (is : List ℕ) (x : ℕ) (hx : x ∈ is) : x ≤ is.sum := by
  induction is with
  | nil => simp at hx
  | cons i is ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · simp only [List.sum_cons]
      omega
    · have h := ih hx
      simp only [List.sum_cons]
      omega

theorem lift_public_bound (n x C d : ℕ) (hx : x ≤ C * ell n ^ d)
    (hd : d ≤ publicExponent) (hC : C ∈ coefficients) :
    x ≤ publicFactor * ell n ^ publicExponent := by
  have hc : C ≤ publicFactor := (member_le_sum _ _ hC).trans (Nat.le_succ _)
  exact hx.trans (Nat.mul_le_mul hc (ell_power_le n d publicExponent hd))

def coreSizes (n : ℕ) : List ℕ :=
  [heightBudget n, betaDenom n, coverTrials n, coverSlack n, Hc n, A n, AM n, B n, BQ n,
    xiSavingInv n, xiBandInv n, xiMInv n,
    meanSamples n (xiSavingInv n), meanSamples n (xiBandInv n), meanSamples n (xiMInv n)]

theorem all_core_polylog (n x : ℕ) (hx : x ∈ coreSizes n) :
    x ≤ publicFactor * ell n ^ publicExponent := by
  have hA := allowance_polylog n
  have hB := score_budget_polylog n
  have hS := concrete_sampling_polylog n
  simp only [coreSizes, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lift_public_bound _ _ heightFactor 1 (by simp [heightBudget]) (by decide)
      (by simp [coefficients])
  · exact lift_public_bound _ _ betaFactor 3 (betaDenom_polylog n) (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (2 * clockFactor) 1 (by simpa only [pow_one] using (elementary_polylog n).1)
      (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ clockFactor 1 (by simpa only [pow_one] using (elementary_polylog n).2.1)
      (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ hcFactor 1 (by simpa only [pow_one] using (elementary_polylog n).2.2)
      (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ aFactor 3 hA.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ amFactor 3 hA.2 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (10000000000 * aFactor) 3 hB.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (400 * aFactor) 3 hB.2.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ savingFactor 3 hB.2.2.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ bandFactor 3 hB.2.2.2.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ mstFactor 3 hB.2.2.2.2 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (meanFactor savingFactor) 9 hS.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (meanFactor bandFactor) 9 hS.2.1 (by decide) (by simp [coefficients])
  · exact lift_public_bound _ _ (meanFactor mstFactor) 9 hS.2.2 (by decide) (by simp [coefficients])

theorem all_sampler_caps (n k : ℕ) :
    samplerCap n k (xiSavingInv n) ≤ publicFactor * k * ell n ∧
      samplerCap n k (xiBandInv n) ≤ publicFactor * k * ell n ∧
      samplerCap n k (xiMInv n) ≤ publicFactor * k * ell n ∧
      privateCap n k ≤ publicFactor * k * ell n := by
  have h := score_budget_polylog n
  have hS := samplerCap_polylog n k (xiSavingInv n) savingFactor h.2.2.1
  have hB := samplerCap_polylog n k (xiBandInv n) bandFactor h.2.2.2.1
  have hM := samplerCap_polylog n k (xiMInv n) mstFactor h.2.2.2.2
  have hc (C : ℕ) (hC : C ∈ coefficients) : C * k * ell n ≤ publicFactor * k * ell n :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      ((member_le_sum _ _ hC).trans (Nat.le_succ _)))
  exact ⟨hS.trans (hc _ (by simp [coefficients])), hB.trans (hc _ (by simp [coefficients])),
    hM.trans (hc _ (by simp [coefficients])), (privateCap_polylog n k).trans (hc _ (by simp [coefficients]))⟩

theorem pool_public_bound (n : ℕ) : NsPool n ≤ publicFactor * t n * ell n ^ 2 := by
  have hc : poolFactor ≤ publicFactor :=
    (member_le_sum _ _ (by simp [coefficients])).trans (Nat.le_succ _)
  exact (reusablePool_polylog n).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))

structure PublicParameters where
  threshold : ℕ
  heights : ℕ
  confidenceDenominator : ℕ
  trials : ℕ
  coordinateCap : ℕ
  slack : ℕ
  hop : ℕ
  coarseMass : ℕ
  fineMass : ℕ
  smallCutoff : ℕ
  bandCutoff : ℕ
  mstCutoff : ℕ
  savingAccuracyDenominator : ℕ
  bandAccuracyDenominator : ℕ
  mstAccuracyDenominator : ℕ
  reusablePool : ℕ
  savingSamples : ℕ
  bandSamples : ℕ
  mstSamples : ℕ
  savingProposalCap : ℕ
  bandProposalCap : ℕ
  mstProposalCap : ℕ

/-- Every field is executable natural arithmetic on `n,k`; radii, metrics, and estimates
are absent. The observed rational calibration enters only `incidenceBudget`. -/
def parameters (n k : ℕ) : PublicParameters :=
  ⟨t n, heightBudget n, betaDenom n, coverTrials n, privateCap n k, coverSlack n, hopBudget n,
    A n, AM n, B n, BQ n, BM n, xiSavingInv n, xiBandInv n, xiMInv n, NsPool n,
    meanSamples n (xiSavingInv n), meanSamples n (xiBandInv n), meanSamples n (xiMInv n),
    samplerCap n k (xiSavingInv n), samplerCap n k (xiBandInv n), samplerCap n k (xiMInv n)⟩

end SteinerUpperBound.EstimatorParameters

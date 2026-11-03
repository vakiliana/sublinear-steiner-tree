module

public import SteinerUpperBound.SavingEstimator.Resources.Polynomial.Stages

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open EstimatorParameters
open PortGraph.RuntimeAdapter.Averaged
open scoped Classical

theorem coveredBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    coveredBase kind n k ≤ monomial kind n (2 ^ 190) 14 54 := by
  let A := monomial kind n (2 ^ 186) 14 54
  have hhead : 32 * workUnit kind ≤ A :=
    (constant_le_monomial kind n 32).trans
      (monomial_mono kind n 32 (2 ^ 186) 0 14 0 54 (by norm_num) (by omega) (by omega))
  have hmean : meanBase kind n k ≤ A :=
    (meanBase_bound kind n k hk).trans
      (monomial_mono kind n (2 ^ 8) (2 ^ 186) 2 14 10 54 (by norm_num) (by omega) (by omega))
  have hpoint : meanSamples n (xiSavingInv n) * pointPublic kind n ≤ A := by
    have hh := (Nat.mul_le_mul_left _ (pointPublic_bound kind n)).trans
      (samples_mul_monomial kind n (2 ^ 15) 2 18)
    exact hh.trans (monomial_mono kind n (2 ^ 15) (2 ^ 186) 3 14 27 54
      (by norm_num) (by omega) (by omega))
  have hgeo : lazyFactor n * geometricPublic kind n ≤ monomial kind n (2 ^ 186) 13 45 := by
    have hh := (Nat.mul_le_mul_left _ (geometricPublic_bound kind n)).trans
      (lazy_mul_monomial kind n (2 ^ 26) 4 36)
    convert hh using 1 <;> norm_num
  have hvo : meanSamples n (xiSavingInv n) * (lazyFactor n * geometricPublic kind n) ≤ A :=
    (Nat.mul_le_mul_left _ hgeo).trans (samples_mul_monomial kind n (2 ^ 186) 13 45)
  have hlast : meanSamples n (xiSavingInv n) * (12 * workUnit kind) ≤ A := by
    have hh := (Nat.mul_le_mul_left _ (constant_le_monomial kind n 12)).trans
      (samples_mul_monomial kind n 12 0 0)
    exact hh.trans (monomial_mono kind n 12 (2 ^ 186) 1 14 9 54
      (by norm_num) (by omega) (by omega))
  have hh :
      32 * workUnit kind + meanBase kind n k +
        meanSamples n (xiSavingInv n) *
          (pointPublic kind n + lazyFactor n * geometricPublic kind n + 12 * workUnit kind) ≤
      16 * A := by
    nlinarith only [hhead, hmean, hpoint, hvo, hlast]
  change 32 * workUnit kind + meanBase kind n k +
    meanSamples n (xiSavingInv n) *
      (pointPublic kind n + lazyFactor n * geometricPublic kind n + 12 * workUnit kind) ≤ _
  exact hh.trans_eq (by dsimp only [A]; unfold monomial; norm_num; ring)

theorem largeBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    largeBase kind n k ≤ monomial kind n (2 ^ 192) 14 54 := by
  let A := monomial kind n (2 ^ 190) 14 54
  have hd : deletionBase kind n k ≤ A :=
    (deletionBase_bound kind n k hk).trans
      (monomial_mono kind n (2 ^ 12) (2 ^ 190) 2 14 3 54 (by norm_num) (by omega) (by omega))
  have hh : 4 * workUnit kind ≤ A :=
    (constant_le_monomial kind n 4).trans
      (monomial_mono kind n 4 (2 ^ 190) 0 14 0 54 (by norm_num) (by omega) (by omega))
  have hc : coveredBase kind n k ≤ A := coveredBase_bound kind n k hk
  have hs : deletionBase kind n k + 4 * workUnit kind + coveredBase kind n k ≤ 4 * A := by
    nlinarith only [hd, hh, hc]
  exact hs.trans_eq (by dsimp only [A]; unfold monomial; norm_num; ring)

theorem frontendBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    frontendBase kind n k ≤ monomial kind n (2 ^ 194) 14 54 := by
  let A := monomial kind n (2 ^ 192) 14 54
  have hs :
      samplerBudget kind (closed n (k + 1)).calibrationProposals (closed n (k + 1)).calibrationSamples ≤ A :=
    (calibrationBase_bound kind n k hk).trans
      (monomial_mono kind n (2 ^ 6) (2 ^ 192) 2 14 10 54 (by norm_num) (by omega) (by omega))
  have hh : 32 * workUnit kind ≤ A :=
    (constant_le_monomial kind n 32).trans
      (monomial_mono kind n 32 (2 ^ 192) 0 14 0 54 (by norm_num) (by omega) (by omega))
  have hm : smallBase kind n k ≤ A :=
    (smallBase_bound kind n k hk).trans
      (monomial_mono kind n (2 ^ 24) (2 ^ 192) 4 14 28 54 (by norm_num) (by omega) (by omega))
  have hl : largeBase kind n k ≤ A := largeBase_bound kind n k hk
  have hb : frontendBase kind n k ≤ 4 * A := by
    dsimp only [frontendBase]
    nlinarith only [hs, hh, hm, hl]
  exact hb.trans_eq (by dsimp only [A]; unfold monomial; norm_num; ring)

theorem rawBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    rawBase kind n k ≤ monomial kind n (2 ^ 200) 16 54 := by
  let A := monomial kind n (2 ^ 194) 14 54
  have hs :
      (configurationWork n (k + 1) (parameters n (k + 1)) + 12) * workUnit kind ≤ A :=
    (setup_bound kind n k).trans
      (monomial_mono kind n 16 (2 ^ 194) 1 14 1 54 (by norm_num) (by omega) (by omega))
  have hf : frontendBase kind n k ≤ A := frontendBase_bound kind n k hk
  have hh : rawBase kind n k ≤ 2 * A := by
    simpa only [rawBase, two_mul] using Nat.add_le_add hs hf
  have he : 2 * A = monomial kind n (2 ^ 195) 14 54 := by
    dsimp only [A]
    unfold monomial
    norm_num
    ring
  exact (hh.trans_eq he).trans
    (monomial_mono kind n (2 ^ 195) (2 ^ 200) 14 16 54 54 (by norm_num) (by omega) (le_refl _))

def resourceConstant : ℕ := 2 ^ 256 * magnitude ^ 32

def executionBudget (kind : CounterKind) (n : ℕ) : ℕ :=
  match kind with
  | .ordinary => workBudget resourceConstant 64 n
  | .positive => positiveBudget resourceConstant 64 n

theorem executionBudget_eq (kind : CounterKind) (n : ℕ) :
    executionBudget kind n = monomial kind n (2 ^ 256) 32 64 := by
  cases kind <;> simp only [executionBudget, workBudget, positiveBudget, resourceConstant] <;>
    unfold monomial <;> simp only [space] <;> ring

theorem resourceConstant_pos : 0 < resourceConstant := by
  have hh := magnitude_pos
  unfold resourceConstant
  positivity

theorem executionBudget_pos (kind : CounterKind) (n : ℕ) : 0 < executionBudget kind n := by
  rw [executionBudget_eq]
  unfold monomial
  have hm := magnitude_pos
  have hs := space_pos kind n
  have ht := t_pos n
  have he := ell_pos n
  positivity

theorem budgeted_rawBase (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    betaDenom n * rawBase kind n k ≤ executionBudget kind n := by
  have hh := Nat.mul_le_mul (denominator_bound n) (rawBase_bound kind n k hk)
  calc
    _ ≤ (magnitude * ell n ^ 9) * monomial kind n (2 ^ 200) 16 54 := hh
    _ = monomial kind n (2 ^ 200) 17 63 := by
      unfold monomial
      ring
    _ ≤ monomial kind n (2 ^ 256) 32 64 :=
      monomial_mono kind n (2 ^ 200) (2 ^ 256) 17 32 63 64 (by norm_num) (by omega) (by omega)
    _ = _ := (executionBudget_eq kind n).symm

end SteinerUpperBound.SavingEstimator.Resources

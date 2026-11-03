module

public import SteinerUpperBound.SavingEstimator.Resources.Budgets
public import SteinerUpperBound.SavingEstimator.Resources.Specification

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound EstimatorParameters
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical

@[irreducible] def magnitude : ℕ :=
  publicFactor + configurationFactor + poolLogFactor + poolFactor + 10000000

theorem magnitude_bounds :
    10000000 ≤ magnitude ∧ publicFactor ≤ magnitude ∧ configurationFactor ≤ magnitude ∧
      poolLogFactor ≤ magnitude ∧ poolFactor ≤ magnitude := by
  unfold magnitude
  omega

theorem magnitude_pos : 0 < magnitude := lt_of_lt_of_le (by decide) magnitude_bounds.1
theorem magnitude_one : 1 ≤ magnitude := magnitude_pos

def space : CounterKind → ℕ → ℕ
  | .ordinary, n => n + 1
  | .positive, _ => 1

theorem space_pos (kind : CounterKind) (n : ℕ) : 0 < space kind n := by cases kind <;> simp [space]
theorem workUnit_le_space (kind : CounterKind) (n : ℕ) : workUnit kind ≤ space kind n := by
  cases kind <;> simp [workUnit, space]

@[irreducible] def monomial (kind : CounterKind) (n C a d : ℕ) : ℕ :=
  C * magnitude ^ a * space kind n * t n * ell n ^ d

theorem monomial_coefficient (kind : CounterKind) (n C a d : ℕ) :
    monomial kind n C a d = C * monomial kind n 1 a d := by
  unfold monomial
  ring

theorem monomial_mono (kind : CounterKind) (n C C' a a' d d' : ℕ)
    (hC : C ≤ C') (ha : a ≤ a') (hd : d ≤ d') :
    monomial kind n C a d ≤ monomial kind n C' a' d' := by
  have hr := Nat.pow_le_pow_right magnitude_pos ha
  have he := ell_power_le n d d' hd
  have hm := Nat.mul_le_mul
    (Nat.mul_le_mul_right (space kind n * t n) (Nat.mul_le_mul hC hr)) he
  convert hm using 1 <;> unfold monomial <;> ring

theorem unit_le_monomial (kind : CounterKind) (n : ℕ) :
    1 ≤ monomial kind n 1 0 0 := by
  have hh := Nat.mul_le_mul (Nat.succ_le_of_lt (space_pos kind n)) (Nat.succ_le_of_lt (t_pos n))
  simpa only [monomial, pow_zero, Nat.mul_one, Nat.one_mul] using hh

theorem constant_le_monomial (kind : CounterKind) (n C : ℕ) :
    C * workUnit kind ≤ monomial kind n C 0 0 := by
  have hm := Nat.mul_le_mul_right (t n) (workUnit_le_space kind n)
  have ht := Nat.mul_le_mul_left (workUnit kind) (Nat.succ_le_of_lt (t_pos n))
  have hunit : workUnit kind ≤ space kind n * t n := by nlinarith only [hm, ht]
  have hh := Nat.mul_le_mul_left C hunit
  simpa only [monomial, pow_zero, Nat.mul_one, Nat.mul_assoc] using hh

theorem core_bound (n x : ℕ) (hx : x ∈ coreSizes n) : x ≤ magnitude * ell n ^ 9 := by
  exact (all_core_polylog n x hx).trans
    (Nat.mul_le_mul_right _ magnitude_bounds.2.1)

theorem cutoff_bound (n : ℕ) : B n ≤ magnitude * ell n ^ 9 :=
  core_bound n _ (by simp [coreSizes])

theorem samples_bound (n : ℕ) : meanSamples n (xiSavingInv n) ≤ magnitude * ell n ^ 9 :=
  core_bound n _ (by simp [coreSizes])

theorem denominator_bound (n : ℕ) : betaDenom n ≤ magnitude * ell n ^ 9 :=
  core_bound n _ (by simp [coreSizes])

theorem core_le_monomial (kind : CounterKind) (n x : ℕ) (hx : x ≤ magnitude * ell n ^ 9) :
    x ≤ monomial kind n 1 1 9 := by
  have hunit : 1 ≤ space kind n * t n :=
    Nat.mul_le_mul (Nat.succ_le_of_lt (space_pos kind n)) (Nat.succ_le_of_lt (t_pos n))
  have hh := Nat.mul_le_mul_left (magnitude * ell n ^ 9) hunit
  calc
    x ≤ magnitude * ell n ^ 9 := hx
    _ ≤ (magnitude * ell n ^ 9) * (space kind n * t n) := by simpa only [Nat.mul_one] using hh
    _ = _ := by unfold monomial; ring

theorem cutoff_add_bound (n : ℕ) : B n + 2 ≤ 2 * magnitude * ell n ^ 9 := by
  have hm : 2 ≤ magnitude := (by decide : 2 ≤ 10000000).trans magnitude_bounds.1
  have he : 1 ≤ ell n ^ 9 := one_le_pow₀ (ell_ge_one n)
  have hh := Nat.mul_le_mul hm he
  nlinarith only [cutoff_bound n, hh]

theorem largestSize_polynomial (n : ℕ) :
    largestSize n ≤ (6 * magnitude + 3) * (n + 2) ^ 12 := by
  have hb : B n ≤ magnitude * (n + 2) ^ 9 :=
    (cutoff_bound n).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (ell_le n) 9))
  have hm : n * ((4 * n + 2) * B n * n) ≤
      (n + 2) * (4 * (n + 2) * (magnitude * (n + 2) ^ 9) * (n + 2)) := by gcongr <;> omega
  have hsmall : n + 2 ≤ (n + 2) ^ 12 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < n + 2) (by decide : 1 ≤ 12)
  dsimp only [largestSize, publicSize]
  nlinarith only [hm, hsmall]

theorem largestLog_bound (n : ℕ) : largestLog n ≤ 7 * magnitude * ell n := by
  have hh := log_of_polynomial_bound n (largestSize n) (6 * magnitude + 3) 12 (largestSize_polynomial n)
  have hc : 6 * magnitude + 3 + 12 + 1 ≤ 7 * magnitude := by have := magnitude_bounds.1; omega
  simp only [largestLog, Nat.log2_eq_log_two] at hh ⊢
  exact hh.trans (Nat.mul_le_mul_right _ hc)

theorem lazyFactor_bound (n : ℕ) :
    lazyFactor n ≤ 2 ^ 160 * magnitude ^ 9 * ell n ^ 9 := by
  have hh := Nat.mul_le_mul_left (2 ^ 128) (Nat.pow_le_pow_left (largestLog_bound n) 9)
  have hc : 2 ^ 128 * 7 ^ 9 ≤ 2 ^ 160 := by norm_num
  have hm := Nat.mul_le_mul_right (magnitude ^ 9 * ell n ^ 9) hc
  dsimp only [lazyFactor]
  nlinarith only [hh, hm]

theorem geometricPublic_bound (kind : CounterKind) (n : ℕ) :
    geometricPublic kind n ≤ monomial kind n (2 ^ 26) 4 36 := by
  have hb := cutoff_add_bound n
  have he9 : 1 ≤ ell n ^ 9 := one_le_pow₀ (ell_ge_one n)
  cases kind
  · calc
      geometricPublic .ordinary n ≤ 2400000 * (n + 1) * t n * (2 * magnitude * ell n ^ 9) ^ 4 := by
        dsimp only [geometricPublic]
        gcongr
      _ ≤ _ := by
        have hc : 2400000 * 16 ≤ 2 ^ 26 := by norm_num
        have hm := Nat.mul_le_mul_right (magnitude ^ 4 * (n + 1) * t n * ell n ^ 36) hc
        convert hm using 1 <;> norm_num only [monomial, space] <;> ring
  · have hb3 : (B n + 2) ^ 3 ≤ (B n + 2) ^ 4 :=
      Nat.pow_le_pow_right (by omega) (by decide)
    calc
      geometricPublic .positive n ≤ 400 * t n * (2 * magnitude * ell n ^ 9) ^ 4 := by
        dsimp only [geometricPublic]
        exact Nat.mul_le_mul_left _ (hb3.trans (Nat.pow_le_pow_left hb 4))
      _ ≤ _ := by
        have hc : 400 * 16 ≤ 2 ^ 26 := by norm_num
        have hm := Nat.mul_le_mul_right (magnitude ^ 4 * t n * ell n ^ 36) hc
        convert hm using 1 <;> norm_num only [monomial, space] <;> ring

theorem pointPublic_bound (kind : CounterKind) (n : ℕ) :
    pointPublic kind n ≤ monomial kind n (2 ^ 15) 2 18 := by
  have hb := cutoff_add_bound n
  have ht1 : 1 ≤ t n := t_pos n
  cases kind
  · calc
      pointPublic .ordinary n ≤ 4200 * (n + 1) * (2 * magnitude * ell n ^ 9) ^ 2 := by
        dsimp only [pointPublic]
        gcongr
      _ ≤ 4200 * (n + 1) * (2 * magnitude * ell n ^ 9) ^ 2 * t n := by
        exact Nat.le_mul_of_pos_right _ (t_pos n)
      _ ≤ _ := by
        have hc : 4200 * 4 ≤ 2 ^ 15 := by norm_num
        have hm := Nat.mul_le_mul_right (magnitude ^ 2 * (n + 1) * t n * ell n ^ 18) hc
        convert hm using 1 <;> norm_num only [monomial, space] <;> ring
  · have hsmall : B n + 1 ≤ magnitude * ell n ^ 9 + magnitude * ell n ^ 9 := by
      have hunit : 1 ≤ magnitude * ell n ^ 9 :=
        Nat.mul_le_mul magnitude_one (one_le_pow₀ (ell_ge_one n))
      nlinarith only [cutoff_bound n, hunit]
    have hc := core_le_monomial .positive n (B n) (cutoff_bound n)
    have hmono := monomial_mono .positive n 1 (2 ^ 14) 1 2 9 18 (by norm_num) (by omega) (by omega)
    have hconst := unit_le_monomial .positive n
    have hconst' := monomial_mono .positive n 1 (2 ^ 14) 0 2 0 18 (by norm_num) (by omega) (by omega)
    have hh := Nat.add_le_add (hc.trans hmono) (hconst.trans hconst')
    dsimp only [pointPublic]
    convert hh using 1 <;> unfold monomial <;> norm_num <;> ring

end SteinerUpperBound.SavingEstimator.Resources

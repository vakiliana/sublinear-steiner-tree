module

public import SteinerUpperBound.ReusableSample.Correctness

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

noncomputable def logBudget (t : ℕ) (β : ℝ) : ℝ :=
  1 + Real.log (512 * (t : ℝ) / β)

noncomputable def rowBudget (n t : ℕ) (β : ℝ) : ℝ :=
  1 + Real.log (128 * ((n : ℝ) + 1) * t / β)

/-- Choosing the exponential increment first makes the stability constants exact. -/
noncomputable def bandwidth (t : ℕ) (β : ℝ) : ℝ :=
  1 / Real.log (1 + 1 / (64 * logBudget t β))

noncomputable def sampleSize (n t : ℕ) (β : ℝ) : ℕ :=
  ⌈512 * (t : ℝ) * logBudget t β * rowBudget n t β⌉₊

theorem logBudget_ge_one (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    1 ≤ logBudget t β := by
  have ht' : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hr : 1 ≤ 512 * (t : ℝ) / β := (le_div_iff₀ hβ).mpr (by nlinarith)
  have hlog := Real.log_nonneg hr
  dsimp [logBudget]
  linarith

theorem rowBudget_ge_one (n t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    1 ≤ rowBudget n t β := by
  have ht' : 1 ≤ (t : ℝ) := by exact_mod_cast ht
  have hp : 1 ≤ ((n : ℝ) + 1) * t := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n) (show 0 ≤ (t : ℝ) by positivity)]
  have hr : 1 ≤ 128 * ((n : ℝ) + 1) * t / β := (le_div_iff₀ hβ).mpr (by nlinarith)
  have hlog := Real.log_nonneg hr
  dsimp [rowBudget]
  linarith

private theorem inverse_log_bounds (L : ℝ) (hL : 1 ≤ L) :
    0 < 1 / Real.log (1 + 1 / (64 * L)) ∧
      64 * L ≤ 1 / Real.log (1 + 1 / (64 * L)) ∧
      1 / Real.log (1 + 1 / (64 * L)) ≤ 128 * L := by
  let q := 1 / (64 * L)
  have hL' : 0 < L := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hq₁ : q ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * L)).mpr
    nlinarith
  have hlog : 0 < Real.log (1 + q) := Real.log_pos (by linarith)
  have hupper : Real.log (1 + q) ≤ q := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + q)
    linarith
  have hlower : q / 2 ≤ Real.log (1 + q) := by
    have hh := Real.le_log_one_add_of_nonneg hq.le
    have hfrac : q / 2 ≤ 2 * q / (q + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < q + 2)).mpr
      nlinarith [mul_nonneg hq.le (show 0 ≤ 2 - q by linarith)]
    exact hfrac.trans hh
  have hid : 64 * L * q = 1 := by
    dsimp [q]
    field_simp
  refine ⟨one_div_pos.mpr hlog, ?_, ?_⟩
  · apply (le_div_iff₀ hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 64 * L)]
  · apply (div_le_iff₀ hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlower (by positivity : 0 ≤ 128 * L)]

theorem bandwidth_bounds (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    0 < bandwidth t β ∧
      64 * logBudget t β ≤ bandwidth t β ∧
      bandwidth t β ≤ 128 * logBudget t β :=
  inverse_log_bounds _ (logBudget_ge_one t ht β hβ hβ')

theorem increment_bandwidth (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    increment (bandwidth t β) = 1 / (64 * logBudget t β) := by
  have hL := logBudget_ge_one t ht β hβ hβ'
  have hpos : 0 < 1 + 1 / (64 * logBudget t β) := by positivity
  simp only [increment, bandwidth, one_div_one_div, Real.exp_log hpos]
  ring

theorem sampleSize_pos (n t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    0 < sampleSize n t β := by
  have hL := logBudget_ge_one t ht β hβ hβ'
  have hM := rowBudget_ge_one n t ht β hβ hβ'
  apply Nat.ceil_pos.mpr
  positivity

theorem sampleSize_bound (n t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    (sampleSize n t β : ℝ) ≤
      512 * (t : ℝ) * logBudget t β * rowBudget n t β + 1 := by
  have hL := logBudget_ge_one t ht β hβ hβ'
  have hM := rowBudget_ge_one n t ht β hβ hβ'
  exact (Nat.ceil_lt_add_one (by positivity)).le

private theorem exp_neg_budget (x : ℝ) (hx : 0 < x) :
    Real.exp (-(1 + Real.log x)) ≤ 1 / x := by
  calc
    _ ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log hx, one_div]

private theorem bandwidth_stability (t : ℕ) (ht : 0 < t) (β : ℝ)
    (hβ : 0 < β) (hβ' : β < 1 / 4) :
    (1 + increment (bandwidth t β)) *
        Real.exp (increment (bandwidth t β) * logBudget t β) ≤ 4 / 3 ∧
      (1 + increment (bandwidth t β)) * Real.exp (-logBudget t β) ≤ β / (128 * t) := by
  let L := logBudget t β
  let q := 1 / (64 * L)
  have hL : 1 ≤ L := logBudget_ge_one t ht β hβ hβ'
  have hL' : 0 < L := by linarith
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₁ : q ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < 64 * L)).mpr
    nlinarith
  have hqL : q * L = 1 / 64 := by
    dsimp [q]
    field_simp
  have he : Real.exp (1 / 64) ≤ 64 / 63 := by
    have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-(1 / 64 : ℝ)))
      (Real.exp_pos (1 / 64)).le
    have hh : Real.exp (-(1 / 64 : ℝ)) * Real.exp (1 / 64) = 1 := by
      rw [← Real.exp_add]
      norm_num
    rw [hh] at h
    nlinarith
  have hd : Real.exp (-L) ≤ β / (512 * t) := by
    have hratio : 0 < 512 * (t : ℝ) / β := by positivity
    have hh := exp_neg_budget _ hratio
    have heq : 1 / (512 * (t : ℝ) / β) = β / (512 * t) := by field_simp
    exact hh.trans_eq heq
  rw [increment_bandwidth t ht β hβ hβ']
  change (1 + q) * Real.exp (q * L) ≤ 4 / 3 ∧
    (1 + q) * Real.exp (-L) ≤ β / (128 * t)
  constructor
  · rw [hqL]
    calc
      _ ≤ (65 / 64) * Real.exp (1 / 64) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ (65 / 64) * (64 / 63) := mul_le_mul_of_nonneg_left he (by norm_num)
      _ ≤ _ := by norm_num
  · calc
      _ ≤ (1 + q) * (β / (512 * t)) := mul_le_mul_of_nonneg_left hd (by linarith)
      _ ≤ (65 / 64) * (β / (512 * t)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ _ := by
        have hh : 0 ≤ β / t := by positivity
        convert mul_le_mul_of_nonneg_right
          (by norm_num : (65 / 64 : ℝ) / 512 ≤ 1 / 128) hh using 1 <;> ring

private theorem sampleSize_margins (n t : ℕ) (ht : 0 < t) (β : ℝ)
    (hβ : 0 < β) (hβ' : β < 1 / 4) :
    2 * n * Real.exp (-(sampleSize n t β / (4 * t)) / bandwidth t β) ≤ β / (64 * t) := by
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hL := logBudget_ge_one t ht β hβ hβ'
  have hM := rowBudget_ge_one n t ht β hβ hβ'
  have hb := bandwidth_bounds t ht β hβ hβ'
  have hNs : 4 * (t : ℝ) * bandwidth t β * rowBudget n t β ≤ sampleSize n t β := by
    have hh := mul_le_mul_of_nonneg_left hb.2.2
      (show 0 ≤ 4 * (t : ℝ) * rowBudget n t β by positivity)
    have hc := Nat.le_ceil (512 * (t : ℝ) * logBudget t β * rowBudget n t β)
    dsimp [sampleSize]
    nlinarith
  have hratio : rowBudget n t β ≤ (sampleSize n t β / (4 * t)) / bandwidth t β := by
    apply (le_div_iff₀ hb.1).mpr
    apply (le_div_iff₀ (by positivity : 0 < 4 * (t : ℝ))).mpr
    nlinarith
  have he : Real.exp (-(sampleSize n t β / (4 * t)) / bandwidth t β) ≤
      β / (128 * ((n : ℝ) + 1) * t) := by
    have h₀ := Real.exp_le_exp.mpr (neg_le_neg hratio)
    have h₁ := exp_neg_budget (128 * ((n : ℝ) + 1) * t / β) (by positivity)
    have hid : 1 / (128 * ((n : ℝ) + 1) * t / β) =
        β / (128 * ((n : ℝ) + 1) * t) := by field_simp
    have h₀' : Real.exp (-(sampleSize n t β / (4 * t)) / bandwidth t β) ≤
        Real.exp (-rowBudget n t β) := by simpa only [neg_div] using h₀
    exact h₀'.trans (h₁.trans_eq hid)
  calc
    _ ≤ 2 * n * (β / (128 * ((n : ℝ) + 1) * t)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((n : ℝ) / (n + 1)) * (β / (64 * t)) := by
      field_simp
      ring
    _ ≤ _ := by
      have hh : (n : ℝ) / (n + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh
        (show 0 ≤ β / (64 * t) by positivity)

/-- The reusable-sample lemma, with no stability or generalization assumptions.
The sample bound is `sampleSize_bound`, and `bandwidth_bounds` gives its
logarithmic bandwidth. Neither parameter depends on the universe size. -/
theorem reusable_sample {U : Type*} [Fintype U] [Nonempty U]
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (ht : 0 < t)
    (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) :
    1 - β ≤
      (run (bandwidth t β) (sampleSize n t β) t R).prob {T | Specification R t T} ∧
    (∀ T, 0 < (run (bandwidth t β) (sampleSize n t β) t R).mass T → acceptances T ≤ t) ∧
    (∀ (X : Fin (sampleSize n t β) → U) (T : Fin n → Bool),
      queryWork R t X T ≤ n * sampleSize n t β) ∧
    (sampleSize n t β : ℝ) ≤
      512 * (t : ℝ) * logBudget t β * rowBudget n t β + 1 := by
  have hband := bandwidth_bounds t ht β hβ hβ'
  have hstab := bandwidth_stability t ht β hβ hβ'
  have hcorrect := correctness (bandwidth t β) hband.1 (sampleSize n t β) t
    (sampleSize_pos n t ht β hβ hβ') ht R β hβ (logBudget t β)
    (by linarith [logBudget_ge_one t ht β hβ hβ'])
    hstab.1 hstab.2 (sampleSize_margins n t ht β hβ hβ')
  refine ⟨by linarith, fun T hT => run_support _ _ _ R T hT,
    fun X T => queryWork_le R t X T, sampleSize_bound n t ht β hβ hβ'⟩

/-- The bandwidth for an arbitrary upper bound on the logarithmic budget.
This is an analytic specification; `logistic_integer_rule` eliminates its
logarithm and exponential from every transition of the integer calibration. -/
noncomputable def calibratedBandwidth (L : ℝ) : ℝ :=
  1 / Real.log (1 + 1 / (64 * L))

theorem calibratedBandwidth_bounds (L : ℝ) (hL : 1 ≤ L) :
    0 < calibratedBandwidth L ∧ 64 * L ≤ calibratedBandwidth L ∧
      calibratedBandwidth L ≤ 128 * L :=
  inverse_log_bounds L hL

theorem calibratedBandwidth_le (L : ℝ) (hL : 1 ≤ L) :
    calibratedBandwidth L ≤ 64 * L + 1 := by
  have hL' : 0 < L := by linarith
  have hz : 1 < 1 + 1 / (64 * L) := by
    have hq : 0 < 1 / (64 * L) := by positivity
    linarith
  have hlog := Real.log_pos hz
  have hlo := Real.one_sub_inv_le_log_of_pos (lt_trans zero_lt_one hz)
  have he : 1 - (1 + 1 / (64 * L))⁻¹ = 1 / (64 * L + 1) := by
    field_simp
    ring
  rw [he] at hlo
  apply (div_le_iff₀ hlog).mpr
  have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 64 * L + 1 by positivity)
  have hc : (64 * L + 1) * (1 / (64 * L + 1)) = 1 := by field_simp
  rw [hc] at hh
  linarith

theorem increment_calibratedBandwidth (L : ℝ) (hL : 1 ≤ L) :
    increment (calibratedBandwidth L) = 1 / (64 * L) := by
  have hz : 0 < 1 + 1 / (64 * L) := by positivity
  simp only [increment, calibratedBandwidth, one_div_one_div, Real.exp_log hz]
  ring

private theorem calibrated_stability (t : ℕ) (ht : 0 < t) (β : ℝ)
    (hβ : 0 < β) (hβ' : β < 1 / 4) (L : ℝ) (hL : logBudget t β ≤ L) :
    (1 + increment (calibratedBandwidth L)) *
        Real.exp (increment (calibratedBandwidth L) * logBudget t β) ≤ 4 / 3 ∧
      (1 + increment (calibratedBandwidth L)) * Real.exp (-logBudget t β) ≤
        β / (128 * t) := by
  have hL₀ := logBudget_ge_one t ht β hβ hβ'
  have hL₁ : 1 ≤ L := hL₀.trans hL
  have hq : increment (calibratedBandwidth L) ≤ increment (bandwidth t β) := by
    rw [increment_calibratedBandwidth L hL₁, increment_bandwidth t ht β hβ hβ']
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hq₀ : 0 ≤ increment (calibratedBandwidth L) := by
    rw [increment_calibratedBandwidth L hL₁]
    positivity
  have hh := bandwidth_stability t ht β hβ hβ'
  constructor
  · calc
      _ ≤ (1 + increment (bandwidth t β)) *
          Real.exp (increment (calibratedBandwidth L) * logBudget t β) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ ≤ (1 + increment (bandwidth t β)) *
          Real.exp (increment (bandwidth t β) * logBudget t β) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hq (by linarith)))
          (by linarith)
      _ ≤ _ := hh.1
  · exact (mul_le_mul_of_nonneg_right (show 1 + increment (calibratedBandwidth L) ≤
        1 + increment (bandwidth t β) by linarith) (Real.exp_pos _).le).trans hh.2

private theorem calibrated_margins (n t Ns : ℕ) (ht : 0 < t) (β : ℝ)
    (hβ : 0 < β) (hβ' : β < 1 / 4) (L M : ℝ)
    (hL : logBudget t β ≤ L) (hM : rowBudget n t β ≤ M)
    (hNs : 512 * (t : ℝ) * L * M ≤ Ns) :
    2 * n * Real.exp (-(Ns / (4 * t)) / calibratedBandwidth L) ≤ β / (64 * t) := by
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hL₀ := logBudget_ge_one t ht β hβ hβ'
  have hM₀ := rowBudget_ge_one n t ht β hβ hβ'
  have hL₁ : 1 ≤ L := hL₀.trans hL
  have hb := calibratedBandwidth_bounds L (hL₀.trans hL)
  have hs : 4 * (t : ℝ) * calibratedBandwidth L * rowBudget n t β ≤ Ns := by
    have hh := mul_le_mul_of_nonneg_left hb.2.2
      (show 0 ≤ 4 * (t : ℝ) * rowBudget n t β by positivity)
    have hh' := mul_le_mul_of_nonneg_left hM (show 0 ≤ 512 * (t : ℝ) * L by positivity)
    nlinarith
  have hr : rowBudget n t β ≤ (Ns / (4 * t)) / calibratedBandwidth L := by
    apply (le_div_iff₀ hb.1).mpr
    apply (le_div_iff₀ (by positivity : 0 < 4 * (t : ℝ))).mpr
    nlinarith
  have he : Real.exp (-(Ns / (4 * t)) / calibratedBandwidth L) ≤
      β / (128 * ((n : ℝ) + 1) * t) := by
    have he₀ : Real.exp (-(Ns / (4 * t)) / calibratedBandwidth L) ≤
        Real.exp (-rowBudget n t β) := by
      simpa only [neg_div] using Real.exp_le_exp.mpr (neg_le_neg hr)
    have he₁ := exp_neg_budget (128 * ((n : ℝ) + 1) * t / β) (by positivity)
    have hid : 1 / (128 * ((n : ℝ) + 1) * t / β) =
        β / (128 * ((n : ℝ) + 1) * t) := by field_simp
    exact he₀.trans (he₁.trans_eq hid)
  calc
    _ ≤ 2 * n * (β / (128 * ((n : ℝ) + 1) * t)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((n : ℝ) / (n + 1)) * (β / (64 * t)) := by field_simp; ring
    _ ≤ _ := by
      have hh : (n : ℝ) / (n + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hh
        (show 0 ≤ β / (64 * t) by positivity)

/-- General calibration: the budgets may be arbitrary upper bounds, and the
number of records may be any integer above the displayed product. -/
theorem reusable_sample_of_budgets {U : Type*} [Fintype U] [Nonempty U]
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (ht : 0 < t)
    (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (L M : ℝ)
    (hL : logBudget t β ≤ L) (hM : rowBudget n t β ≤ M)
    (Ns : ℕ) (hNs : 512 * (t : ℝ) * L * M ≤ Ns) :
    1 - β ≤ (run (calibratedBandwidth L) Ns t R).prob {T | Specification R t T} ∧
    (∀ T, 0 < (run (calibratedBandwidth L) Ns t R).mass T → acceptances T ≤ t) ∧
    (∀ (X : Fin Ns → U) (T : Fin n → Bool), queryWork R t X T ≤ n * Ns) := by
  have hL₀ := logBudget_ge_one t ht β hβ hβ'
  have hM₀ := rowBudget_ge_one n t ht β hβ hβ'
  have hL₁ : 1 ≤ L := hL₀.trans hL
  have hM₁ : 1 ≤ M := hM₀.trans hM
  have hNs' : 0 < Ns := by
    have hh : 0 < (Ns : ℝ) := lt_of_lt_of_le (by positivity) hNs
    exact_mod_cast hh
  have hs := calibrated_stability t ht β hβ hβ' L hL
  have hc := correctness (calibratedBandwidth L) (calibratedBandwidth_bounds L hL₁).1 Ns t
    hNs' ht R β hβ (logBudget t β) (by linarith) hs.1 hs.2
    (calibrated_margins n t Ns ht β hβ hβ' L M hL hM hNs)
  exact ⟨by linarith, fun T hT => run_support _ _ _ R T hT, fun X T => queryWork_le R t X T⟩

/-- This calibration is computed entirely with integer arithmetic. -/
def integerSamples (t Lbar Mbar : ℕ) : ℕ := 512 * t * Lbar * Mbar

theorem integerSamples_dvd (t Lbar Mbar : ℕ) : t ∣ integerSamples t Lbar Mbar := by
  refine ⟨512 * Lbar * Mbar, ?_⟩
  dsimp [integerSamples]
  ring

theorem integerSamples_div (t Lbar Mbar : ℕ) (ht : 0 < t) :
    integerSamples t Lbar Mbar / t = 512 * Lbar * Mbar := by
  apply Nat.div_eq_of_eq_mul_left ht
  dsimp [integerSamples]
  ring

theorem integer_reusable_sample {U : Type*} [Fintype U] [Nonempty U]
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (ht : 0 < t)
    (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (Lbar Mbar : ℕ)
    (hL : logBudget t β ≤ Lbar) (hM : rowBudget n t β ≤ Mbar) :
    1 - β ≤ (run (calibratedBandwidth Lbar) (integerSamples t Lbar Mbar) t R).prob
      {T | Specification R t T} ∧
    (∀ T, 0 < (run (calibratedBandwidth Lbar) (integerSamples t Lbar Mbar) t R).mass T →
      acceptances T ≤ t) ∧
    (∀ (X : Fin (integerSamples t Lbar Mbar) → U) (T : Fin n → Bool),
      queryWork R t X T ≤ n * integerSamples t Lbar Mbar) := by
  apply reusable_sample_of_budgets R t ht β hβ hβ' Lbar Mbar hL hM
  simp only [integerSamples, Nat.cast_mul, Nat.cast_ofNat, le_refl]

private theorem log_le_of_doubling (x : ℝ) (hx : 0 < x) (k : ℕ) (hk : x ≤ (2 : ℝ) ^ k) :
    Real.log x ≤ k := by
  have hh := Real.log_le_log hx hk
  rw [Real.log_pow] at hh
  have ht : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith

theorem logBudget_le_of_doubling (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β)
    (k : ℕ) (hk : 512 * (t : ℝ) ≤ β * (2 : ℝ) ^ k) :
    logBudget t β ≤ (k + 1 : ℕ) := by
  have hh := log_le_of_doubling (512 * (t : ℝ) / β) (by positivity) k
    ((div_le_iff₀ hβ).mpr (by nlinarith))
  dsimp [logBudget]
  push_cast
  linarith

theorem rowBudget_le_of_doubling (n t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β)
    (k : ℕ) (hk : 128 * ((n : ℝ) + 1) * t ≤ β * (2 : ℝ) ^ k) :
    rowBudget n t β ≤ (k + 1 : ℕ) := by
  have hh := log_le_of_doubling (128 * ((n : ℝ) + 1) * t / β) (by positivity) k
    ((div_le_iff₀ hβ).mpr (by nlinarith))
  dsimp [rowBudget]
  push_cast
  linarith

theorem integer_reusable_sample_of_doubling {U : Type*} [Fintype U] [Nonempty U]
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (ht : 0 < t)
    (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (k ℓ : ℕ)
    (hk : 512 * (t : ℝ) ≤ β * (2 : ℝ) ^ k)
    (hℓ : 128 * ((n : ℝ) + 1) * t ≤ β * (2 : ℝ) ^ ℓ) :
    1 - β ≤ (run (calibratedBandwidth (↑(k + 1 : ℕ))) (integerSamples t (k + 1) (ℓ + 1)) t R).prob
      {T | Specification R t T} ∧
    (∀ T, 0 < (run (calibratedBandwidth (↑(k + 1 : ℕ))) (integerSamples t (k + 1) (ℓ + 1)) t R).mass T →
      acceptances T ≤ t) ∧
    (∀ (X : Fin (integerSamples t (k + 1) (ℓ + 1)) → U) (T : Fin n → Bool),
      queryWork R t X T ≤ n * integerSamples t (k + 1) (ℓ + 1)) :=
  integer_reusable_sample R t ht β hβ hβ' (k + 1) (ℓ + 1)
    (logBudget_le_of_doubling t ht β hβ k hk) (rowBudget_le_of_doubling n t ht β hβ ℓ hℓ)

end SteinerUpperBound.ReusableSample

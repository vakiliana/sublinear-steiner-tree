module

public import SteinerLowerBound.MetricComparison.Observation

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical

theorem sqrt_difference_le_chi {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) ^ 2 / b := by
  have hid : a - b =
      (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  have hsum : b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb.le,
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  apply (le_div_iff₀ hb).mpr
  have h := mul_le_mul_of_nonneg_left hsum
    (sq_nonneg (Real.sqrt a - Real.sqrt b))
  rw [hid]
  nlinarith

theorem bernoulli_sqrt_sum (x y : ℝ)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1) :
    (Real.sqrt x - Real.sqrt y) ^ 2 +
      (Real.sqrt (1 - x) - Real.sqrt (1 - y)) ^ 2 =
        2 * (1 - Law.affinity (Law.bernoulli x hx₀ hx₁) (Law.bernoulli y hy₀ hy₁)) := by
  have h := Law.sqrt_difference_sum (Law.bernoulli x hx₀ hx₁) (Law.bernoulli y hy₀ hy₁)
  simpa only [Fintype.sum_bool, Law.bernoulli_mass_true, Law.bernoulli_mass_false] using h

theorem bernoulli_chi_bound (x y : ℝ)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 < y) (hy₁ : y < 1) :
    2 * (1 - Law.affinity (Law.bernoulli x hx₀ hx₁)
      (Law.bernoulli y hy₀.le hy₁.le)) ≤
      (x - y) ^ 2 / y + (x - y) ^ 2 / (1 - y) := by
  rw [← bernoulli_sqrt_sum]
  have h := sqrt_difference_le_chi (sub_nonneg.mpr hx₁) (sub_pos.mpr hy₁)
  have he : (1 - x - (1 - y)) ^ 2 = (x - y) ^ 2 := by ring
  rw [he] at h
  exact add_le_add (sqrt_difference_le_chi hx₀ hy₀) h

theorem bernoulli_additive_bound (x y m R D : ℝ)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
    (hm : 1 ≤ m) (hR : 0 < R) (hD : 0 ≤ D)
    (hyl : 1 / (4 * m) ≤ y) (hyu : y ≤ 1 / 2)
    (hdiff : |x - y| ≤ D / (R * m)) :
    1 - Law.affinity (Law.bernoulli x hx₀ hx₁) (Law.bernoulli y hy₀ hy₁) ≤
      8 * D ^ 2 / (m * R ^ 2) := by
  have hm₀ : 0 < m := by linarith
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hyl
  have hy' : y < 1 := by linarith
  have hh := bernoulli_chi_bound x y hx₀ hx₁ hy hy'
  have hd : (x - y) ^ 2 ≤ (D / (R * m)) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (x - y)) hdiff
    simpa only [← sq, sq_abs] using h
  have h₁ : (x - y) ^ 2 / y ≤ 4 * m * (D / (R * m)) ^ 2 := by
    apply (div_le_iff₀ hy).mpr
    have hl := (div_le_iff₀ (by positivity : 0 < 4 * m)).mp hyl
    have hmul := mul_le_mul_of_nonneg_left hl (sq_nonneg (D / (R * m)))
    nlinarith
  have h₂ : (x - y) ^ 2 / (1 - y) ≤ 2 * (D / (R * m)) ^ 2 := by
    apply (div_le_iff₀ (sub_pos.mpr hy')).mpr
    nlinarith [sq_nonneg (D / (R * m))]
  have he : 8 * D ^ 2 / (m * R ^ 2) = 8 * m * (D / (R * m)) ^ 2 := by
    field_simp
    <;> ring
  rw [he]
  nlinarith [mul_nonneg (sub_nonneg.mpr hm) (sq_nonneg (D / (R * m)))]

theorem bernoulli_relative_bound (x y r : ℝ)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hy₀ : 0 ≤ y) (hy₁ : y ≤ 1)
    (hr : 0 ≤ r) (hyu : y ≤ 1 / 2) (hdiff : |x - y| ≤ r * y) :
    1 - Law.affinity (Law.bernoulli x hx₀ hx₁) (Law.bernoulli y hy₀ hy₁) ≤
      r ^ 2 * y := by
  by_cases hy : y = 0
  · have hx : x = 0 := by
      rw [hy, mul_zero] at hdiff
      have h := (abs_le.mp hdiff).2
      linarith
    subst y
    subst x
    simp
  · have hypos : 0 < y := lt_of_le_of_ne hy₀ (Ne.symm hy)
    have hylt : y < 1 := by linarith
    have hh := bernoulli_chi_bound x y hx₀ hx₁ hypos hylt
    have hd : (x - y) ^ 2 ≤ r ^ 2 * y ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (x - y)) hdiff
      nlinarith [sq_abs (x - y)]
    have h₁ : (x - y) ^ 2 / y ≤ r ^ 2 * y := by
      apply (div_le_iff₀ hypos).mpr
      nlinarith
    have h₂ : (x - y) ^ 2 / (1 - y) ≤ r ^ 2 * y := by
      apply (div_le_iff₀ (sub_pos.mpr hylt)).mpr
      have hmul := mul_le_mul_of_nonneg_left
        (show 2 * y ≤ 1 by linarith) (mul_nonneg (sq_nonneg r) hy₀)
      nlinarith
    linarith

theorem ratio_difference_bound (N N₀ S F m R A : ℝ)
    (hF : 0 < F) (hS : F / 2 ≤ S) (hm : 0 < m) (hR : 0 < R) (hA : 0 ≤ A)
    (hN₀ : 0 ≤ N₀) (hNu : N₀ / F ≤ 4 / m)
    (hden : |S - F| ≤ A * F / R)
    (hnum : |N - N₀| ≤ A * F / (R * m)) :
    |N / S - N₀ / F| ≤ 10 * A / (R * m) := by
  have hS₀ : 0 < S := by linarith
  have hid : N / S - N₀ / F =
      (F * (N - N₀) - N₀ * (S - F)) / (S * F) := by field_simp; ring
  rw [hid, abs_div, abs_of_pos (mul_pos hS₀ hF)]
  apply (div_le_iff₀ (mul_pos hS₀ hF)).mpr
  have habs : |F * (N - N₀) - N₀ * (S - F)| ≤
      F * |N - N₀| + N₀ * |S - F| := by
    simpa only [abs_mul, abs_of_pos hF, abs_of_nonneg hN₀] using
      abs_sub (F * (N - N₀)) (N₀ * (S - F))
  have hNbound : N₀ ≤ 4 * F / m := by
    have hh := (div_le_iff₀ hF).mp hNu
    nlinarith [show (4 / m) * F = 4 * F / m by ring]
  have hmain :
      F * |N - N₀| + N₀ * |S - F| ≤ 5 * A * F ^ 2 / (R * m) := by
    calc
      _ ≤ F * (A * F / (R * m)) + (4 * F / m) * (A * F / R) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hnum hF.le)
          (mul_le_mul hNbound hden (abs_nonneg _) (by positivity))
      _ = _ := by ring
  apply habs.trans (hmain.trans _)
  have hh := mul_le_mul_of_nonneg_left (show F ≤ 2 * S by linarith)
    (show 0 ≤ 5 * A * F / (R * m) by positivity)
  convert hh using 1 <;> ring

end SteinerLowerBound.MetricComparison

module

public import SteinerUpperBound.LocalAccess

@[expose] public section

namespace SteinerUpperBound.AccessAccounts

open LocalAccess

theorem partnerBudget_le (n k b B : ℕ) (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) :
    partnerBudget n k b B ≤ 1000 * (n + 1) * (B + 2) ^ 2 := by
  have hscale := Nat.mul_le_mul_right ((B + 2) ^ 2) (Nat.add_le_add_right hk 1)
  have hlin : b ≤ b ^ 2 + 1 := by nlinarith [sq_nonneg ((b : ℝ) - 1)]
  unfold partnerBudget locateBudget frameBudget mutualBudget eligibilityBudget
  nlinarith [Nat.zero_le (n * B ^ 2), Nat.zero_le (n * B)]

theorem residual_product (n g t epsilon b B P : ℝ)
    (hn : 0 ≤ n) (hg : 0 < g) (ht : 0 < t) (he : 0 < epsilon) (he₁ : epsilon ≤ 1)
    (hgn : g ≤ n) (hb₀ : 0 ≤ b) (hP₀ : 0 ≤ P)
    (hb : b ≤ 200 * n / (epsilon * g) + 1) (hP : P ≤ 4 * g / t)
    (hB : 10 / epsilon ≤ B) :
    b * P ≤ 81 * B * n / t := by
  have hc : 0 ≤ 200 * n / (epsilon * g) + 1 := by positivity
  have heg : epsilon * g ≤ n := by
    exact (mul_le_mul_of_nonneg_right he₁ hg.le).trans (by simpa only [one_mul] using hgn)
  have hgDiv : g ≤ n / epsilon := (le_div_iff₀ he).mpr (by simpa only [mul_comm] using heg)
  have hcoef : 804 / epsilon ≤ 81 * B := by
    simp only [div_eq_mul_inv] at hB ⊢
    nlinarith [inv_nonneg.mpr he.le]
  calc
    b * P ≤ (200 * n / (epsilon * g) + 1) * (4 * g / t) :=
      mul_le_mul hb hP hP₀ hc
    _ = (800 * n / epsilon + 4 * g) / t := by
      field_simp
      <;> ring
    _ ≤ (804 * n / epsilon) / t := by
      apply div_le_div_of_nonneg_right _ ht.le
      simp only [div_eq_mul_inv] at hgDiv ⊢
      linarith
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right hcoef hn
      apply div_le_div_of_nonneg_right _ ht.le
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem access_work (n k t b B P : ℝ)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) (ht : 0 < t)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hinc : b ≤ 4 * n / t + 1) (hprod : b * P ≤ 81 * B * n / t) :
    1000 * (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P) +
        k * b * B * (2 * B + 64) ≤
      400000 * (n + 1) * (1 + n / t) * (B + 2) ^ 4 := by
  let q := n / t
  have hq : 0 ≤ q := div_nonneg hn ht.le
  have hincq : b ≤ 4 * q + 1 := by
    dsimp only [q]
    simpa only [mul_div_assoc] using hinc
  have hsq : 1 ≤ (B + 2) ^ 2 := by nlinarith
  have hBsq : B ^ 2 ≤ (B + 2) ^ 2 := by nlinarith
  have hpower : (B + 2) ^ 2 ≤ (B + 2) ^ 4 := by nlinarith [sq_nonneg ((B + 2) ^ 2 - 1)]
  have hdegree : 1 + 2 * b * B * P ≤ 163 * (1 + q) * (B + 2) ^ 2 := by
    have hpq : b * P ≤ 81 * B * q := by
      dsimp only [q]
      simpa only [mul_div_assoc] using hprod
    have h₀ := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 2 * B by positivity)
    have h₁ := mul_le_mul_of_nonneg_right hBsq hq
    have h₂ := mul_le_mul_of_nonneg_right (show 1 + 162 * q ≤ 163 * (1 + q) by linarith)
      (sq_nonneg (B + 2))
    nlinarith
  have hfirst :
      1000 * (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P) ≤
        163000 * (n + 1) * (1 + q) * (B + 2) ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hdegree
      (show 0 ≤ 1000 * (n + 1) * (B + 2) ^ 2 by positivity)
    nlinarith
  have hbaseline : k * b * B * (2 * B + 64) ≤
      256 * (n + 1) * (1 + q) * (B + 2) ^ 4 := by
    calc
      _ ≤ n * (4 * q + 1) * (B + 2) * (64 * (B + 2)) := by
        gcongr <;> first | exact hkn | exact hincq | linarith
      _ = 64 * n * (4 * q + 1) * (B + 2) ^ 2 := by ring
      _ ≤ 256 * (n + 1) * (1 + q) * (B + 2) ^ 4 := by
        have h₀ : 4 * q + 1 ≤ 4 * (1 + q) := by linarith
        calc
          _ ≤ 64 * (n + 1) * (4 * (1 + q)) * (B + 2) ^ 4 := by gcongr <;> linarith
          _ = _ := by ring
  have hz : 0 ≤ (n + 1) * (1 + q) * (B + 2) ^ 4 := by positivity
  change _ ≤ 400000 * (n + 1) * (1 + q) * (B + 2) ^ 4
  nlinarith

theorem access_disclosures (n t b B P : ℝ)
    (hn : 0 ≤ n) (ht : 0 < t) (hB : 0 ≤ B)
    (hprod : b * P ≤ 81 * B * n / t) :
    (B + 2) * (1 + 2 * b * B * P) ≤
      200 * (1 + n / t) * (B + 2) ^ 3 := by
  have hq : 0 ≤ n / t := div_nonneg hn ht.le
  have hs : 1 ≤ (B + 2) ^ 2 := by nlinarith
  have hBsq : B ^ 2 ≤ (B + 2) ^ 2 := by nlinarith
  have hpq : b * P ≤ 81 * B * (n / t) := by simpa only [mul_div_assoc] using hprod
  have h₀ := mul_le_mul_of_nonneg_left hpq (show 0 ≤ 2 * B by positivity)
  have h₁ := mul_le_mul_of_nonneg_right hBsq hq
  have h₂ := mul_le_mul_of_nonneg_right
    (show 1 + 162 * (n / t) ≤ 163 * (1 + n / t) by linarith) (sq_nonneg (B + 2))
  have hh : 1 + 2 * b * B * P ≤ 163 * (1 + n / t) * (B + 2) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ B + 2 by positivity)
  have hz : 0 ≤ (1 + n / t) * (B + 2) ^ 3 := by positivity
  nlinarith

end SteinerUpperBound.AccessAccounts

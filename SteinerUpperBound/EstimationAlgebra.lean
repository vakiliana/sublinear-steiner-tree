module

public import SteinerUpperBound.Model
public import SteinerLowerBound.Testing

@[expose] public section

namespace SteinerUpperBound.Estimation

open SteinerLowerBound

noncomputable def lowerCount (gmin empirical accuracy : ℝ) : ℝ :=
  gmin * max 0 (empirical - accuracy)

theorem lowerCount_bounds (g gmin mean empirical accuracy : ℝ)
    (hg : 0 ≤ g) (ha : 0 ≤ accuracy) (ha₁ : accuracy ≤ 1)
    (hm : 0 ≤ mean) (hm₁ : mean ≤ 1)
    (hcal : (1 - accuracy) * g ≤ gmin) (hcal₁ : gmin ≤ g)
    (he : |empirical - mean| ≤ accuracy) :
    0 ≤ lowerCount gmin empirical accuracy ∧
      lowerCount gmin empirical accuracy ≤ g * mean ∧
      g * mean - lowerCount gmin empirical accuracy ≤ 3 * accuracy * g := by
  have hgmin : 0 ≤ gmin := (mul_nonneg (sub_nonneg.mpr ha₁) hg).trans hcal
  have hclip₀ : 0 ≤ max 0 (empirical - accuracy) := le_max_left _ _
  have hclip₁ : max 0 (empirical - accuracy) ≤ mean := by
    apply max_le hm
    linarith [(abs_le.mp he).2]
  have hclip₂ : mean - max 0 (empirical - accuracy) ≤ 2 * accuracy := by
    linarith [(abs_le.mp he).1, le_max_right (0 : ℝ) (empirical - accuracy)]
  have hgap : 0 ≤ g - gmin := sub_nonneg.mpr hcal₁
  have hfirst : (g - gmin) * mean ≤ accuracy * g := by
    calc
      _ ≤ (g - gmin) * 1 := mul_le_mul_of_nonneg_left hm₁ hgap
      _ ≤ _ := by nlinarith
  have hsecond : gmin * (mean - max 0 (empirical - accuracy)) ≤ 2 * accuracy * g := by
    have h := mul_le_mul_of_nonneg_left hclip₂ hgmin
    have h' := mul_le_mul_of_nonneg_right hcal₁ (show 0 ≤ 2 * accuracy by positivity)
    nlinarith
  refine ⟨mul_nonneg hgmin hclip₀, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hclip₁ hgmin).trans
      (mul_le_mul_of_nonneg_right hcal₁ hm)
  · unfold lowerCount
    nlinarith

noncomputable def output (upper saving band Qs Qq : ℝ) : ℝ :=
  upper - max (saving / (32 * Qs)) (band / Qq)

theorem estimate_correct
    (L opt upper saving band gamma lambda e sigma Qs Qq c nu : ℝ)
    (hL : 0 ≤ L) (hopt : 0 ≤ opt) (hMST : L ≤ 2 * opt)
    (hupper₀ : L ≤ upper) (hupper₁ : upper ≤ (1 + nu) * L)
    (he : 0 < e) (hsigma : 0 < sigma) (hQs : 0 < Qs) (hQq : 0 < Qq)
    (hsaving : 0 ≤ saving) (hband : 0 ≤ band)
    (hsound : saving / (32 * Qs) ≤ L - opt) (hbsound : band / Qq ≤ L - opt)
    (hgamma : gamma ≤ 2 * saving + e * L / 1000)
    (hlambda : lambda ≤ 2 * (band + sigma * L / 1000) / sigma + L / 100)
    (hnegative : gamma ≤ e * L / 100 → lambda ≤ L / 10 → L ≤ (2 - e / 2) * opt)
    (hc : 0 < c) (hcS : c ≤ e / (32000 * Qs)) (hcT : c ≤ sigma / (1000 * Qq))
    (hcE : c ≤ e / 8) (hc₁ : c ≤ 1 / 10) (hnu : 0 ≤ nu) (hnu₁ : nu ≤ c / 10) :
    GoodEstimate (2 - c) opt (output upper saving band Qs Qq) := by
  let D := max (saving / (32 * Qs)) (band / Qq)
  have hD₀ : 0 ≤ D := (div_nonneg hsaving (by positivity)).trans (le_max_left _ _)
  have hD₁ : D ≤ L - opt := max_le hsound hbsound
  have hlarge (hD : c * L ≤ D) : output upper saving band Qs Qq ≤ (2 - c) * opt := by
    have hcoef₀ : 0 ≤ 1 + nu - c := by linarith
    have hcoef₁ : 2 * (1 + nu - c) ≤ 2 - c := by linarith
    calc
      _ ≤ (1 + nu - c) * L := by unfold output; dsimp [D] at hD; nlinarith
      _ ≤ (1 + nu - c) * (2 * opt) := mul_le_mul_of_nonneg_left hMST hcoef₀
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef₁ hopt]
  refine ⟨?_, ?_⟩
  · unfold output
    dsimp [D] at hD₁
    linarith
  · by_cases hs : saving ≤ e * L / 1000
    · by_cases ht : band ≤ sigma * L / 1000
      · have hg : gamma ≤ e * L / 100 := by
          nlinarith [mul_nonneg he.le hL]
        have hb : lambda ≤ L / 10 := by
          have h : 2 * (band + sigma * L / 1000) / sigma ≤ L / 250 := by
            rw [div_le_iff₀ hsigma]
            nlinarith
          linarith
        have hn := hnegative hg hb
        have hcoef : (1 + nu) * (2 - e / 2) ≤ 2 - c := by
          nlinarith [mul_nonneg hnu he.le]
        calc
          _ ≤ upper := by unfold output; dsimp [D] at hD₀; linarith
          _ ≤ (1 + nu) * L := hupper₁
          _ ≤ (1 + nu) * ((2 - e / 2) * opt) :=
            mul_le_mul_of_nonneg_left hn (by linarith)
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hcoef hopt]
      · apply hlarge
        have hc' := (le_div_iff₀ (show 0 < 1000 * Qq by positivity)).mp hcT
        have hm := mul_le_mul_of_nonneg_right hc' hL
        apply le_trans _ (le_max_right _ _)
        rw [le_div_iff₀ hQq]
        nlinarith [lt_of_not_ge ht]
    · apply hlarge
      have hc' := (le_div_iff₀ (show 0 < 32000 * Qs by positivity)).mp hcS
      have hm := mul_le_mul_of_nonneg_right hc' hL
      apply le_trans _ (le_max_left _ _)
      rw [le_div_iff₀ (show 0 < 32 * Qs by positivity)]
      nlinarith [lt_of_not_ge hs]

end SteinerUpperBound.Estimation

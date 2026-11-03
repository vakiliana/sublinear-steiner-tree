module

public import SteinerLowerBound.MetricComparison.StarBounds

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open HardDistribution

noncomputable def parameterScale (d : ℕ) (H₀ M : ℝ) : ℝ :=
  1 + |H₀ * M ^ d| + |anchorConstant d H₀ M| +
    |24 * (H₀ * M ^ d) * (d.choose 3 : ℝ) / d|

theorem scale_eq_parameters {S Ω : Type*} [Fintype S] (k : Setup S Ω) :
    scale k = parameterScale k.d k.H0 k.M := rfl

theorem eventual_size_conditions (d : ℕ) (hd : 3 ≤ d) (H₀ M : ℝ) :
    ∃ m₀ : ℕ, ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ m : ℕ, m₀ ≤ m → ∀ R : ℝ, R₀ ≤ R →
        d ≤ m ∧ 16 ≤ m ∧ 0 < R ∧
          16 * parameterScale d H₀ M ≤ R ∧
          H₀ * M ^ d / ((d : ℝ) * R) ≤ 1 / 2 ∧
          anchorConstant d H₀ M / R ≤ 1 := by
  let L := parameterScale d H₀ M
  have hL : 1 ≤ L := by
    dsimp only [L, parameterScale]
    linarith [abs_nonneg (H₀ * M ^ d), abs_nonneg (anchorConstant d H₀ M),
      abs_nonneg (24 * (H₀ * M ^ d) * (d.choose 3 : ℝ) / d)]
  have hA : H₀ * M ^ d ≤ L := by
    dsimp only [L, parameterScale]
    linarith [le_abs_self (H₀ * M ^ d), abs_nonneg (anchorConstant d H₀ M),
      abs_nonneg (24 * (H₀ * M ^ d) * (d.choose 3 : ℝ) / d)]
  have hB : anchorConstant d H₀ M ≤ L := by
    dsimp only [L, parameterScale]
    linarith [abs_nonneg (H₀ * M ^ d), le_abs_self (anchorConstant d H₀ M),
      abs_nonneg (24 * (H₀ * M ^ d) * (d.choose 3 : ℝ) / d)]
  refine ⟨max d 16, 16 * L, by linarith, ?_⟩
  intro m hm R hR
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd₀ : (0 : ℝ) < d := by linarith
  have hRp : 0 < R := by linarith
  refine ⟨(le_max_left d 16).trans hm, (le_max_right d 16).trans hm, hRp, hR, ?_, ?_⟩
  · apply (div_le_iff₀ (mul_pos hd₀ hRp)).mpr
    have hh := mul_le_mul_of_nonneg_right hd' hRp.le
    nlinarith
  · apply (div_le_one hRp).mpr
    linarith

end SteinerLowerBound.MetricComparison

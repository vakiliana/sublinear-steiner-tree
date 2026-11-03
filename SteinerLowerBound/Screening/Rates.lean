module

public import SteinerLowerBound.Screening.LuckyStop

@[expose] public section

namespace SteinerLowerBound.Screening

open scoped BigOperators Classical

theorem threshold_sizes (A R : ℕ) (hA : 64 ≤ A) (hR : 0 < R) :
    0 < A / 16 ∧ 0 < (A * R + 15) / 16 ∧
      A ≤ 32 * (A / 16) ∧ A * R ≤ 16 * ((A * R + 15) / 16) ∧
      2 * (R + 2 * ((A * R + 15) / 16) + (A / 16) * R) ≤ A * R ∧
      2 * (3 * ((A * R + 15) / 16) + (A / 16) * R) ≤ A * R := by
  have hK : 64 ≤ A * R := by nlinarith
  have hDR : 16 * ((A / 16) * R) ≤ A * R := by
    have hh : 16 * (A / 16) ≤ A := by omega
    nlinarith
  have hAR : 64 * R ≤ A * R := by nlinarith
  have hT : 16 * ((A * R + 15) / 16) ≤ A * R + 15 := by omega
  have hD : 0 < A / 16 := by omega
  have hDP : A ≤ 32 * (A / 16) := by omega
  have hTP : A * R ≤ 16 * ((A * R + 15) / 16) := by omega
  refine ⟨hD, by omega, hDP, hTP, ?_, ?_⟩ <;> omega

noncomputable def screeningConstant (d B₀ B₁ : ℝ) : ℝ :=
  1636 + 128 * d + 32 * d * B₀ + 8 * B₀ + 4 * B₁

theorem screening_rate_bound
    (d m A R K D t Fc Fs q B₀ B₁ : ℝ)
    (hd : 0 ≤ d) (hm : 0 < m) (hA : 0 < A) (hR : 0 < R)
    (hD : 0 < D) (ht : 0 < t) (hq : 0 ≤ q) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hK : K = A * R) (hM : m = d * A)
    (hDP : A ≤ 32 * D) (hTP : K ≤ 16 * t)
    (hFc : K / 2 ≤ Fc) (hFs : K / 2 ≤ Fs) :
    (2 * q / D + 2 * q * R / t + (2 * R / Fc) * q) / t +
      2 * d * (B₀ / R) * q / t +
      ((4 * (B₀ / R) + 2 * m * (B₁ / (R * m))) / Fs) * q +
      ((2 * q + 2 * m * q / D) / Fs + 2 * q / t) / R ≤
        screeningConstant d B₀ B₁ * (q / (A * K) + q / (K * R)) := by
  have hKp : 0 < K := hK ▸ mul_pos hA hR
  have hFcp : 0 < Fc := lt_of_lt_of_le (by positivity) hFc
  have hFsp : 0 < Fs := lt_of_lt_of_le (by positivity) hFs
  have iD : 1 / D ≤ 32 / A := (div_le_div_iff₀ hD hA).mpr (by nlinarith)
  have iT : 1 / t ≤ 16 / K := (div_le_div_iff₀ ht hKp).mpr (by nlinarith)
  have iFc : 1 / Fc ≤ 2 / K := (div_le_div_iff₀ hFcp hKp).mpr (by nlinarith)
  have iFs : 1 / Fs ≤ 2 / K := (div_le_div_iff₀ hFsp hKp).mpr (by nlinarith)
  have iDT : (1 / D) * (1 / t) ≤ (32 / A) * (16 / K) :=
    mul_le_mul iD iT (by positivity) (by positivity)
  have iTT : (1 / t) * (1 / t) ≤ (16 / K) * (16 / K) :=
    mul_le_mul iT iT (by positivity) (by positivity)
  have iCT : (1 / Fc) * (1 / t) ≤ (2 / K) * (16 / K) :=
    mul_le_mul iFc iT (by positivity) (by positivity)
  have hcluster :
      (2 * q / D + 2 * q * R / t + (2 * R / Fc) * q) / t ≤ 1600 * q / (A * K) := by
    calc
      _ = 2 * q * ((1 / D) * (1 / t)) +
          2 * q * R * ((1 / t) * (1 / t)) +
            2 * R * q * ((1 / Fc) * (1 / t)) := by ring
      _ ≤ 2 * q * ((32 / A) * (16 / K)) +
          2 * q * R * ((16 / K) * (16 / K)) +
            2 * R * q * ((2 / K) * (16 / K)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left iDT (by positivity))
          (mul_le_mul_of_nonneg_left iTT (by positivity)))
            (mul_le_mul_of_nonneg_left iCT (by positivity))
      _ = _ := by rw [hK]; field_simp; ring
  have hstar : 2 * d * (B₀ / R) * q / t ≤ (32 * d * B₀) * q / (K * R) := by
    calc
      _ = (2 * d * B₀ * q / R) * (1 / t) := by ring
      _ ≤ (2 * d * B₀ * q / R) * (16 / K) :=
        mul_le_mul_of_nonneg_left iT (by positivity)
      _ = _ := by ring
  have hlucky :
      ((4 * (B₀ / R) + 2 * m * (B₁ / (R * m))) / Fs) * q ≤
        (8 * B₀ + 4 * B₁) * q / (K * R) := by
    calc
      _ = ((4 * B₀ + 2 * B₁) * q / R) * (1 / Fs) := by
        field_simp
        <;> ring
      _ ≤ ((4 * B₀ + 2 * B₁) * q / R) * (2 / K) :=
        mul_le_mul_of_nonneg_left iFs (by positivity)
      _ = _ := by ring
  have iDS : (1 / D) * (1 / Fs) ≤ (32 / A) * (2 / K) :=
    mul_le_mul iD iFs (by positivity) (by positivity)
  have hnotice :
      ((2 * q + 2 * m * q / D) / Fs + 2 * q / t) / R ≤
        (36 + 128 * d) * q / (K * R) := by
    calc
      _ = (2 * q / R) * (1 / Fs) +
          (2 * m * q / R) * ((1 / D) * (1 / Fs)) +
            (2 * q / R) * (1 / t) := by ring
      _ ≤ (2 * q / R) * (2 / K) +
          (2 * m * q / R) * ((32 / A) * (2 / K)) +
            (2 * q / R) * (16 / K) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left iFs (by positivity))
          (mul_le_mul_of_nonneg_left iDS (by positivity)))
            (mul_le_mul_of_nonneg_left iT (by positivity))
      _ = _ := by rw [hM]; field_simp; ring
  let C₂ := 36 + 128 * d + 32 * d * B₀ + 8 * B₀ + 4 * B₁
  have hC₂ : 0 ≤ C₂ := by dsimp only [C₂]; positivity
  have hX : 0 ≤ q / (A * K) := by positivity
  have hY : 0 ≤ q / (K * R) := by positivity
  have hCX : 1600 * (q / (A * K)) ≤ screeningConstant d B₀ B₁ * (q / (A * K)) :=
    mul_le_mul_of_nonneg_right (by unfold screeningConstant; nlinarith) hX
  have hCY : C₂ * (q / (K * R)) ≤ screeningConstant d B₀ B₁ * (q / (K * R)) :=
    mul_le_mul_of_nonneg_right (by dsimp only [C₂, screeningConstant]; linarith) hY
  calc
    _ ≤ 1600 * q / (A * K) + (32 * d * B₀) * q / (K * R) +
        (8 * B₀ + 4 * B₁) * q / (K * R) + (36 + 128 * d) * q / (K * R) :=
      add_le_add (add_le_add (add_le_add hcluster hstar) hlucky) hnotice
    _ = 1600 * (q / (A * K)) + C₂ * (q / (K * R)) := by dsimp only [C₂]; ring
    _ ≤ screeningConstant d B₀ B₁ * (q / (A * K)) +
        screeningConstant d B₀ B₁ * (q / (K * R)) := add_le_add hCX hCY
    _ = _ := by ring

end SteinerLowerBound.Screening

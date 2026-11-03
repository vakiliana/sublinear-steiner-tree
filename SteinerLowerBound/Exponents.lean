module

public import Mathlib

@[expose] public section

namespace SteinerLowerBound

namespace Exponents

noncomputable def lowerExponent (s : ℕ) : ℝ := (3 * s + 7 : ℕ) / (2 * s + 5 : ℕ)

theorem lowerExponent_eq (s : ℕ) :
    lowerExponent s = 3 / 2 - 1 / (4 * (s : ℝ) + 10) := by
  unfold lowerExponent
  push_cast
  have h₁ : 2 * (s : ℝ) + 5 ≠ 0 := by positivity
  have h₂ : 4 * (s : ℝ) + 10 ≠ 0 := by positivity
  field_simp
  ring

theorem lowerExponent_lt (s : ℕ) : lowerExponent s < 3 / 2 := by
  rw [lowerExponent_eq]
  have h : (0 : ℝ) < 1 / (4 * (s : ℝ) + 10) := by positivity
  linarith

theorem exists_lowerExponent {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ 3 / 2 - ε < lowerExponent s := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
  refine ⟨n + 1, by omega, ?_⟩
  rw [lowerExponent_eq]
  have hn' : 1 < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  have hden : 0 < 4 * ((n + 1 : ℕ) : ℝ) + 10 := by positivity
  have hsmall : 1 / (4 * ((n + 1 : ℕ) : ℝ) + 10) < ε := by
    rw [div_lt_iff₀ hden]
    push_cast
    nlinarith
  linarith

theorem power_corollary {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∀ n : ℝ, 1 ≤ n → n ^ (3 / 2 - ε) ≤ n ^ lowerExponent s := by
  obtain ⟨s, hs, hb⟩ := exists_lowerExponent hε
  exact ⟨s, hs, fun n hn => Real.rpow_le_rpow_of_exponent_le hn hb.le⟩

theorem size_balance (s : ℕ) (t γ : ℝ) :
    t ^ (s + 3) * (γ * t ^ (s + 2)) = γ * t ^ (2 * s + 5) := by
  calc
    _ = γ * (t ^ (s + 3) * t ^ (s + 2)) := by ring
    _ = γ * t ^ ((s + 3) + (s + 2)) := by rw [← pow_add]
    _ = _ := by congr 2; omega

theorem query_balance (s : ℕ) (t γ : ℝ) :
    t ^ (s + 3) * (γ * t ^ (s + 2)) ^ 2 = γ ^ 2 * t ^ (3 * s + 7) := by
  calc
    _ = γ ^ 2 * (t ^ (s + 3) * (t ^ (s + 2)) ^ 2) := by ring
    _ = γ ^ 2 * t ^ ((s + 3) + (s + 2) * 2) := by rw [← pow_mul, ← pow_add]
    _ = _ := by congr 2; omega

theorem balanced_rpow (s : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (t ^ (2 * s + 5)) ^ lowerExponent s = t ^ (3 * s + 7) := by
  have hexp : ((2 * s + 5 : ℕ) : ℝ) * lowerExponent s = (3 * s + 7 : ℕ) := by
    unfold lowerExponent
    have hden : (((2 * s + 5 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [← Real.rpow_natCast t (2 * s + 5), ← Real.rpow_mul ht, hexp, Real.rpow_natCast]

theorem floor_bounds {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) ∧ (⌊x⌋₊ : ℝ) ≤ x := by
  constructor
  · have := Nat.lt_floor_add_one x
    linarith
  · exact Nat.floor_le (by linarith)

end Exponents

end SteinerLowerBound

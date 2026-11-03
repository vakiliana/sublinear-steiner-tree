module

public import SteinerUpperBound.LargeCoverProgram.Basic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open scoped Classical

theorem ceil_rat_cast (q : ℚ) : (⌈q⌉₊ : ℕ) = ⌈(q : ℝ)⌉₊ := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil (q : ℝ)
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil q

/-- The observed large-branch decision and calibrated interval imply the
manuscript large condition. They also prove that the PUBLIC incidence clamp
is inactive. No retained set or metric occurs in the budget computation. -/
theorem calibrated_large_budget (n g : ℕ) (p : Parameters) (gm gp : ℚ)
    (hn : 0 < n) (hg : 0 < g) (ht : 0 < p.t)
    (heps : 0 < (p.eps : ℝ)) (hxi : (p.xi : ℝ) ≤ 1 / 100)
    (hcal : (1 - (p.xi : ℝ)) * g ≤ (gm : ℝ))
    (hupper : (gp : ℝ) ≤ (1 + (p.xi : ℝ)) * g)
    (hbranch : 100 * (p.t : ℚ) / p.eps < gp) :
    50 * (p.t : ℝ) / (p.eps : ℝ) < g ∧ 0 < (gm : ℝ) ∧
      rowCapacity n p gm = SavingScores.incidenceBudget n (p.eps : ℝ) gm ∧
      (n : ℝ) / rowCapacity n p gm ≤ (p.eps : ℝ) * gm / 100 := by
  have hg' : 0 < (g : ℝ) := by exact_mod_cast hg
  have ht' : 0 < (p.t : ℝ) := by exact_mod_cast ht
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbranch' : 100 * (p.t : ℝ) / (p.eps : ℝ) < (gp : ℝ) := by exact_mod_cast hbranch
  have hgp : (gp : ℝ) ≤ 2 * g := by
    nlinarith [mul_nonneg (show 0 ≤ (1 : ℝ) - p.xi by linarith) hg'.le]
  have hlarge : 50 * (p.t : ℝ) / (p.eps : ℝ) < g := by
    have hh : 100 * (p.t : ℝ) / (p.eps : ℝ) =
        2 * (50 * (p.t : ℝ) / (p.eps : ℝ)) := by ring
    linarith
  have hgm : (g : ℝ) / 2 ≤ gm := by
    nlinarith [mul_nonneg (show 0 ≤ (1 / 2 : ℝ) - p.xi by linarith) hg'.le]
  have hgm' : 0 < (gm : ℝ) := by linarith
  have hep : 25 * (p.t : ℝ) ≤ (p.eps : ℝ) * gm := by
    have hh := (div_lt_iff₀ heps).mp hlarge
    nlinarith [mul_le_mul_of_nonneg_left hgm heps.le]
  let q : ℚ := 100 * (n : ℚ) / (p.eps * gm)
  have hq : (q : ℝ) = 100 * (n : ℝ) / ((p.eps : ℝ) * gm) := by simp [q]
  have hqpos : 0 < q := by
    have hh : 0 < (q : ℝ) := by rw [hq]; positivity
    exact_mod_cast hh
  have hqbound : (q : ℝ) ≤ 4 * (n : ℝ) / p.t := by
    rw [hq]
    apply (div_le_div_iff₀ (mul_pos heps hgm') ht').mpr
    nlinarith [mul_le_mul_of_nonneg_left hep (show 0 ≤ 4 * (n : ℝ) by positivity)]
  have hf : 4 * (n : ℝ) / p.t ≤ ((4 * n / p.t : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ ht').mpr
    have hh := Nat.lt_mul_div_succ (4 * n) ht
    have hh' : 4 * (n : ℝ) < (p.t : ℝ) * (((4 * n / p.t : ℕ) : ℝ) + 1) := by exact_mod_cast hh
    linarith
  have hceil : (⌈q⌉₊ : ℕ) ≤ 4 * n / p.t + 2 := by
    apply Nat.ceil_le.mpr
    have hh : (q : ℝ) ≤ ((4 * n / p.t + 2 : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hh
  have hp : 1 ≤ (⌈q⌉₊ : ℕ) := Nat.ceil_pos.mpr hqpos
  have heq : rowCapacity n p gm = SavingScores.incidenceBudget n (p.eps : ℝ) gm := by
    unfold rowCapacity
    rw [max_eq_right (show 1 ≤ p.t by omega)]
    change min (4 * n / p.t + 2) (max 1 ⌈q⌉₊) = _
    rw [max_eq_right hp, min_eq_right hceil, ceil_rat_cast]
    unfold SavingScores.incidenceBudget
    rw [hq]
  have hloss := SavingScores.incidenceBudget_loss n hn (p.eps : ℝ) gm heps hgm'
  rw [← heq] at hloss
  exact ⟨hlarge, hgm', heq, hloss⟩

end SteinerUpperBound.LargeCoverProgram

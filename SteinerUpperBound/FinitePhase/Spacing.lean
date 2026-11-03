module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.FinitePhase

open scoped Classical BigOperators

def count : ℕ := 1000000

noncomputable abbrev delta : ℝ := 1 / 10000000000

noncomputable abbrev contraction : ℝ := 1 - 2 * delta

noncomputable def theta (j : Fin count) : ℝ :=
  1 + (Structural.omega - 1) * (j.val : ℝ) / count

noncomputable def scale (base : ℝ) (j : Fin count) (i : ℕ) : ℝ :=
  base * theta j * Structural.omega ^ i

theorem contraction_pos : 0 < contraction := by norm_num [contraction, delta]

theorem omega_pos : 0 < Structural.omega := by norm_num [Structural.omega]

theorem theta_lower (j : Fin count) : 1 ≤ theta j := by
  have hj : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  dsimp only [theta]
  norm_num [Structural.omega, count]
  linarith

theorem theta_upper (j : Fin count) :
    theta j ≤ Structural.omega - (Structural.omega - 1) / count := by
  have hj : (j.val : ℝ) + 1 ≤ count := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  norm_num [theta, Structural.omega, count] at hj ⊢
  linarith

theorem theta_lt_omega (j : Fin count) : theta j < Structural.omega := by
  have h := theta_upper j
  norm_num [Structural.omega, count] at h ⊢
  linarith

theorem theta_le_contracted_omega (j : Fin count) :
    theta j ≤ contraction * Structural.omega := by
  apply (theta_upper j).trans
  norm_num [Structural.omega, count, contraction, delta]

theorem theta_separated {j k : Fin count} (hjk : j.val < k.val) :
    theta j ≤ contraction * theta k := by
  have hdiff : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast Nat.succ_le_of_lt hjk
  have hk := theta_upper k
  norm_num [theta, Structural.omega, count, contraction, delta] at hdiff hk ⊢
  linarith

theorem scale_pos (base : ℝ) (hb : 0 < base) (j : Fin count) (i : ℕ) :
    0 < scale base j i :=
  mul_pos (mul_pos hb (lt_of_lt_of_le zero_lt_one (theta_lower j))) (pow_pos omega_pos i)

theorem scale_separated_same (base : ℝ) (hb : 0 < base) (i : ℕ)
    {j k : Fin count} (hjk : j.val < k.val) :
    scale base j i ≤ contraction * scale base k i := by
  have hm := mul_le_mul_of_nonneg_left (theta_separated hjk)
    (mul_nonneg hb.le (pow_nonneg omega_pos.le i))
  dsimp only [scale]
  nlinarith

theorem scale_separated_levels (base : ℝ) (hb : 0 < base) {i k : ℕ} (hik : i < k)
    (j l : Fin count) : scale base j i ≤ contraction * scale base l k := by
  have hp : Structural.omega ^ (i + 1) ≤ Structural.omega ^ k :=
    pow_le_pow_right₀ (by norm_num [Structural.omega]) (Nat.succ_le_of_lt hik)
  have h₀ : 0 ≤ contraction * base := mul_nonneg contraction_pos.le hb.le
  have h₁ := mul_le_mul_of_nonneg_left hp h₀
  have h₂ := mul_le_mul_of_nonneg_left (theta_lower l)
    (mul_nonneg h₀ (pow_nonneg omega_pos.le k))
  have h₃ := mul_le_mul_of_nonneg_left (theta_le_contracted_omega j)
    (mul_nonneg hb.le (pow_nonneg omega_pos.le i))
  dsimp only [scale]
  rw [pow_succ] at h₁
  nlinarith

def Window (base : ℝ) (j : Fin count) (i : ℕ) (w : ℝ) : Prop :=
  contraction * scale base j i ≤ w ∧ w < scale base j i

theorem window_unique (base : ℝ) (hb : 0 < base) {j l : Fin count} {i k : ℕ} {w : ℝ}
    (hj : Window base j i w) (hl : Window base l k w) : j = l ∧ i = k := by
  rcases lt_trichotomy i k with hik | hik | hki
  · have h := scale_separated_levels base hb hik j l
    exact (not_lt_of_ge (h.trans hl.1) hj.2).elim
  · subst k
    rcases lt_trichotomy j.val l.val with hjl | hjl | hlj
    · have h := scale_separated_same base hb i hjl
      exact (not_lt_of_ge (h.trans hl.1) hj.2).elim
    · exact ⟨Fin.ext hjl, rfl⟩
    · have h := scale_separated_same base hb i hlj
      exact (not_lt_of_ge (h.trans hj.1) hl.2).elim
  · have h := scale_separated_levels base hb hki l j
    exact (not_lt_of_ge (h.trans hj.1) hl.2).elim

end SteinerUpperBound.FinitePhase

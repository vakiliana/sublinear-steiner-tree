module

public import SteinerLowerBound.MasterParameters
public import SteinerLowerBound.VisibleMass

@[expose] public section

namespace SteinerLowerBound

namespace MasterBound

noncomputable def opened (R m : ℝ) : ℝ :=
  4 * Real.exp 1 * R ^ 3 / m + 8 * R * Real.log m

noncomputable def error (s : ℕ) (a b x y v g z A R m q : ℝ) : ℝ :=
  a * Real.sqrt (q / (m * R ^ 2)) +
    b * (q / (A * R ^ 2) + q / (A ^ 2 * R)) +
    x * opened R m / R ^ 2 + y * opened R m / (m * R) +
    v * m * (g * R / m) ^ (s + 3) + z / m ^ 3

noncomputable def constant (s : ℕ) (a b x y v g z : ℝ) : ℝ :=
  1 + |a| + |b| + |4 * Real.exp 1 * (x + y)| + |8 * (x + y)| +
    |v * g ^ (s + 3)| + |z|

theorem constant_pos (s : ℕ) (a b x y v g z : ℝ) :
    0 < constant s a b x y v g z := by
  unfold constant
  positivity

theorem opened_eq (S : Type*) [Fintype S] (R : ℝ) :
    opened R (Fintype.card S) = VisibleMass.openedBudget (S := S) R := rfl

theorem bound (s : ℕ) (a b x y v g z A R m q : ℝ)
    (hA : 0 < A) (hR : 0 < R) (hm : 1 ≤ m) (hq : 0 ≤ q)
    (hRm : R ≤ m) (hy : 0 ≤ y) :
    error s a b x y v g z A R m q ≤
      constant s a b x y v g z *
        (Real.sqrt (q / (m * R ^ 2)) + q / (A * R ^ 2) + q / (A ^ 2 * R) +
          R ^ (s + 3) / m ^ (s + 2) + R / m + Real.log m / R + 1 / m ^ 3) := by
  have hm₀ : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm
  have hcat : opened R m / R ^ 2 =
      4 * Real.exp 1 * R / m + 8 * Real.log m / R := by
    unfold opened
    field_simp
  have hclose : opened R m / (m * R) =
      4 * Real.exp 1 * R ^ 2 / m ^ 2 + 8 * Real.log m / m := by
    unfold opened
    field_simp
  have hratio : R ^ 2 / m ^ 2 ≤ R / m := by
    rw [← div_pow]
    have hn : 0 ≤ R / m := div_nonneg hR.le hm₀.le
    have ho : R / m ≤ 1 := (div_le_one hm₀).mpr hRm
    nlinarith [mul_nonneg hn (sub_nonneg.mpr ho)]
  have hlogRatio : Real.log m / m ≤ Real.log m / R :=
    div_le_div_of_nonneg_left hlog hR hRm
  have hcloseBound : y * (opened R m / (m * R)) ≤
      y * (4 * Real.exp 1 * R / m + 8 * Real.log m / R) := by
    rw [hclose]
    apply mul_le_mul_of_nonneg_left _ hy
    have hquad := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ 4 * Real.exp 1 by positivity)
    have hlinear := mul_le_mul_of_nonneg_left hlogRatio (by norm_num : (0 : ℝ) ≤ 8)
    convert add_le_add hquad hlinear using 1 <;> ring
  have hmoment : v * m * (g * R / m) ^ (s + 3) =
      (v * g ^ (s + 3)) * (R ^ (s + 3) / m ^ (s + 2)) := by
    simp only [div_pow, mul_pow]
    rw [show m ^ (s + 3) = m ^ (s + 2) * m by rw [pow_succ]]
    field_simp
  have hfirst :
      error s a b x y v g z A R m q ≤
        a * Real.sqrt (q / (m * R ^ 2)) +
          b * (q / (A * R ^ 2) + q / (A ^ 2 * R)) +
          (4 * Real.exp 1 * (x + y)) * (R / m) +
          (8 * (x + y)) * (Real.log m / R) +
          (v * g ^ (s + 3)) * (R ^ (s + 3) / m ^ (s + 2)) +
          z * (1 / m ^ 3) := by
    calc
      _ = a * Real.sqrt (q / (m * R ^ 2)) +
          b * (q / (A * R ^ 2) + q / (A ^ 2 * R)) +
          x * (4 * Real.exp 1 * R / m + 8 * Real.log m / R) +
          y * (opened R m / (m * R)) +
          (v * g ^ (s + 3)) * (R ^ (s + 3) / m ^ (s + 2)) +
          z * (1 / m ^ 3) := by
        unfold error
        rw [hmoment]
        have h := congrArg (fun u : ℝ => x * u) hcat
        linear_combination h
      _ ≤ a * Real.sqrt (q / (m * R ^ 2)) +
          b * (q / (A * R ^ 2) + q / (A ^ 2 * R)) +
          x * (4 * Real.exp 1 * R / m + 8 * Real.log m / R) +
          y * (4 * Real.exp 1 * R / m + 8 * Real.log m / R) +
          (v * g ^ (s + 3)) * (R ^ (s + 3) / m ^ (s + 2)) +
          z * (1 / m ^ 3) := by linarith
      _ = _ := by ring
  let C := constant s a b x y v g z
  have hna := abs_nonneg a
  have hnb := abs_nonneg b
  have hnx := abs_nonneg (4 * Real.exp 1 * (x + y))
  have hny := abs_nonneg (8 * (x + y))
  have hnv := abs_nonneg (v * g ^ (s + 3))
  have hnz := abs_nonneg z
  have ha : a ≤ C := by dsimp [C, constant]; linarith [le_abs_self a]
  have hb : b ≤ C := by dsimp [C, constant]; linarith [le_abs_self b]
  have hx : 4 * Real.exp 1 * (x + y) ≤ C := by
    dsimp [C, constant]
    linarith [le_abs_self (4 * Real.exp 1 * (x + y))]
  have hy' : 8 * (x + y) ≤ C := by
    dsimp [C, constant]
    linarith [le_abs_self (8 * (x + y))]
  have hv : v * g ^ (s + 3) ≤ C := by
    dsimp [C, constant]
    linarith [le_abs_self (v * g ^ (s + 3))]
  have hz : z ≤ C := by dsimp [C, constant]; linarith [le_abs_self z]
  calc
    _ ≤ _ := hfirst
    _ ≤ C * Real.sqrt (q / (m * R ^ 2)) +
        C * (q / (A * R ^ 2) + q / (A ^ 2 * R)) +
        C * (R / m) + C * (Real.log m / R) +
        C * (R ^ (s + 3) / m ^ (s + 2)) + C * (1 / m ^ 3) := by
      gcongr
    _ = _ := by dsimp [C]; ring

end MasterBound

end SteinerLowerBound

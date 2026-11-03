module

public import SteinerUpperBound.EstimatorParameters.Scores
public import SteinerUpperBound.EstimatorParameters.Balance

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters

def rawIncidence (n denom : ℕ) (gminus : ℚ) : ℕ :=
  ⌈100 * (n : ℚ) * denom / gminus⌉₊

/-- The only observed input is the rational calibration output. -/
def incidenceBudget (n : ℕ) (gminus : ℚ) : ℕ :=
  if 0 < gminus then min n (rawIncidence n (epsInv n) gminus) else 0

theorem incidenceBudget_fallback (n : ℕ) (gminus : ℚ) (hg : gminus ≤ 0) :
    incidenceBudget n gminus = 0 := by simp [incidenceBudget, not_lt.mpr hg]

theorem incidenceBudget_le (n : ℕ) (gminus : ℚ) : incidenceBudget n gminus ≤ n := by
  unfold incidenceBudget
  split_ifs
  · exact min_le_left _ _
  · exact Nat.zero_le _

theorem ratCeil_real (q : ℚ) : ⌈(q : ℝ)⌉₊ = ⌈q⌉₊ := by
  apply Nat.le_antisymm
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil q
  · apply Nat.ceil_le.mpr
    exact_mod_cast Nat.le_ceil (q : ℝ)

theorem rawIncidence_real (n : ℕ) (gminus : ℚ) :
    rawIncidence n (epsInv n) gminus = ⌈100 * (n : ℝ) / (eps n * (gminus : ℝ))⌉₊ := by
  unfold rawIncidence
  rw [← ratCeil_real]
  congr 1
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast, eps, epsQ,
    Rat.cast_one]
  ring_nf <;> simp only [inv_inv] <;> ring

theorem incidenceBudget_large (n g : ℕ) (gminus : ℚ) (hgn : g ≤ n)
    (hlarge : 50 * (t n : ℚ) * epsInv n < g) (hcal : (g : ℚ) / 2 ≤ gminus) :
    0 < gminus ∧ incidenceBudget n gminus = rawIncidence n (epsInv n) gminus ∧
      (incidenceBudget n gminus : ℚ) ≤ 4 * (n : ℚ) / t n + 1 ∧
      incidenceBudget n gminus ^ 2 ≤ 50 * (n + 1) := by
  have ht : (0 : ℚ) < t n := by exact_mod_cast t_pos n
  have hE : (1 : ℚ) ≤ epsInv n := by exact_mod_cast (integer_budget_pos n).1
  have hgnQ : (g : ℚ) ≤ n := by exact_mod_cast hgn
  have hnt : (n : ℚ) < (t n : ℚ) ^ 2 := by exact_mod_cast n_lt_t_sq n
  have h50t : 50 * (t n : ℚ) < n := by
    have he := mul_le_mul_of_nonneg_left hE (show (0 : ℚ) ≤ 50 * t n by positivity)
    nlinarith
  have ht50 : (50 : ℚ) < t n := by nlinarith
  have hn50 : (50 : ℚ) < n := by nlinarith
  have hgm : 25 * (t n : ℚ) * epsInv n < gminus := by nlinarith
  have hgm0 : 0 < gminus := by nlinarith
  have hratio : 100 * (n : ℚ) * epsInv n / gminus < 4 * (n : ℚ) / t n := by
    apply (div_lt_div_iff₀ hgm0 ht).mpr
    have hm := mul_lt_mul_of_pos_left hgm (show (0 : ℚ) < 4 * n by linarith)
    nlinarith
  have hceil : (rawIncidence n (epsInv n) gminus : ℚ) <
      100 * (n : ℚ) * epsInv n / gminus + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hraw : (rawIncidence n (epsInv n) gminus : ℚ) ≤ 4 * (n : ℚ) / t n + 1 := by linarith
  have hnumerator : 4 * (n : ℚ) ≤ ((n : ℚ) - 1) * t n := by
    have hh := mul_le_mul_of_nonneg_left (show (5 : ℚ) ≤ t n by linarith)
      (show (0 : ℚ) ≤ (n : ℚ) - 1 by linarith)
    nlinarith
  have hcap : 4 * (n : ℚ) / t n + 1 ≤ n := by
    have hdiv := (div_le_iff₀ ht).mpr hnumerator
    linarith
  have hrawN : rawIncidence n (epsInv n) gminus ≤ n := by exact_mod_cast hraw.trans hcap
  have heq : incidenceBudget n gminus = rawIncidence n (epsInv n) gminus := by
    simp only [incidenceBudget, hgm0, ite_true, min_eq_right hrawN]
  have hntdiv : (n : ℚ) / t n < t n := (div_lt_iff₀ ht).mpr (by nlinarith)
  have hb : (incidenceBudget n gminus : ℚ) ≤ 5 * t n := by
    rw [heq]
    calc
      _ ≤ 4 * ((n : ℚ) / t n) + 1 := by convert hraw using 1 <;> ring
      _ ≤ 4 * (t n : ℚ) + 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hntdiv.le (by norm_num)) le_rfl
      _ ≤ _ := by linarith
  have hbN : incidenceBudget n gminus ≤ 5 * t n := by exact_mod_cast hb
  have hsq := Nat.pow_le_pow_left hbN 2
  refine ⟨hgm0, heq, by simpa only [heq] using hraw, ?_⟩
  nlinarith [t_sq_le n]

theorem incidenceBudget_large_real (n g : ℕ) (gminus : ℚ) (hgn : g ≤ n)
    (hlarge : 50 * (t n : ℝ) / eps n < g) (hcal : (g : ℝ) / 2 ≤ (gminus : ℝ)) :
    0 < gminus ∧ incidenceBudget n gminus = ⌈100 * (n : ℝ) / (eps n * (gminus : ℝ))⌉₊ ∧
      (incidenceBudget n gminus : ℝ) ≤ 4 * (n : ℝ) / t n + 1 ∧
      incidenceBudget n gminus ^ 2 ≤ 50 * (n + 1) := by
  have he : 50 * (t n : ℝ) / eps n = 50 * (t n : ℝ) * epsInv n := by
    simp only [eps, epsQ, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    simp only [div_eq_mul_inv, one_mul, inv_inv]
  rw [he] at hlarge
  have hl : 50 * (t n : ℚ) * epsInv n < g := by exact_mod_cast hlarge
  have hcR : (((g : ℚ) / 2 : ℚ) : ℝ) ≤ (gminus : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hcal
  have hc : (g : ℚ) / 2 ≤ gminus := Rat.cast_le.mp hcR
  obtain ⟨hg, hb, hbd, hsq⟩ := incidenceBudget_large n g gminus hgn hl hc
  have hbdR : (((incidenceBudget n gminus : ℕ) : ℚ) : ℝ) ≤
      ((4 * (n : ℚ) / t n + 1 : ℚ) : ℝ) := Rat.cast_le.mpr hbd
  simp only [Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast,
    Rat.cast_one] at hbdR
  exact ⟨hg, hb.trans (rawIncidence_real n gminus), hbdR, hsq⟩

theorem incidenceBudget_large_pos (n g : ℕ) (gminus : ℚ) (hgn : g ≤ n)
    (hlarge : 50 * (t n : ℚ) * epsInv n < g) (hcal : (g : ℚ) / 2 ≤ gminus) :
    0 < incidenceBudget n gminus := by
  have h := incidenceBudget_large n g gminus hgn hlarge hcal
  have ht : (0 : ℚ) < t n := by exact_mod_cast t_pos n
  have he : (0 : ℚ) < epsInv n := by exact_mod_cast (integer_budget_pos n).1
  have hg : (0 : ℚ) < g := (by positivity : (0 : ℚ) < 50 * t n * epsInv n).trans hlarge
  have hn : (0 : ℚ) < n := hg.trans_le (by exact_mod_cast hgn)
  rw [h.2.1]
  unfold rawIncidence
  exact Nat.ceil_pos.mpr (by positivity [h.1])

end SteinerUpperBound.EstimatorParameters

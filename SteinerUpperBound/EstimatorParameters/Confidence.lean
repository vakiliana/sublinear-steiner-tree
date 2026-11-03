module

public import SteinerUpperBound.EstimatorParameters.Grids

@[expose] public section

set_option maxRecDepth 4096

namespace SteinerUpperBound.EstimatorParameters

open SteinerLowerBound
open scoped Classical BigOperators

def betaDenom (n : ℕ) : ℕ := 1000000 * (heightBudget n + 1) ^ 3
def betaQ (n : ℕ) : ℚ := 1 / betaDenom n
noncomputable abbrev beta (n : ℕ) : ℝ := (betaQ n : ℝ)

def coverClock (n : ℕ) : ℕ := Nat.log2 (8 * (n + 1) * betaDenom n) + 1
def coverTrials (n : ℕ) : ℕ := 2 * coverClock n
def coverSlack (n : ℕ) : ℕ := coverClock n
def privateCap (n k : ℕ) : ℕ := k * coverClock n
def hopBudget (n : ℕ) : ℕ := ell n
def Hc (n : ℕ) : ℕ := 3 * (1 + coverTrials n) + coverSlack n

def betaFactor : ℕ := 1000000 * (heightFactor + 1) ^ 3
def clockFactor : ℕ := 8 * betaFactor + 5
def hcFactor : ℕ := 3 + 7 * clockFactor

theorem betaDenom_pos (n : ℕ) : 0 < betaDenom n := by unfold betaDenom; positivity
theorem betaDenom_large (n : ℕ) : 1000000 ≤ betaDenom n := by
  have h : 1 ≤ (heightBudget n + 1) ^ 3 := by
    have hp : 0 < (heightBudget n + 1) ^ 3 := by positivity
    omega
  unfold betaDenom
  nlinarith

theorem beta_eq (n : ℕ) : beta n = 1 / (betaDenom n : ℝ) := by
  simp only [beta, betaQ, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem beta_bounds (n : ℕ) : 0 < beta n ∧ beta n ≤ 1 / 1000000 ∧ beta n < 1 / 4 := by
  have hp : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hl : (1000000 : ℝ) ≤ betaDenom n := by exact_mod_cast betaDenom_large n
  rw [beta_eq]
  have hu : 1 / (betaDenom n : ℝ) ≤ 1 / 1000000 :=
    (div_le_div_iff₀ hp (by norm_num)).mpr (by nlinarith)
  exact ⟨by positivity, hu, hu.trans_lt (by norm_num)⟩

theorem reciprocal_union_le (D m : ℕ) (hD : 0 < D) (hm : m * 1000000 ≤ D) :
    (m : ℝ) * (1 / (D : ℝ)) ≤ 1 / 1000000 := by
  have hp : (0 : ℝ) < D := by exact_mod_cast hD
  have hn : (m : ℝ) * 1000000 ≤ D := by exact_mod_cast hm
  rw [mul_one_div]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem beta_union (n m : ℕ) (hm : m ≤ heightBudget n) :
    (m : ℝ) * beta n ≤ 1 / 1000000 := by
  have hp : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hh : heightBudget n + 1 ≤ (heightBudget n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < heightBudget n + 1) (show 1 ≤ 3 by omega)
  have hn : m * 1000000 ≤ betaDenom n := by
    have hmp : m ≤ (heightBudget n + 1) ^ 3 := by omega
    simpa only [betaDenom, Nat.mul_comm] using Nat.mul_le_mul_right 1000000 hmp
  rw [beta_eq]
  exact reciprocal_union_le _ _ (betaDenom_pos n) hn

theorem cover_doubling (n : ℕ) : 8 * (n + 1) * betaDenom n < 2 ^ coverClock n :=
  Nat.lt_log2_self

theorem coverClock_pos (n : ℕ) : 0 < coverClock n := by unfold coverClock; omega
theorem coverTrials_pos (n : ℕ) : 0 < coverTrials n := by unfold coverTrials; have h := coverClock_pos n; omega

theorem hopBudget_bounds (n k : ℕ) (hkn : k ≤ n) : Covers.hopCount k ≤ hopBudget n := by
  unfold Covers.hopCount hopBudget ell
  rw [← Nat.log2_eq_log_two]
  have h := log2_mono (show k ≤ n + 2 by omega)
  omega

theorem betaDenom_polylog (n : ℕ) : betaDenom n ≤ betaFactor * ell n ^ 3 := by
  have h : heightBudget n + 1 ≤ (heightFactor + 1) * ell n := by
    unfold heightBudget
    nlinarith [ell_ge_one n]
  have hh := Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left h 3)
  unfold betaDenom betaFactor
  nlinarith

theorem coverClock_polylog (n : ℕ) : coverClock n ≤ clockFactor * ell n := by
  have hd := (betaDenom_polylog n).trans (polylog_to_polynomial n betaFactor 3)
  have hpoly : 8 * (n + 1) * betaDenom n ≤ (8 * betaFactor) * (n + 2) ^ 4 := by
    have h := Nat.mul_le_mul (show n + 1 ≤ n + 2 by omega) hd
    nlinarith
  exact log_of_polynomial_bound n _ (8 * betaFactor) 4 hpoly

theorem elementary_polylog (n : ℕ) :
    coverTrials n ≤ (2 * clockFactor) * ell n ∧
      coverSlack n ≤ clockFactor * ell n ∧ Hc n ≤ hcFactor * ell n := by
  have h := coverClock_polylog n
  have he := ell_ge_one n
  unfold coverTrials coverSlack Hc hcFactor
  constructor
  · nlinarith
  constructor
  · exact h
  · unfold coverTrials coverSlack
    nlinarith

theorem privateCap_polylog (n k : ℕ) : privateCap n k ≤ clockFactor * k * ell n := by
  have h := Nat.mul_le_mul_left k (coverClock_polylog n)
  unfold privateCap
  nlinarith

theorem cover_error_bound (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (k : ℝ) * Real.exp (-(coverTrials n : ℝ) / 2) + Real.exp (-(coverSlack n : ℝ)) +
      k * Real.exp (-(privateCap n k : ℝ) / k) ≤ beta n / 4 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hfirst : -(coverTrials n : ℝ) / 2 = -(coverClock n : ℝ) := by
    unfold coverTrials
    push_cast
    ring
  have hprivate : -(privateCap n k : ℝ) / k = -(coverClock n : ℝ) := by
    unfold privateCap
    push_cast
    field_simp
  rw [hfirst, hprivate]
  change (k : ℝ) * Real.exp (-(coverClock n : ℝ)) + Real.exp (-(coverClock n : ℝ)) +
    k * Real.exp (-(coverClock n : ℝ)) ≤ _
  have he := MSTApproximation.exp_neg_nat_le_two_pow_inv (coverClock n)
  have hdouble : 8 * ((n : ℝ) + 1) * betaDenom n ≤ (2 : ℝ) ^ coverClock n := by
    exact_mod_cast (cover_doubling n).le
  have hinv := inv_anti₀ (show (0 : ℝ) < 8 * (n + 1) * betaDenom n by positivity) hdouble
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hc : 0 ≤ (2 : ℝ) * (n + 1) := by positivity
  calc
    _ = (2 * (k : ℝ) + 1) * Real.exp (-(coverClock n : ℝ)) := by ring
    _ ≤ (2 * ((n : ℝ) + 1)) * Real.exp (-(coverClock n : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (2 * ((n : ℝ) + 1)) * ((2 : ℝ) ^ coverClock n)⁻¹ := mul_le_mul_of_nonneg_left he hc
    _ ≤ (2 * ((n : ℝ) + 1)) * (8 * ((n : ℝ) + 1) * betaDenom n)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hc
    _ = beta n / 4 := by rw [beta_eq]; field_simp; ring

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Covers.Terminal I) :=
  Classical.decEq _

theorem actual_cover_failure {V : Type*} [Fintype V] (I : Instance V)
    (n : ℕ) (hkn : I.terminals.card ≤ n) (rho : ℝ) (hr : 0 < rho) (root : Covers.Terminal I) :
    (Covers.actualBits I (rho / Covers.hopCount I.terminals.card) root
      (privateCap n I.terminals.card) (coverTrials n)).prob
      {b | ¬ Covers.IsCover I rho b ∨
        Real.exp 1 * (1 + (coverTrials n : ℝ) *
          (1 + 2 * Covers.hopCount I.terminals.card * I.mst / rho)) + coverSlack n ≤
            ((CategoricalCoupling.selected b).card : ℝ)} ≤ beta n / 4 := by
  exact (Covers.actual_cover_at_radius I rho hr root _ _ _).trans
    (cover_error_bound n I.terminals.card (Finset.card_pos.mpr ⟨root.val, root.property⟩) hkn)

end SteinerUpperBound.EstimatorParameters

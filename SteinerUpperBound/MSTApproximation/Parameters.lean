module

public import SteinerUpperBound.MSTApproximation.Interval

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open scoped Classical

noncomputable def componentBudget (A nu : ℝ) : ℕ := ⌈100 * A / nu⌉₊
noncomputable def scoreAccuracy (A nu : ℝ) : ℝ := nu / (100 * A)
noncomputable def scoreSamples (beta xi : ℝ) : ℕ := ⌈256 / (beta * xi ^ 2)⌉₊

theorem componentBudget_bound (A nu : ℝ) :
    100 * A / nu ≤ (componentBudget A nu : ℝ) :=
  Nat.le_ceil _

theorem scoreAccuracy_bounds (A nu : ℝ) (hA : 1 ≤ A) (hn : 0 < nu) (hn1 : nu ≤ 1) :
    0 < scoreAccuracy A nu ∧ scoreAccuracy A nu ≤ 1 := by
  unfold scoreAccuracy
  exact ⟨by positivity, (div_le_one (by linarith)).mpr (by linarith)⟩

theorem scoreSamples_budget (beta xi : ℝ) (hb : 0 < beta) (hx : 0 < xi) :
    0 < scoreSamples beta xi ∧ 256 ≤ beta * ((scoreSamples beta xi : ℝ) * xi ^ 2) := by
  have h := Nat.le_ceil (256 / (beta * xi ^ 2))
  have hp : (0 : ℝ) < beta * xi ^ 2 := by positivity
  have hnum := (div_le_iff₀ hp).mp h
  refine ⟨?_, by unfold scoreSamples; nlinarith⟩
  have hpos : (0 : ℝ) < scoreSamples beta xi :=
    (show (0 : ℝ) < 256 / (beta * xi ^ 2) by positivity).trans_le h
  exact_mod_cast hpos

/-- Dyadic public integer tuning; no real logarithm is evaluated by the sampler. -/
noncomputable def proposalExponent (samples : ℕ) (beta xi : ℝ) : ℕ :=
  Nat.log2 (⌈16 * (samples : ℝ) / (beta * xi)⌉₊ + 1) + 1

noncomputable def proposalBudget (terminals samples : ℕ) (beta xi : ℝ) : ℕ :=
  terminals * proposalExponent samples beta xi

theorem proposalExponent_large (samples : ℕ) (beta xi : ℝ) (hb : 0 < beta) (hx : 0 < xi) :
    16 * (samples : ℝ) ≤ beta * xi * (2 : ℝ) ^ proposalExponent samples beta xi := by
  let r : ℕ := ⌈16 * (samples : ℝ) / (beta * xi)⌉₊
  have hceil : 16 * (samples : ℝ) / (beta * xi) ≤ r := Nat.le_ceil _
  have hlogN : r + 1 < 2 ^ (Nat.log2 (r + 1) + 1) := Nat.lt_log2_self
  have hlog : (r : ℝ) + 1 < (2 : ℝ) ^ (Nat.log2 (r + 1) + 1) := by exact_mod_cast hlogN
  have hnum := (div_le_iff₀ (mul_pos hb hx)).mp hceil
  have hm := mul_le_mul_of_nonneg_left (show (r : ℝ) ≤ (2 : ℝ) ^ proposalExponent samples beta xi by
    change (r : ℝ) ≤ (2 : ℝ) ^ (Nat.log2 (r + 1) + 1)
    linarith) (mul_pos hb hx).le
  nlinarith

theorem exp_neg_nat_le_two_pow_inv (d : ℕ) :
    Real.exp (-(d : ℝ)) ≤ ((2 : ℝ) ^ d)⁻¹ := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) he d
  have hExp : Real.exp (d : ℝ) = Real.exp 1 ^ d := by
    simpa only [mul_one] using Real.exp_nat_mul 1 d
  rw [← hExp] at hp
  rw [Real.exp_neg]
  exact inv_anti₀ (by positivity) hp

theorem proposalBudget_bound (terminals samples : ℕ) (hk : 0 < terminals) (hs : 0 < samples)
    (beta xi : ℝ) (hb : 0 < beta) (hx : 0 < xi) :
    Real.exp (-(proposalBudget terminals samples beta xi : ℝ) / terminals) ≤
      beta * xi / (16 * samples) := by
  have hkR : (0 : ℝ) < terminals := by exact_mod_cast hk
  have hsR : (0 : ℝ) < samples := by exact_mod_cast hs
  have he : -(proposalBudget terminals samples beta xi : ℝ) / terminals =
      -(proposalExponent samples beta xi : ℝ) := by
    unfold proposalBudget
    push_cast
    field_simp
  rw [he]
  apply (exp_neg_nat_le_two_pow_inv _).trans
  have hlarge := proposalExponent_large samples beta xi hb hx
  have htwo : (0 : ℝ) < 2 ^ proposalExponent samples beta xi := by positivity
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ htwo (by positivity : (0 : ℝ) < 16 * samples)).mpr
  nlinarith

end SteinerUpperBound.MSTApproximation

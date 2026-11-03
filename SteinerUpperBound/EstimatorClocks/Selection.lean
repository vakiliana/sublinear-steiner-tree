module

public import SteinerUpperBound.EstimatorParameters.Confidence
public import SteinerUpperBound.QueryProgram.DisclosureCap

@[expose] public section

namespace SteinerUpperBound.EstimatorClocks

open QueryProgram

structure Budget where
  workBudget : ℕ
  disclosureBudget : ℕ
deriving DecidableEq, Repr

structure FactoryBudget where
  clock : Budget
  positiveThreshold : ℕ
deriving DecidableEq, Repr

def amplification : ℕ := 100000

def byHeight (height workAccount positiveAccount : ℕ) : Budget :=
  ⟨amplification * (height + 1) * (workAccount + 1),
    amplification * (height + 1) * (positiveAccount + 1)⟩

def stage (n workAccount positiveAccount : ℕ) : Budget :=
  byHeight (EstimatorParameters.heightBudget n) workAccount positiveAccount

def factory (k workAccount positiveAccount : ℕ) : FactoryBudget :=
  let a := amplification * (positiveAccount + 1)
  ⟨⟨amplification * (workAccount + 1), 2 * k * (a + 14)⟩, a⟩

def clocked {M Q R : Type*} (budget : Budget) (p : Code M Q R) :
    Code M Q (Option (Option R)) :=
  (p.disclosureCap budget.disclosureBudget).cap budget.workBudget

theorem amplified_ratio (A B : ℕ) (hA : 0 < A) :
    (B : ℝ) / ((A * (B + 1) + 1 : ℕ) : ℝ) ≤ 1 / (A : ℝ) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hd : (0 : ℝ) < ((A * (B + 1) + 1 : ℕ) : ℝ) := by positivity
  apply (div_le_div_iff₀ hd ha).mpr
  push_cast
  nlinarith

theorem byHeight_ratios (height workAccount positiveAccount : ℕ) :
    4 * (workAccount : ℝ) /
        (((byHeight height workAccount positiveAccount).workBudget + 1 : ℕ) : ℝ) ≤
        4 / (amplification * ((height : ℝ) + 1)) ∧
      (positiveAccount : ℝ) /
        (((byHeight height workAccount positiveAccount).disclosureBudget + 1 : ℕ) : ℝ) ≤
        1 / (amplification * ((height : ℝ) + 1)) := by
  have hA : 0 < amplification * (height + 1) := by unfold amplification; positivity
  have hw := mul_le_mul_of_nonneg_left (amplified_ratio _ workAccount hA)
    (by norm_num : (0 : ℝ) ≤ 4)
  have hp := amplified_ratio _ positiveAccount hA
  constructor
  · simpa only [byHeight, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      div_eq_mul_inv, mul_one, one_mul, mul_assoc]
      using hw
  · simpa only [byHeight, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hp

theorem byHeight_loss (height workAccount positiveAccount : ℕ) :
    4 * (workAccount : ℝ) /
          (((byHeight height workAccount positiveAccount).workBudget + 1 : ℕ) : ℝ) +
        (positiveAccount : ℝ) /
          (((byHeight height workAccount positiveAccount).disclosureBudget + 1 : ℕ) : ℝ) ≤
      5 / (amplification * ((height : ℝ) + 1)) := by
  have h := byHeight_ratios height workAccount positiveAccount
  calc
    _ ≤ 4 / (amplification * ((height : ℝ) + 1)) +
        1 / (amplification * ((height : ℝ) + 1)) := add_le_add h.1 h.2
    _ = _ := by ring

noncomputable def stageLoss (n : ℕ) : ℝ :=
  EstimatorParameters.beta n +
    5 / (amplification * ((EstimatorParameters.heightBudget n : ℝ) + 1))

theorem stageLoss_nonneg (n : ℕ) : 0 ≤ stageLoss n := by
  unfold stageLoss
  have h := (EstimatorParameters.beta_bounds n).1.le
  positivity

theorem summed_stage_loss (n count : ℕ) (hc : count ≤ EstimatorParameters.heightBudget n) :
    (count : ℝ) * stageLoss n ≤ 51 / 1000000 := by
  have hb := EstimatorParameters.beta_union n count hc
  have hcR : (count : ℝ) ≤ (EstimatorParameters.heightBudget n : ℝ) + 1 := by exact_mod_cast (by omega)
  have hd : (0 : ℝ) < amplification * ((EstimatorParameters.heightBudget n : ℝ) + 1) := by
    unfold amplification
    positivity
  have ht : (count : ℝ) * (5 / (amplification * ((EstimatorParameters.heightBudget n : ℝ) + 1))) ≤
      1 / 20000 := by
    rw [← mul_div_assoc, div_le_iff₀ hd]
    norm_num [amplification] at *
    linarith
  unfold stageLoss
  nlinarith

theorem factory_ratios (k workAccount positiveAccount : ℕ) :
    4 * (workAccount : ℝ) /
        (((factory k workAccount positiveAccount).clock.workBudget + 1 : ℕ) : ℝ) ≤ 1 / 25000 ∧
      (positiveAccount : ℝ) /
        (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) ≤ 1 / 100000 := by
  have hw := mul_le_mul_of_nonneg_left (amplified_ratio amplification workAccount (by decide))
    (by norm_num : (0 : ℝ) ≤ 4)
  have hp := amplified_ratio amplification positiveAccount (by decide)
  constructor
  · norm_num only [factory, amplification, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at *
    convert hw using 1
    ring
  · simpa only [factory, amplification, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hp

theorem factory_disclosure_ge_threshold (k workAccount positiveAccount : ℕ) (hk : 0 < k) :
    (factory k workAccount positiveAccount).positiveThreshold ≤
      (factory k workAccount positiveAccount).clock.disclosureBudget := by
  change amplification * (positiveAccount + 1) ≤
    2 * k * (amplification * (positiveAccount + 1) + 14)
  calc
    amplification * (positiveAccount + 1) ≤ amplification * (positiveAccount + 1) + 14 := by omega
    _ = 1 * (amplification * (positiveAccount + 1) + 14) := by omega
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

theorem factory_exponential (k workAccount positiveAccount : ℕ) (hk : 0 < k) :
    Real.exp ((factory k workAccount positiveAccount).positiveThreshold -
      ((factory k workAccount positiveAccount).clock.disclosureBudget : ℝ) / (2 * k)) ≤ 1 / 10000 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have heq : ((factory k workAccount positiveAccount).positiveThreshold : ℝ) -
      ((factory k workAccount positiveAccount).clock.disclosureBudget : ℝ) / (2 * k) = -14 := by
    simp only [factory, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp
    ring
  rw [heq]
  have h := MSTApproximation.exp_neg_nat_le_two_pow_inv 14
  norm_num at h
  exact h.trans (by norm_num)

theorem factory_total_loss (k workAccount positiveAccount : ℕ) (hk : 0 < k) :
    4 * (workAccount : ℝ) /
          (((factory k workAccount positiveAccount).clock.workBudget + 1 : ℕ) : ℝ) +
        (positiveAccount : ℝ) /
          (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) +
        Real.exp ((factory k workAccount positiveAccount).positiveThreshold -
          ((factory k workAccount positiveAccount).clock.disclosureBudget : ℝ) / (2 * k)) ≤
      3 / 20000 := by
  have h := factory_ratios k workAccount positiveAccount
  have he := factory_exponential k workAccount positiveAccount hk
  linarith

theorem total_loss (n count k workAccount positiveAccount : ℕ)
    (hc : count ≤ EstimatorParameters.heightBudget n) (hk : 0 < k) :
    (count : ℝ) * stageLoss n +
        4 * (workAccount : ℝ) /
          (((factory k workAccount positiveAccount).clock.workBudget + 1 : ℕ) : ℝ) +
        (positiveAccount : ℝ) /
          (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) +
        Real.exp ((factory k workAccount positiveAccount).positiveThreshold -
          ((factory k workAccount positiveAccount).clock.disclosureBudget : ℝ) / (2 * k)) ≤
      201 / 1000000 := by
  have hs := summed_stage_loss n count hc
  have hf := factory_total_loss k workAccount positiveAccount hk
  linarith

end SteinerUpperBound.EstimatorClocks

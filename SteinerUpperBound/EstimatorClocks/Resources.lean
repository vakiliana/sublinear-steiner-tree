module

public import SteinerUpperBound.EstimatorClocks.Correctness
public import SteinerUpperBound.EstimatorParameters.Balance

@[expose] public section

namespace SteinerUpperBound.EstimatorClocks

open QueryProgram
open scoped BigOperators

theorem factory_budget (k workAccount positiveAccount : ℕ) :
    (factory k workAccount positiveAccount).clock.workBudget +
        (factory k workAccount positiveAccount).clock.disclosureBudget + 1 ≤
      400000 * (workAccount + k * positiveAccount + k + 1) := by
  dsimp only [factory]
  unfold amplification
  nlinarith [Nat.zero_le (k * positiveAccount)]

theorem factory_budget_of_pos (k workAccount positiveAccount : ℕ) (hk : 0 < k) :
    (factory k workAccount positiveAccount).clock.workBudget +
        (factory k workAccount positiveAccount).clock.disclosureBudget + 1 ≤
      400000 * (workAccount + k * positiveAccount + k) := by
  dsimp only [factory]
  unfold amplification
  nlinarith [Nat.zero_le (k * positiveAccount)]

theorem byHeight_budget (height workAccount positiveAccount : ℕ) :
    (byHeight height workAccount positiveAccount).workBudget +
        (byHeight height workAccount positiveAccount).disclosureBudget + 1 ≤
      300000 * (height + 1) * (workAccount + positiveAccount + 1) := by
  dsimp only [byHeight]
  unfold amplification
  nlinarith [Nat.zero_le (height * workAccount), Nat.zero_le (height * positiveAccount)]

theorem weighted_accounts (n k K d workAccount positiveAccount : ℕ) (hk : k ≤ n)
    (hw : workAccount ≤ K * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d)
    (hp : positiveAccount ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :
    workAccount + k * positiveAccount + k + 1 ≤
      2 * (K + 1) * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d := by
  let Y := EstimatorParameters.t n * EstimatorParameters.ell n ^ d
  let X := (n + 1) * Y
  have hY : 1 ≤ Y := Nat.succ_le_of_lt (by
    dsimp [Y]
    exact mul_pos (EstimatorParameters.t_pos n) (pow_pos (EstimatorParameters.ell_pos n) d))
  have hwX : workAccount ≤ K * X := by simpa only [X, Y, Nat.mul_assoc] using hw
  have hpY : positiveAccount ≤ K * Y := by simpa only [Y, Nat.mul_assoc] using hp
  have hkp : k * positiveAccount ≤ K * X := by
    calc
      k * positiveAccount ≤ k * (K * Y) := Nat.mul_le_mul_left _ hpY
      _ ≤ (n + 1) * (K * Y) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by dsimp [X]; ring
  have hkX : k + 1 ≤ X := by
    calc
      k + 1 ≤ n + 1 := by omega
      _ = (n + 1) * 1 := by omega
      _ ≤ X := Nat.mul_le_mul_left _ hY
  have hsum : workAccount + k * positiveAccount + k + 1 ≤ 2 * (K + 1) * X := by nlinarith
  simpa only [X, Y, Nat.mul_assoc] using hsum

theorem factory_budget_polylog (n k K d workAccount positiveAccount : ℕ) (hk : k ≤ n)
    (hw : workAccount ≤ K * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d)
    (hp : positiveAccount ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :
    (factory k workAccount positiveAccount).clock.workBudget +
        (factory k workAccount positiveAccount).clock.disclosureBudget + 1 ≤
      800000 * (K + 1) * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d := by
  calc
    _ ≤ 400000 * (workAccount + k * positiveAccount + k + 1) :=
      factory_budget k workAccount positiveAccount
    _ ≤ 400000 * (2 * (K + 1) * (n + 1) *
        EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :=
      Nat.mul_le_mul_left _ (weighted_accounts n k K d workAccount positiveAccount hk hw hp)
    _ = _ := by ring

theorem stage_budget_polylog (n K d workAccount positiveAccount : ℕ)
    (hw : workAccount ≤ K * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d)
    (hp : positiveAccount ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :
    (stage n workAccount positiveAccount).workBudget +
        (stage n workAccount positiveAccount).disclosureBudget + 1 ≤
      600000 * (EstimatorParameters.heightFactor + 1) * (K + 1) * (n + 1) *
        EstimatorParameters.t n * EstimatorParameters.ell n ^ (d + 1) := by
  let X := (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d
  have hXP : 1 ≤ X := Nat.succ_le_of_lt (by
    dsimp [X]
    exact mul_pos (mul_pos (by omega) (EstimatorParameters.t_pos n))
      (pow_pos (EstimatorParameters.ell_pos n) d))
  have hwX : workAccount ≤ K * X := by simpa only [X, Nat.mul_assoc] using hw
  have hpX : positiveAccount ≤ K * X := by
    calc
      positiveAccount ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d := hp
      _ ≤ (n + 1) * (K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) := by
        have h := Nat.mul_le_mul_right
          (K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) (show 1 ≤ n + 1 by omega)
        simpa only [one_mul] using h
      _ = K * X := by dsimp [X]; ring
  have hsum : workAccount + positiveAccount + 1 ≤ 2 * (K + 1) * X := by nlinarith
  have hH : EstimatorParameters.heightBudget n + 1 ≤
      (EstimatorParameters.heightFactor + 1) * EstimatorParameters.ell n := by
    have he := EstimatorParameters.ell_ge_one n
    unfold EstimatorParameters.heightBudget
    nlinarith
  calc
    _ ≤ 300000 * (EstimatorParameters.heightBudget n + 1) * (workAccount + positiveAccount + 1) :=
      byHeight_budget (EstimatorParameters.heightBudget n) workAccount positiveAccount
    _ ≤ 300000 * ((EstimatorParameters.heightFactor + 1) * EstimatorParameters.ell n) *
        (2 * (K + 1) * X) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hH) hsum
    _ = _ := by dsimp [X]; rw [pow_succ]; ring

theorem summed_stage_budgets_polylog {J : Type*} (n K d : ℕ) (s : Finset J)
    (workAccount positiveAccount : J → ℕ) (hs : s.card ≤ EstimatorParameters.heightBudget n)
    (hw : ∀ j ∈ s, workAccount j ≤
      K * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d)
    (hp : ∀ j ∈ s, positiveAccount j ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :
    ∑ j ∈ s, ((stage n (workAccount j) (positiveAccount j)).workBudget +
        (stage n (workAccount j) (positiveAccount j)).disclosureBudget + 1) ≤
      600000 * EstimatorParameters.heightFactor * (EstimatorParameters.heightFactor + 1) *
        (K + 1) * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ (d + 2) := by
  let bound := 600000 * (EstimatorParameters.heightFactor + 1) * (K + 1) * (n + 1) *
    EstimatorParameters.t n * EstimatorParameters.ell n ^ (d + 1)
  calc
    _ ≤ ∑ _j ∈ s, bound := Finset.sum_le_sum (fun j hj =>
      stage_budget_polylog n K d (workAccount j) (positiveAccount j) (hw j hj) (hp j hj))
    _ = s.card * bound := by simp
    _ ≤ EstimatorParameters.heightBudget n * bound := Nat.mul_le_mul_right _ hs
    _ = _ := by
      dsimp [bound, EstimatorParameters.heightBudget]
      simp only [pow_add, pow_one, pow_two]
      ring

theorem nat_division_balance (n : ℕ) :
    (n + 1) * (1 + n / EstimatorParameters.t n) ≤ 2 * (n + 1) * EstimatorParameters.t n := by
  have hn : n ≤ EstimatorParameters.t n * EstimatorParameters.t n := by
    nlinarith [EstimatorParameters.n_lt_t_sq n]
  have hd : n / EstimatorParameters.t n ≤ EstimatorParameters.t n := Nat.div_le_of_le_mul hn
  have ht := EstimatorParameters.t_pos n
  have hm := Nat.mul_le_mul_left (n + 1)
    (show 1 + n / EstimatorParameters.t n ≤ 2 * EstimatorParameters.t n by omega)
  nlinarith

theorem real_division_balance (n : ℕ) :
    ((n : ℝ) + 1) * (1 + (n : ℝ) / EstimatorParameters.t n) ≤
      2 * ((n : ℝ) + 1) * EstimatorParameters.t n := by
  have ht : (0 : ℝ) < EstimatorParameters.t n := by exact_mod_cast EstimatorParameters.t_pos n
  have ht1 : (1 : ℝ) ≤ EstimatorParameters.t n := by exact_mod_cast EstimatorParameters.t_pos n
  have hn : (n : ℝ) ≤ (EstimatorParameters.t n : ℝ) ^ 2 := by
    exact_mod_cast (EstimatorParameters.n_lt_t_sq n).le
  have hd : (n : ℝ) / EstimatorParameters.t n ≤ EstimatorParameters.t n :=
    (div_le_iff₀ ht).mpr (by nlinarith)
  have hm := mul_le_mul_of_nonneg_left (show 1 + (n : ℝ) / EstimatorParameters.t n ≤
    2 * EstimatorParameters.t n by linarith) (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
  nlinarith

theorem factory_clock_expected_total {M Q R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (n k K d workAccount positiveAccount : ℕ) (hk : k ≤ n)
    (hw : workAccount ≤ K * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d)
    (hp : positiveAccount ≤ K * EstimatorParameters.t n * EstimatorParameters.ell n ^ d) :
    (clocked (factory k workAccount positiveAccount).clock p).evaluate m bits
      (fun o => (o.work : ℝ) + (o.positiveReplies : ℝ)) ≤
        (800000 * (K + 1) * (n + 1) * EstimatorParameters.t n * EstimatorParameters.ell n ^ d : ℕ) := by
  have h := clocked_expected_resources m bits p (factory k workAccount positiveAccount).clock
  have hb := factory_budget_polylog n k K d workAccount positiveAccount hk hw hp
  rw [Code.evaluate_add]
  calc
    _ ≤ (((factory k workAccount positiveAccount).clock.workBudget +
        (factory k workAccount positiveAccount).clock.disclosureBudget + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [h.1, h.2]
    _ ≤ _ := by exact_mod_cast hb

end SteinerUpperBound.EstimatorClocks

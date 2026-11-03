module

public import SteinerUpperBound.Matching.DepthTail

@[expose] public section

/-!
# The rank-averaged per-directed-state call bound

The oracle is the actual rank-recursive, fresh-cache algorithm in `Oracle`.
The fixed power is three; the explicit constant is intentionally loose.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound
open scoped Classical BigOperators

namespace Budget

theorem exponential_absorption (N h : ℕ) (hN : 2 ≤ N) (hpow : N < 2 ^ h) :
    (6 : ℝ) * (N : ℝ) ^ 4 * Real.exp (-(8 : ℝ) * h) ≤ 1 := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNexp : (N : ℝ) ≤ Real.exp (h : ℝ) := by
    have hpowR : (N : ℝ) ≤ (2 : ℝ) ^ h := by exact_mod_cast hpow.le
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      Real.exp_one_gt_two.le h
    have hexp : Real.exp (h : ℝ) = Real.exp 1 ^ h := by
      simpa only [mul_one] using Real.exp_nat_mul 1 h
    rw [hexp]
    exact hpowR.trans he
  have hsix : (6 : ℝ) ≤ (N : ℝ) ^ 4 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hNR 4
    norm_num at hp
    linarith
  have hpoly : (6 : ℝ) * (N : ℝ) ^ 4 ≤ (N : ℝ) ^ 8 := by
    calc
      _ ≤ (N : ℝ) ^ 4 * (N : ℝ) ^ 4 :=
        mul_le_mul_of_nonneg_right hsix (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (N : ℝ) ^ 8 * Real.exp (-(8 : ℝ) * h) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ Real.exp (h : ℝ) ^ 8 * Real.exp (-(8 : ℝ) * h) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) hNexp 8) (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num only [Nat.cast_ofNat]
      have he : (8 : ℝ) * h + (-(8 : ℝ) * h) = 0 := by ring
      rw [he, Real.exp_zero]

end Budget

namespace Graph

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Graph V E)

def size (_G : Graph V E) : ℕ := Fintype.card V + Fintype.card E + 2

def logSize (G : Graph V E) : ℕ := Nat.log 2 G.size + 1

/-- `8388610 * (1 + floor(log₂(m+p+2)))³`. -/
def callBudget (G : Graph V E) : ℝ := 8388610 * (G.logSize : ℝ) ^ 3

theorem size_ge_two : 2 ≤ G.size := by unfold size; omega

theorem logSize_pos : 0 < G.logSize := Nat.zero_lt_succ _

theorem logSize_le_size : G.logSize ≤ G.size := by
  have hn : G.size ≠ 0 := by have := G.size_ge_two; omega
  have hh := Nat.log_lt_self 2 hn
  unfold logSize
  omega

theorem size_lt_two_pow_logSize : G.size < 2 ^ G.logSize :=
  Nat.lt_pow_succ_log_self (by decide) _

theorem copies_lt_two_pow_logSize : Fintype.card E < 2 ^ G.logSize := by
  have hp : Fintype.card E < G.size := by unfold size; omega
  exact hp.trans G.size_lt_two_pow_logSize

theorem callBudget_ge_one : 1 ≤ G.callBudget := by
  have hh : (1 : ℝ) ≤ G.logSize := by exact_mod_cast G.logSize_pos
  have hp : (1 : ℝ) ≤ (G.logSize : ℝ) ^ 3 := one_le_pow₀ hh
  unfold callBudget
  nlinarith

theorem depth_tail_cost_le_one :
    ((Fintype.card V * (2 * Fintype.card E + 1) : ℕ) : ℝ) *
      (Rank.uniform (E := E)).prob {ρ | G.LongStack (Budget.depth G.logSize) ρ} ≤ 1 := by
  let N := G.size
  let h := G.logSize
  have hm : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast (show Fintype.card V ≤ N by unfold N size; omega)
  have hp : (Fintype.card E : ℝ) ≤ N := by exact_mod_cast (show Fintype.card E ≤ N by unfold N size; omega)
  have hh : (h : ℝ) ≤ N := by exact_mod_cast G.logSize_le_size
  have hcoeff : (2 * Fintype.card E + 1 : ℝ) ≤ 2 * N := by
    have hn : (Fintype.card E : ℝ) + 1 ≤ N := by
      exact_mod_cast (show Fintype.card E + 1 ≤ N by unfold N size; omega)
    linarith
  have hw : ((Fintype.card V * (2 * Fintype.card E + 1) : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ 2 := by
    push_cast
    have hb := mul_le_mul hm hcoeff (by positivity) (by positivity)
    nlinarith
  have hhp : (3 : ℝ) * h * Fintype.card E ≤ 3 * (N : ℝ) ^ 2 := by
    have hb := mul_le_mul hh hp (by positivity) (by positivity)
    nlinarith
  have hprod :
      ((Fintype.card V * (2 * Fintype.card E + 1) : ℕ) : ℝ) *
        (3 * h * Fintype.card E) ≤ 6 * (N : ℝ) ^ 4 := by
    have hb := mul_le_mul hw hhp (by positivity) (by positivity)
    nlinarith
  calc
    _ ≤ ((Fintype.card V * (2 * Fintype.card E + 1) : ℕ) : ℝ) *
        (3 * h * Fintype.card E * Real.exp (-(8 : ℝ) * h)) :=
      mul_le_mul_of_nonneg_left
        (G.longStack_tail h G.logSize_pos G.copies_lt_two_pow_logSize) (by positivity)
    _ = (((Fintype.card V * (2 * Fintype.card E + 1) : ℕ) : ℝ) *
        (3 * h * Fintype.card E)) * Real.exp (-(8 : ℝ) * h) := by ring
    _ ≤ 6 * (N : ℝ) ^ 4 * Real.exp (-(8 : ℝ) * h) :=
      mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    _ ≤ 1 := Budget.exponential_absorption N h G.size_ge_two G.size_lt_two_pow_logSize

/-- The required per-directed-state expected call bound, cached invocations included. -/
theorem expected_Q_le (d : Directed E) :
    (Rank.uniform (E := E)).expect (fun ρ => (G.Q ρ d : ℝ)) ≤ G.callBudget := by
  have hbase := G.Q_expect_le_depth_tail d (Budget.depth G.logSize)
  have hcost := G.depth_tail_cost_le_one
  have hpoly : (Budget.depth G.logSize : ℝ) = 8388608 * (G.logSize : ℝ) ^ 3 + 1 := by
    exact_mod_cast Budget.depth_polynomial G.logSize
  have hh : (1 : ℝ) ≤ G.logSize := by exact_mod_cast G.logSize_pos
  have hh3 : (1 : ℝ) ≤ (G.logSize : ℝ) ^ 3 := one_le_pow₀ hh
  unfold callBudget
  nlinarith

end Graph

end SteinerUpperBound.Matching

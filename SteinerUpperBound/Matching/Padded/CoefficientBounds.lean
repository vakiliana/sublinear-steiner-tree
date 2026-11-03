module

public import SteinerUpperBound.Matching.Padded.Absorption

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Parameters

open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem next_log_le : Nat.log 2 (P.Nstar + 1) ≤ P.logarithm := by
  have hn : P.Nstar + 1 ≤ 2 ^ P.logarithm := Nat.succ_le_of_lt (Nstar_lt_pow S P)
  have hh := Nat.log_mono_right (b := 2) hn
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hh

theorem bucketCoefficient_poly :
    bucketCoefficient S P ≤ 16384 * P.logarithm ^ 2 := by
  let h := P.logarithm
  have hh : 1 ≤ h := logarithm_pos S P
  have hl := next_log_le S P
  change Nat.log 2 (P.Nstar + 1) ≤ h at hl
  have hsquare : (Nat.log 2 (P.Nstar + 1) + 2) ^ 2 ≤ 9 * h ^ 2 := by
    calc
      _ ≤ (3 * h) ^ 2 := Nat.pow_le_pow_left (by omega) _
      _ = _ := by ring
  have hproduct : (2 * (32 * h + 1) + 1) * (72 * (h + 1)) ≤ 9648 * h ^ 2 := by
    have hp := Nat.mul_le_mul (show 2 * (32 * h + 1) + 1 ≤ 67 * h by omega)
      (show 72 * (h + 1) ≤ 144 * h by omega)
    nlinarith
  have hpow : 1 ≤ h ^ 2 := one_le_pow₀ hh
  unfold bucketCoefficient Cache.extensionCoefficient Sparse.operationBound Geometric.operationBound Geometric.height
  dsimp only [Parameters.rankExponent, Parameters.sortHeight, Cache.sortScale]
  change 128 * (Nat.log 2 (P.Nstar + 1) + 1 + 1) ^ 2 + 8 + 17 +
    (32 + 2 * (32 * h + 1) * (72 * (h + 1))) + (72 * (h + 1) + 4) ≤ 16384 * h ^ 2
  nlinarith

theorem callBudget_power :
    G.callBudget ≤ 16777216 * (P.logarithm : ℝ) ^ 3 := by
  have hb := callBudget_le S P
  have hh : (0 : ℝ) ≤ (P.logarithm : ℝ) ^ 3 := by positivity
  linarith

theorem depth_power :
    (_root_.SteinerUpperBound.Matching.Budget.depth (2 * P.logarithm) : ℝ) + 1 ≤
      134217728 * (P.logarithm : ℝ) ^ 3 := by
  rw [_root_.SteinerUpperBound.Matching.Budget.depth_polynomial]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hh : (1 : ℝ) ≤ (P.logarithm : ℝ) ^ 3 :=
    one_le_pow₀ (by exact_mod_cast logarithm_pos S P)
  nlinarith

theorem static_work_power :
    (P.rankExponent + P.sortHeight + 12 : ℝ) ≤ 64 * P.logarithm := by
  have hh : (1 : ℝ) ≤ P.logarithm := by exact_mod_cast logarithm_pos S P
  unfold Parameters.rankExponent Parameters.sortHeight
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem request_work_power :
    (6 : ℝ) * (P.rankExponent + 2) ≤ 256 * P.logarithm := by
  have hh : (1 : ℝ) ≤ P.logarithm := by exact_mod_cast logarithm_pos S P
  unfold Parameters.rankExponent
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  linarith

end SteinerUpperBound.Matching.Padded.Parameters

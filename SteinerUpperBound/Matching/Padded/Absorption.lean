module

public import SteinerUpperBound.Matching.Padded.GoodCost

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Parameters

open SteinerLowerBound
open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem logarithm_pos : 0 < P.logarithm := Nat.succ_pos _

theorem logarithm_le_Nstar : P.logarithm ≤ P.Nstar := by
  have hn : P.Nstar ≠ 0 := by have := P.two_le; omega
  have hh := Nat.log_lt_self 2 hn
  unfold Parameters.logarithm
  omega

theorem graph_size_le : G.size ≤ P.Nstar := by
  have hp := S.copies_le_slots
  have hs := P.size_le
  unfold Graph.size
  omega

theorem graph_log_le : G.logSize ≤ P.logarithm := by
  exact Nat.add_le_add_right (Nat.log_mono_right (graph_size_le S P)) 1

theorem callBudget_le :
    G.callBudget ≤ 8388610 * (P.logarithm : ℝ) ^ 3 := by
  have hh : (G.logSize : ℝ) ≤ P.logarithm := by exact_mod_cast graph_log_le S P
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hh _) (by norm_num)

theorem W_sum_le (A : Account S) : (∑ v, A.W v) ≤ A.Cstar * P.Nstar := by
  calc
    _ ≤ ∑ v, (S.length v : ℝ) * A.Cstar := Finset.sum_le_sum fun v _ => A.W_le v
    _ = (S.totalSlots : ℝ) * A.Cstar := by
      rw [← Finset.sum_mul]
      simp only [Slots.totalSlots, Nat.cast_sum]
    _ ≤ _ := by
      have hs : (S.totalSlots : ℝ) ≤ P.Nstar := by exact_mod_cast (show S.totalSlots ≤ P.Nstar by have := P.size_le; omega)
      convert mul_le_mul_of_nonneg_right hs A.Cstar_nonneg using 1 <;> ring

theorem size_cube_le_rankCard : P.Nstar ^ 3 ≤ P.rankCard := by
  have hn : 1 ≤ P.Nstar := by have := P.two_le; omega
  exact (pow_le_pow_right₀ hn (by decide : 3 ≤ 32)).trans (rankCard_ge_power S P)

theorem residual_tie_le_one :
    (Fintype.card V : ℝ) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard) ≤ 1 := by
  have hm : (Fintype.card V : ℝ) ≤ P.Nstar := by exact_mod_cast (show Fintype.card V ≤ P.Nstar by have := P.size_le; omega)
  have hp : (Fintype.card E : ℝ) ≤ P.Nstar := by exact_mod_cast copies_le_Nstar S P
  have hQ : (0 : ℝ) < P.rankCard := by exact_mod_cast P.rankCard_pos
  have hcard : (P.Nstar : ℝ) ^ 3 ≤ P.rankCard := by exact_mod_cast size_cube_le_rankCard S P
  rw [← mul_div_assoc]
  apply (div_le_one hQ).mpr
  have hs : (Fintype.card E : ℝ) ^ 2 ≤ (P.Nstar : ℝ) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hp _
  have hm' := mul_le_mul hm hs (by positivity) (by positivity)
  nlinarith

theorem weighted_tie_le (A : Account S) :
    (∑ v, A.W v) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard) ≤ A.Cstar := by
  have hp : (Fintype.card E : ℝ) ≤ P.Nstar := by exact_mod_cast copies_le_Nstar S P
  have hQ : (0 : ℝ) < P.rankCard := by exact_mod_cast P.rankCard_pos
  have hcard : (P.Nstar : ℝ) ^ 3 ≤ P.rankCard := by exact_mod_cast size_cube_le_rankCard S P
  have hratio : (P.Nstar : ℝ) * ((Fintype.card E : ℝ) ^ 2 / P.rankCard) ≤ 1 := by
    rw [← mul_div_assoc]
    apply (div_le_one hQ).mpr
    have hs : (Fintype.card E : ℝ) ^ 2 ≤ (P.Nstar : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hp _
    nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg P.Nstar : (0 : ℝ) ≤ _)]
  have hw := mul_le_mul_of_nonneg_right (W_sum_le S P A)
    (show 0 ≤ (Fintype.card E : ℝ) ^ 2 / P.rankCard by positivity)
  have hh := mul_le_mul_of_nonneg_left hratio A.Cstar_nonneg
  nlinarith

theorem exp_extra_le (h : ℕ) (hh : 0 < h) :
    Real.exp (-(64 : ℝ) * h) ≤ (1 / 4 : ℝ) * Real.exp (-(8 : ℝ) * h) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have hp := mul_le_mul he he (by norm_num) (Real.exp_pos _).le
    rw [← Real.exp_add] at hp
    norm_num at hp ⊢
    exact hp
  have hx : Real.exp (-(56 : ℝ) * h) ≤ 1 / 4 := by
    have heq : -(56 : ℝ) * h = -((56 : ℝ) * h) := by ring
    rw [heq, Real.exp_neg]
    have hm := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ 56 * h by linarith)
    have hfour : (4 : ℝ) ≤ Real.exp (56 * h) := he2.trans hm
    have hd : (1 : ℝ) / Real.exp (56 * h) ≤ 1 / 4 :=
      (div_le_div_iff₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 4)).mpr
        (by simpa only [one_mul] using hfour)
    simpa only [one_div] using hd
  have heq : -(64 : ℝ) * h = -(8 : ℝ) * h + -(56 : ℝ) * h := by ring
  rw [heq, Real.exp_add]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx (Real.exp_pos (-(8 : ℝ) * h)).le

theorem weighted_density_le (A : Account S) :
    (∑ v, A.W v) *
      ((Fintype.card V : ℝ) * (P.rankExponent + 2) * Real.exp (-(64 : ℝ) * P.logarithm)) ≤ A.Cstar := by
  let N := P.Nstar
  let h := P.logarithm
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast P.two_le
  have hm : (Fintype.card V : ℝ) ≤ N := by exact_mod_cast (show Fintype.card V ≤ N by have := P.size_le; dsimp only [N]; omega)
  have hh : (h : ℝ) ≤ N := by exact_mod_cast logarithm_le_Nstar S P
  have hR : (P.rankExponent + 2 : ℝ) ≤ 34 * N := by
    unfold Parameters.rankExponent
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    dsimp only [h] at hh
    nlinarith

  have hextra := exp_extra_le h (logarithm_pos S P)
  have habs := _root_.SteinerUpperBound.Matching.Budget.exponential_absorption N h P.two_le (Nstar_lt_pow S P)
  have hbase : (N : ℝ) * (Fintype.card V : ℝ) * (P.rankExponent + 2) *
      Real.exp (-(64 : ℝ) * h) ≤ 1 := by
    have hcoef : (N : ℝ) * Fintype.card V * (P.rankExponent + 2) ≤ 34 * (N : ℝ) ^ 3 := by
      have hp := mul_le_mul hm hR (by positivity) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ N)]
    have he := mul_le_mul hcoef hextra (Real.exp_pos _).le (by positivity)
    have hN2 : (34 / 4 : ℝ) * (N : ℝ) ^ 3 ≤ 6 * (N : ℝ) ^ 4 := by
      have hcoef' : 0 ≤ 6 * (N : ℝ) - 34 / 4 := by linarith
      nlinarith [mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ N) 3) hcoef']
    have hFinal := mul_le_mul_of_nonneg_right hN2 (Real.exp_pos (-(8 : ℝ) * h)).le
    nlinarith
  have hw := mul_le_mul_of_nonneg_right (W_sum_le S P A)
    (show (0 : ℝ) ≤ (Fintype.card V : ℝ) * (P.rankExponent + 2) * Real.exp (-(64 : ℝ) * h) by positivity)
  have hh' := mul_le_mul_of_nonneg_left hbase A.Cstar_nonneg
  dsimp only [N, h] at *
  nlinarith

theorem trace_exception_le_one :
    ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1)) *
      (Rank.uniform (E := E)).prob {ρ |
        G.LongStack (_root_.SteinerUpperBound.Matching.Budget.depth (2 * P.logarithm)) ρ} ≤ 1 := by
  let N := P.Nstar
  let h := P.logarithm
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast P.two_le
  have hNnat : 2 ≤ N := P.two_le
  have hpN : Fintype.card E + 1 ≤ N := by
    have hs := P.size_le
    have hp := S.copies_le_slots
    dsimp only [N]
    omega
  have hp : (Fintype.card E : ℝ) + 1 ≤ N := by exact_mod_cast hpN
  have hh : (h : ℝ) ≤ N := by exact_mod_cast logarithm_le_Nstar S P
  have hpos : 0 < 2 * h := by have := logarithm_pos S P; dsimp only [h]; omega
  have hpow : N ^ 2 < 2 ^ (2 * h) := by
    have hb : N < 2 ^ h := Nstar_lt_pow S P
    have hsquare : N ^ 2 < (2 ^ h) ^ 2 := by nlinarith
    simpa only [← pow_mul, Nat.mul_comm] using hsquare
  have hcopies : Fintype.card E < 2 ^ (2 * h) := by
    have hlt : Fintype.card E < N ^ 2 := by nlinarith
    exact hlt.trans hpow
  have ht := G.longStack_tail (2 * h) hpos hcopies
  have habs := _root_.SteinerUpperBound.Matching.Budget.exponential_absorption
    (N ^ 2) (2 * h) (by nlinarith : 2 ≤ N ^ 2) hpow
  have hM :
      (Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1) ≤
        4 * (N : ℝ) ^ 3 := by
    have hp0 : (0 : ℝ) ≤ Fintype.card E := Nat.cast_nonneg _
    have ha := mul_le_mul hp (show (2 * Fintype.card E : ℝ) ≤ 2 * N by linarith)
      (by positivity) (by positivity)
    have hb := mul_le_mul ha (show (2 * Fintype.card E + 1 : ℝ) ≤ 2 * N by linarith)
      (by positivity) (by positivity)
    nlinarith
  have hcoeff : (3 : ℝ) * (2 * h : ℕ) * Fintype.card E ≤ 6 * (N : ℝ) ^ 2 := by
    have hp' : (Fintype.card E : ℝ) ≤ N := by linarith
    have hc := mul_le_mul hh hp' (by positivity) (by positivity)
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  have hprod :
      ((Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1)) *
        ((3 : ℝ) * (2 * h : ℕ) * Fintype.card E) ≤ 6 * (N : ℝ) ^ 8 := by
    have hm := mul_le_mul hM hcoeff (by positivity) (by positivity)
    have hn3 : (4 : ℝ) ≤ (N : ℝ) ^ 3 := by
      have hh' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 3
      norm_num at hh' ⊢
      linarith
    have hp' := mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ N) 5) (sub_nonneg.mpr hn3)
    nlinarith
  have htail := mul_le_mul_of_nonneg_left ht
    (show (0 : ℝ) ≤ (Fintype.card E + 1 : ℝ) * (2 * Fintype.card E) * (2 * Fintype.card E + 1) by positivity)
  have he := mul_le_mul_of_nonneg_right hprod (Real.exp_pos (-(8 : ℝ) * (2 * h : ℕ))).le
  norm_num only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] at habs htail he
  nlinarith

end SteinerUpperBound.Matching.Padded.Parameters

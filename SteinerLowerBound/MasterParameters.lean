module

public import SteinerLowerBound.ParameterGeometry

@[expose] public section

namespace SteinerLowerBound

open ParameterGrowth ParameterGeometry

namespace MasterParameters

noncomputable def master (d s : ℕ) (γ c : ℝ) (t : ℕ) : ℝ :=
  let A : ℝ := clusters s t
  let R : ℝ := clusterSize s γ t
  let m : ℝ := special d s t
  let q : ℝ := queries s γ c t
  Real.sqrt (q / (m * R ^ 2)) + q / (A * R ^ 2) + q / (A ^ 2 * R) +
    R ^ (s + 3) / m ^ (s + 2) + R / m + Real.log m / R + 1 / m ^ 3

theorem moment_ratio (d s : ℕ) (γ : ℝ) (t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hγ : 0 ≤ γ) (hγ₁ : γ ≤ 1)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (clusterSize s γ t : ℝ) ^ (s + 3) / (special d s t : ℝ) ^ (s + 2) ≤ γ := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hm₀ : (0 : ℝ) < special d s t := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < t) (special_ge_t d s t hd ht))
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ clusterSize s γ t by positivity)
    (clusterSize_bounds s γ t hR).2 (s + 3)
  have hγpow : γ ^ (s + 3) ≤ γ := by
    have h := pow_le_pow_left₀ hγ hγ₁ (s + 2)
    have hmul := mul_le_mul_of_nonneg_right h hγ
    simpa only [one_pow, pow_succ, one_mul] using hmul
  have hdPow : (1 : ℝ) ≤ (d : ℝ) ^ (s + 2) := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (show (1 : ℝ) ≤ d by exact_mod_cast hd) (s + 2)
  calc
    _ ≤ (γ * (t : ℝ) ^ (s + 2)) ^ (s + 3) / (special d s t : ℝ) ^ (s + 2) :=
      div_le_div_of_nonneg_right hp (pow_nonneg hm₀.le _)
    _ = γ ^ (s + 3) / (d : ℝ) ^ (s + 2) := by
      simp only [special, clusters, Nat.cast_mul, Nat.cast_pow, mul_pow, ← pow_mul]
      rw [Nat.mul_comm (s + 2) (s + 3)]
      field_simp
    _ ≤ γ := by
      rw [div_le_iff₀ (pow_pos hd₀ _)]
      have h := mul_le_mul_of_nonneg_left hdPow hγ
      nlinarith

theorem master_bound (d s : ℕ) (γ c : ℝ) (t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hc : 0 ≤ c)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    master d s γ c t ≤ Real.sqrt c + c + γ +
      (c * γ + γ + 2 * logConstant d s / γ + 1) / t := by
  let A : ℝ := clusters s t
  let R : ℝ := clusterSize s γ t
  let m : ℝ := special d s t
  let q : ℝ := queries s γ c t
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hA₀ : 0 < A := by dsimp [A, clusters]; positivity
  have hR₀ : 0 < R := by
    dsimp [R]
    exact_mod_cast (show 0 < clusterSize s γ t by have := clusterSize_pos s γ t hR; omega)
  have hm₀ : 0 < m := by
    dsimp [m]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < t) (special_ge_t d s t hd ht))
  have hAm : A ≤ m := by dsimp [A, m]; exact_mod_cast special_ge_clusters d s t hd
  have hq : q ≤ c * A * R ^ 2 := Nat.floor_le (by positivity)
  have hqm : q / (m * R ^ 2) ≤ c := by
    rw [div_le_iff₀ (mul_pos hm₀ (pow_pos hR₀ 2))]
    have h := mul_le_mul_of_nonneg_right hAm (show 0 ≤ c * R ^ 2 by positivity)
    nlinarith
  have hqs : Real.sqrt (q / (m * R ^ 2)) ≤ Real.sqrt c := Real.sqrt_le_sqrt hqm
  have hqR : q / (A * R ^ 2) ≤ c := by
    rw [div_le_iff₀ (mul_pos hA₀ (pow_pos hR₀ 2))]
    nlinarith
  have hqA : q / (A ^ 2 * R) ≤ c * γ / t := by
    calc
      _ ≤ (c * A * R ^ 2) / (A ^ 2 * R) := div_le_div_of_nonneg_right hq (by positivity)
      _ = c * (R / A) := by field_simp
      _ ≤ c * (γ / t) := mul_le_mul_of_nonneg_left (radius_over_clusters s γ t ht hR) hc
      _ = _ := by ring
  have hmoment := moment_ratio d s γ t hd ht hγ.le hγ₁ hR
  have hRm := radius_over_special d s γ t hd ht hR
  have hlog := log_over_radius d s γ t hd ht hγ hR
  have hinv := inverse_cube_special d s t hd ht
  calc
    _ ≤ Real.sqrt c + c + c * γ / t + γ + γ / t +
        2 * logConstant d s / (γ * t) + 1 / t := by
      dsimp only [master]
      dsimp only [A, R, m, q] at hqs hqR hqA hmoment hRm hlog hinv
      linarith
    _ = _ := by field_simp; ring

theorem exists_small (d s : ℕ) (hd : 1 ≤ d)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) (L : ℝ) (A₀ m₀ : ℕ) :
    ∃ γ c : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        1 ≤ t ∧ A₀ ≤ clusters s t ∧ m₀ ≤ special d s t ∧
        L ≤ clusterSize s γ t ∧ (clusterSize s γ t : ℝ) ≤ special d s t ∧
        Real.log (special d s t) ≤ clusterSize s γ t ∧
        2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
        2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 ∧
        C * master d s γ c t ≤ ε := by
  let γ := min (1 / 2 : ℝ) (ε / (4 * C))
  let δ := min (1 / 2 : ℝ) (ε / (8 * C))
  let c := δ ^ 2
  have hγ : 0 < γ := lt_min (by norm_num) (by positivity)
  have hγ₁ : γ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ₁ : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hc : 0 < c := sq_pos_of_pos hδ
  have hc₁ : c ≤ 1 := by dsimp [c]; nlinarith
  have hcg : C * γ ≤ ε / 4 := by
    have h := (le_div_iff₀ (show 0 < 4 * C by positivity)).mp
      (show γ ≤ ε / (4 * C) from min_le_right _ _)
    nlinarith
  have hhead : C * (Real.sqrt c + c) ≤ ε / 4 := by
    have hsqrt : Real.sqrt c = δ := by dsimp [c]; rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hδ.le]
    rw [hsqrt]
    have h := (le_div_iff₀ (show 0 < 8 * C by positivity)).mp
      (show δ ≤ ε / (8 * C) from min_le_right _ _)
    have hcδ : c ≤ δ := by dsimp [c]; nlinarith
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hcδ δ) hC.le
    nlinarith
  let H := c * γ + γ + 2 * logConstant d s / γ + 1
  have hH : 0 < H := by
    have hlog := logConstant_nonneg d s hd
    dsimp [H]
    positivity
  obtain ⟨tg, hg⟩ := eventual_conditions d s hd γ c L hγ hγ₁ hc A₀ m₀
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt ((tg : ℝ) + 1 + 2 * C * H / ε)
  refine ⟨γ, c, hγ, hγ₁, hc, hc₁, t₀, ?_⟩
  intro t ht
  have htt : (t₀ : ℝ) ≤ t := by exact_mod_cast ht
  have htG : tg ≤ t := by
    have h : (tg : ℝ) ≤ t := by
      have hp : 0 < 2 * C * H / ε := by positivity
      linarith
    exact_mod_cast h
  obtain ⟨ht₁, htA, htm, htL, hRm, hlog, hR, hq⟩ := hg t htG
  have ht₀' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htail : C * H / (t : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ ht₀']
    have h : 2 * C * H / ε ≤ (t : ℝ) := by linarith [show (0 : ℝ) ≤ tg from Nat.cast_nonneg _]
    have hm := (div_le_iff₀ hε).mp h
    nlinarith
  have hmaster := mul_le_mul_of_nonneg_left (master_bound d s γ c t hd ht₁ hγ hγ₁ hc.le hR) hC.le
  have hsmall : C * master d s γ c t ≤ ε := by
    have heq : C * (Real.sqrt c + c + γ + H / (t : ℝ)) =
        C * (Real.sqrt c + c) + C * γ + C * H / (t : ℝ) := by ring
    change C * master d s γ c t ≤ C * (Real.sqrt c + c + γ + H / (t : ℝ)) at hmaster
    rw [heq] at hmaster
    linarith
  exact ⟨ht₁, htA, htm, htL, hRm, hlog, hR, hq, hsmall⟩

end MasterParameters

end SteinerLowerBound

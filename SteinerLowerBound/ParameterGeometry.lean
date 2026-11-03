module

public import SteinerLowerBound.ParameterGrowth

@[expose] public section

namespace SteinerLowerBound

namespace ParameterGeometry

open ParameterGrowth

noncomputable def tiny (A R : ℕ) : ℝ := 1 / (((A * R : ℕ) : ℝ) ^ 3)

theorem tiny_pos (A R : ℕ) (hA : 1 ≤ A) (hR : 1 ≤ R) : 0 < tiny A R := by
  have hK : 0 < A * R := Nat.mul_pos (by omega) (by omega)
  unfold tiny
  positivity

theorem tiny_le_one (A R : ℕ) (hA : 1 ≤ A) (hR : 1 ≤ R) : tiny A R ≤ 1 := by
  have hK : (1 : ℝ) ≤ (A * R : ℕ) := by
    exact_mod_cast (show 1 ≤ A * R by nlinarith)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hK 3
  unfold tiny
  exact (div_le_one (by positivity)).mpr (by simpa using hp)

theorem offset_le_one (A R : ℕ) (hA : 1 ≤ A) (hR : 1 ≤ R) :
    tiny A R * A * ((R : ℝ) - 1) ≤ 1 := by
  have hK : (1 : ℝ) ≤ (A * R : ℕ) := by exact_mod_cast (show 1 ≤ A * R by nlinarith)
  have hK₀ : (0 : ℝ) < (A * R : ℕ) := by linarith
  have hp : ((A * R : ℕ) : ℝ) ≤ ((A * R : ℕ) : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hK (show 1 ≤ 3 by norm_num)
  have hratio : ((A * R : ℕ) : ℝ) / ((A * R : ℕ) : ℝ) ^ 3 ≤ 1 :=
    (div_le_one (pow_pos hK₀ 3)).mpr hp
  have hsmall : tiny A R * A * ((R : ℝ) - 1) ≤
      ((A * R : ℕ) : ℝ) / ((A * R : ℕ) : ℝ) ^ 3 := by
    have ht := (tiny_pos A R hA hR).le
    have hA₀ : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hmul := mul_nonneg ht hA₀
    calc
      _ ≤ tiny A R * ((A * R : ℕ) : ℝ) := by push_cast; nlinarith
      _ = _ := by unfold tiny; ring
  exact hsmall.trans hratio

theorem distance_scale (N K D : ℕ) (hK : 1 ≤ K) (hNK : K ≤ N) (hND : N ≤ D * K) :
    1 / (N : ℝ) ^ 3 ≤ 1 / (K : ℝ) ^ 3 ∧
      1 / (K : ℝ) ^ 3 ≤ (D : ℝ) ^ 3 / (N : ℝ) ^ 3 := by
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hN₀ : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast hNK
  have hND' : (N : ℝ) ≤ (D : ℝ) * K := by exact_mod_cast hND
  constructor
  · exact one_div_le_one_div_of_le (pow_pos hK₀ 3)
      (pow_le_pow_left₀ hK₀.le hKN 3)
  · rw [div_le_div_iff₀ (pow_pos hK₀ 3) (pow_pos hN₀ 3)]
    have h := pow_le_pow_left₀ hN₀.le hND' 3
    simpa only [one_mul, mul_pow] using h

noncomputable def logConstant (d s : ℕ) : ℝ := Real.log d + (s + 3 : ℕ)

theorem logConstant_nonneg (d s : ℕ) (hd : 1 ≤ d) : 0 ≤ logConstant d s := by
  unfold logConstant
  have := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd)
  positivity

theorem log_special_le (d s t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    Real.log (special d s t) ≤ logConstant d s * t := by
  have hd₀ : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have hlogt : Real.log t ≤ (t : ℝ) := by linarith [Real.log_le_sub_one_of_pos ht₀]
  have h₁ := mul_le_mul_of_nonneg_left ht₁ hlogd
  have h₂ := mul_le_mul_of_nonneg_left hlogt (show (0 : ℝ) ≤ (s + 3 : ℕ) by positivity)
  simp only [special, clusters, Nat.cast_mul, Nat.cast_pow,
    Real.log_mul hd₀.ne' (pow_ne_zero _ ht₀.ne'), Real.log_pow]
  unfold logConstant
  nlinarith

theorem clusters_ge_t (s t : ℕ) (ht : 1 ≤ t) : t ≤ clusters s t := by
  have h := pow_le_pow_right₀ ht (show 1 ≤ s + 3 by omega)
  simpa [clusters] using h

theorem special_ge_t (d s t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) : t ≤ special d s t := by
  have h := Nat.mul_le_mul_right (clusters s t) hd
  exact (clusters_ge_t s t ht).trans (by simpa [special] using h)

theorem special_ge_clusters (d s t : ℕ) (hd : 1 ≤ d) : clusters s t ≤ special d s t := by
  simpa [special] using Nat.mul_le_mul_right (clusters s t) hd

theorem radius_over_clusters (s : ℕ) (γ : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (clusterSize s γ t : ℝ) / clusters s t ≤ γ / t := by
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hA₀ : (0 : ℝ) < clusters s t := by simp only [clusters, Nat.cast_pow]; positivity
  rw [div_le_div_iff₀ hA₀ ht₀]
  have h := mul_le_mul_of_nonneg_right (clusterSize_bounds s γ t hR).2 ht₀.le
  simpa only [clusters, Nat.cast_pow, pow_succ, Nat.cast_mul, mul_assoc] using h

theorem radius_over_special (d s : ℕ) (γ : ℝ) (t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (clusterSize s γ t : ℝ) / special d s t ≤ γ / t := by
  have hA₀ : (0 : ℝ) < clusters s t := by
    have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    simp only [clusters, Nat.cast_pow]
    positivity
  have hmA : (clusters s t : ℝ) ≤ special d s t := by
    have h : clusters s t ≤ special d s t := by
      simpa [special] using Nat.mul_le_mul_right (clusters s t) hd
    exact_mod_cast h
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hA₀ hmA).trans
    (radius_over_clusters s γ t ht hR)

theorem log_over_radius (d s : ℕ) (γ : ℝ) (t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hγ : 0 < γ)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    Real.log (special d s t) / clusterSize s γ t ≤ 2 * logConstant d s / (γ * t) := by
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hR₀ : (0 : ℝ) < clusterSize s γ t := by
    exact_mod_cast (show 0 < clusterSize s γ t by have := clusterSize_pos s γ t hR; omega)
  have hpow : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ (s + 2) :=
    pow_le_pow_right₀ ht₁ (by omega)
  have hrlow : (γ / 2) * (t : ℝ) ^ 2 ≤ clusterSize s γ t :=
    (mul_le_mul_of_nonneg_left hpow (by positivity)).trans (clusterSize_bounds s γ t hR).1
  have hlog := log_special_le d s t hd ht
  have hleft := mul_le_mul_of_nonneg_right hlog (show 0 ≤ γ * (t : ℝ) by positivity)
  have hright := mul_le_mul_of_nonneg_left hrlow
    (show 0 ≤ 2 * logConstant d s by have := logConstant_nonneg d s hd; positivity)
  rw [div_le_div_iff₀ hR₀ (mul_pos hγ ht₀)]
  nlinarith

theorem radius_le_special (d s : ℕ) (γ : ℝ) (t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hγ : γ ≤ 1)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (clusterSize s γ t : ℝ) ≤ special d s t := by
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hγpow : γ * (t : ℝ) ^ (s + 2) ≤ (t : ℝ) ^ (s + 2) := by
    simpa using mul_le_mul_of_nonneg_right hγ (show 0 ≤ (t : ℝ) ^ (s + 2) by positivity)
  have hpow : (t : ℝ) ^ (s + 2) ≤ (clusters s t : ℝ) := by
    simpa [clusters] using pow_le_pow_right₀ ht₁ (show s + 2 ≤ s + 3 by omega)
  have hmA : (clusters s t : ℝ) ≤ special d s t := by exact_mod_cast special_ge_clusters d s t hd
  exact (clusterSize_bounds s γ t hR).2 |>.trans hγpow |>.trans hpow |>.trans hmA

theorem radius_ge_fixed (s : ℕ) (γ L : ℝ) (t : ℕ)
    (ht : 1 ≤ t) (hγ : 0 < γ) (hL : 2 * L / γ ≤ (t : ℝ))
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    L ≤ clusterSize s γ t := by
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hp : (t : ℝ) ≤ (t : ℝ) ^ (s + 2) := by
    simpa using pow_le_pow_right₀ ht₁ (show 1 ≤ s + 2 by omega)
  have hr := (mul_le_mul_of_nonneg_left hp (show 0 ≤ γ / 2 by positivity)).trans
    (clusterSize_bounds s γ t hR).1
  have h := (div_le_iff₀ hγ).mp hL
  linarith

theorem log_le_radius (d s : ℕ) (γ : ℝ) (t : ℕ)
    (hd : 1 ≤ d) (ht : 1 ≤ t) (hγ : 0 < γ)
    (hL : 2 * logConstant d s / γ ≤ (t : ℝ))
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    Real.log (special d s t) ≤ clusterSize s γ t := by
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht₀ : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hp : (t : ℝ) ^ 2 ≤ (t : ℝ) ^ (s + 2) := pow_le_pow_right₀ ht₁ (by omega)
  have hr := (mul_le_mul_of_nonneg_left hp (show 0 ≤ γ / 2 by positivity)).trans
    (clusterSize_bounds s γ t hR).1
  have h' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hγ).mp hL) ht₀
  have hlog := log_special_le d s t hd ht
  nlinarith

theorem log_over_special (d s t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    Real.log (special d s t) / special d s t ≤ logConstant d s / t := by
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hm₀ : (0 : ℝ) < special d s t := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < t) (special_ge_t d s t hd ht))
  have hA2 : (t : ℝ) ^ 2 ≤ (clusters s t : ℝ) := by
    simpa [clusters] using pow_le_pow_right₀ ht₁ (show 2 ≤ s + 3 by omega)
  have hmA : (clusters s t : ℝ) ≤ special d s t := by exact_mod_cast special_ge_clusters d s t hd
  have hlog := mul_le_mul_of_nonneg_right (log_special_le d s t hd ht) ht₀.le
  have hbound := mul_le_mul_of_nonneg_left (hA2.trans hmA) (logConstant_nonneg d s hd)
  rw [div_le_div_iff₀ hm₀ ht₀]
  nlinarith

theorem inverse_cube_special (d s t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    1 / (special d s t : ℝ) ^ 3 ≤ 1 / t := by
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have htm : (t : ℝ) ≤ special d s t := by exact_mod_cast special_ge_t d s t hd ht
  have hm₁ : (1 : ℝ) ≤ special d s t := by
    exact_mod_cast (show 1 ≤ special d s t by have := special_ge_t d s t hd ht; omega)
  have hp : (special d s t : ℝ) ≤ (special d s t : ℝ) ^ 3 := by
    simpa using pow_le_pow_right₀ hm₁ (show 1 ≤ 3 by norm_num)
  exact one_div_le_one_div_of_le ht₀ (htm.trans hp)

theorem eventual_conditions (d s : ℕ) (hd : 1 ≤ d) (γ c L : ℝ)
    (hγ : 0 < γ) (hγ₁ : γ ≤ 1) (hc : 0 < c) (A₀ m₀ : ℕ) :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      1 ≤ t ∧ A₀ ≤ clusters s t ∧ m₀ ≤ special d s t ∧
      L ≤ clusterSize s γ t ∧ (clusterSize s γ t : ℝ) ≤ special d s t ∧
      Real.log (special d s t) ≤ clusterSize s γ t ∧
      2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 := by
  obtain ⟨tf, htf, hfloor⟩ := eventual_floor_conditions s γ c hγ hc
  let B : ℝ := 1 + tf + A₀ + m₀ + |2 * L / γ| + |2 * logConstant d s / γ|
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt B
  refine ⟨t₀, ?_⟩
  intro t ht
  have htR : (t₀ : ℝ) ≤ t := by exact_mod_cast ht
  have htf₀ : (0 : ℝ) ≤ tf := Nat.cast_nonneg tf
  have hA₀ : (0 : ℝ) ≤ A₀ := Nat.cast_nonneg A₀
  have hm₀ : (0 : ℝ) ≤ m₀ := Nat.cast_nonneg m₀
  have htF : tf ≤ t := by
    have h : (tf : ℝ) ≤ t := by dsimp [B] at ht₀; linarith [abs_nonneg (2 * L / γ), abs_nonneg (2 * logConstant d s / γ)]
    exact_mod_cast h
  have ht₁ : 1 ≤ t := htf.trans htF
  have htA : A₀ ≤ t := by
    have h : (A₀ : ℝ) ≤ t := by dsimp [B] at ht₀; linarith [abs_nonneg (2 * L / γ), abs_nonneg (2 * logConstant d s / γ)]
    exact_mod_cast h
  have htm : m₀ ≤ t := by
    have h : (m₀ : ℝ) ≤ t := by dsimp [B] at ht₀; linarith [abs_nonneg (2 * L / γ), abs_nonneg (2 * logConstant d s / γ)]
    exact_mod_cast h
  have htL : 2 * L / γ ≤ (t : ℝ) := by
    dsimp [B] at ht₀
    linarith [le_abs_self (2 * L / γ), abs_nonneg (2 * logConstant d s / γ)]
  have htlog : 2 * logConstant d s / γ ≤ (t : ℝ) := by
    dsimp [B] at ht₀
    linarith [le_abs_self (2 * logConstant d s / γ), abs_nonneg (2 * L / γ)]
  obtain ⟨hR, hq⟩ := hfloor t htF
  exact ⟨ht₁, htA.trans (clusters_ge_t s t ht₁), htm.trans (special_ge_t d s t hd ht₁),
    radius_ge_fixed s γ L t ht₁ hγ htL hR, radius_le_special d s γ t hd ht₁ hγ₁ hR,
    log_le_radius d s γ t hd ht₁ hγ htlog hR, hR, hq⟩

end ParameterGeometry

end SteinerLowerBound

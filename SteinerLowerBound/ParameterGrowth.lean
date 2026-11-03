module

public import SteinerLowerBound.Exponents

@[expose] public section

namespace SteinerLowerBound

namespace ParameterGrowth

def clusters (s t : ℕ) : ℕ := t ^ (s + 3)
noncomputable def clusterSize (s : ℕ) (γ : ℝ) (t : ℕ) : ℕ := ⌊γ * (t : ℝ) ^ (s + 2)⌋₊
def special (d s t : ℕ) : ℕ := d * clusters s t
noncomputable def ordinary (s : ℕ) (γ : ℝ) (t : ℕ) : ℕ := clusters s t * clusterSize s γ t
noncomputable def points (d s : ℕ) (γ : ℝ) (t : ℕ) : ℕ :=
  (d + 1) * ordinary s γ t + special d s t
noncomputable def queries (s : ℕ) (γ c : ℝ) (t : ℕ) : ℕ :=
  ⌊c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2⌋₊

theorem clusterSize_bounds (s : ℕ) (γ : ℝ) (t : ℕ)
    (h : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (γ / 2) * (t : ℝ) ^ (s + 2) ≤ clusterSize s γ t ∧
      (clusterSize s γ t : ℝ) ≤ γ * (t : ℝ) ^ (s + 2) := by
  have hb := Exponents.floor_bounds h
  simpa only [clusterSize, div_mul_eq_mul_div] using hb

theorem clusterSize_pos (s : ℕ) (γ : ℝ) (t : ℕ)
    (h : 2 ≤ γ * (t : ℝ) ^ (s + 2)) : 1 ≤ clusterSize s γ t := by
  have hb := (clusterSize_bounds s γ t h).1
  have : (1 : ℝ) ≤ clusterSize s γ t := by linarith
  exact_mod_cast this

theorem points_le (d s : ℕ) (γ : ℝ) (t : ℕ) (hR : 1 ≤ clusterSize s γ t) :
    points d s γ t ≤ (2 * d + 1) * ordinary s γ t := by
  have h := Nat.mul_le_mul_left (d * clusters s t) hR
  unfold points ordinary special
  nlinarith

theorem points_growth (d s : ℕ) (γ : ℝ) (t : ℕ) (_hγ : 0 ≤ γ)
    (h : 2 ≤ γ * (t : ℝ) ^ (s + 2)) :
    (points d s γ t : ℝ) ≤ ((2 * d + 1 : ℕ) : ℝ) * γ * (t : ℝ) ^ (2 * s + 5) := by
  have hn : (points d s γ t : ℝ) ≤ ((2 * d + 1 : ℕ) : ℝ) * ordinary s γ t := by
    exact_mod_cast points_le d s γ t (clusterSize_pos s γ t h)
  have hr := (clusterSize_bounds s γ t h).2
  have hm := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ clusters s t by positivity)
  calc
    _ ≤ ((2 * d + 1 : ℕ) : ℝ) * ordinary s γ t := hn
    _ ≤ ((2 * d + 1 : ℕ) : ℝ) * ((clusters s t : ℝ) * (γ * (t : ℝ) ^ (s + 2))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [ordinary, Nat.cast_mul] using hm
    _ = _ := by
      simp only [clusters, Nat.cast_pow]
      rw [Exponents.size_balance]
      ring

theorem queries_growth (s : ℕ) (γ c : ℝ) (t : ℕ) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hR : 2 ≤ γ * (t : ℝ) ^ (s + 2))
    (hq : 2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2) :
    (c * γ ^ 2 / 8) * (t : ℝ) ^ (3 * s + 7) ≤ queries s γ c t := by
  have hq' := (Exponents.floor_bounds hq).1
  have hr := (clusterSize_bounds s γ t hR).1
  have hsq := pow_le_pow_left₀ (show 0 ≤ (γ / 2) * (t : ℝ) ^ (s + 2) by positivity) hr 2
  have hmul := mul_le_mul_of_nonneg_left hsq
    (show 0 ≤ c * (clusters s t : ℝ) / 2 by positivity)
  calc
    _ = (c / 2) * ((t : ℝ) ^ (s + 3) * ((γ / 2) * (t : ℝ) ^ (s + 2)) ^ 2) := by
      rw [Exponents.query_balance]
      ring
    _ ≤ (c / 2) * ((clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2) := by
      convert hmul using 1 <;> simp only [clusters, Nat.cast_pow] <;> ring
    _ ≤ queries s γ c t := by
      dsimp only [queries]
      convert hq' using 1
      ring

theorem query_exponent_scale (d s : ℕ) (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℕ,
      2 ≤ γ * (t : ℝ) ^ (s + 2) →
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 →
      k * (points d s γ t : ℝ) ^ Exponents.lowerExponent s ≤ (queries s γ c t : ℝ) / 10 := by
  let C := ((2 * d + 1 : ℕ) : ℝ) * γ
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : 0 ≤ Exponents.lowerExponent s := by unfold Exponents.lowerExponent; positivity
  have hCp : 0 < C ^ Exponents.lowerExponent s := Real.rpow_pos_of_pos hC _
  let k := c * γ ^ 2 / (80 * C ^ Exponents.lowerExponent s)
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k, hk, ?_⟩
  intro t hR hq
  have hn := points_growth d s γ t hγ.le hR
  have hn' : (points d s γ t : ℝ) ≤ C * (t : ℝ) ^ (2 * s + 5) := by simpa [C] using hn
  have hrpow := Real.rpow_le_rpow (show (0 : ℝ) ≤ points d s γ t by positivity) hn' hb
  rw [Real.mul_rpow hC.le (by positivity), Exponents.balanced_rpow s (by positivity)] at hrpow
  have hscale := mul_le_mul_of_nonneg_left hrpow hk.le
  have hquery := queries_growth s γ c t hγ.le hc.le hR hq
  have heq : k * (C ^ Exponents.lowerExponent s * (t : ℝ) ^ (3 * s + 7)) =
      (c * γ ^ 2 / 80) * (t : ℝ) ^ (3 * s + 7) := by
    dsimp [k]
    field_simp
  rw [heq] at hscale
  linarith

theorem eventual_floor_conditions (s : ℕ) (γ c : ℝ) (hγ : 0 < γ) (hc : 0 < c) :
    ∃ t₀ : ℕ, 1 ≤ t₀ ∧ ∀ t : ℕ, t₀ ≤ t →
      2 ≤ γ * (t : ℝ) ^ (s + 2) ∧
      2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2 := by
  obtain ⟨t₀, ht₀⟩ := exists_nat_gt (max (1 : ℝ) (max (2 / γ) (2 / c)))
  refine ⟨t₀, ?_, ?_⟩
  · have : (1 : ℝ) < t₀ := (le_max_left _ _).trans_lt ht₀
    exact_mod_cast this.le
  · intro t ht
    have ht' : (t₀ : ℝ) ≤ t := by exact_mod_cast ht
    have ht₁ : (1 : ℝ) ≤ t := by linarith [le_max_left (1 : ℝ) (max (2 / γ) (2 / c))]
    have hp₂ : (t : ℝ) ≤ (t : ℝ) ^ (s + 2) := by
      simpa using pow_le_pow_right₀ ht₁ (show 1 ≤ s + 2 by omega)
    have hp₃ : (t : ℝ) ≤ (clusters s t : ℝ) := by
      simpa [clusters] using pow_le_pow_right₀ ht₁ (show 1 ≤ s + 3 by omega)
    have hγt : 2 ≤ γ * (t : ℝ) := by
      have h := (le_max_left (2 / γ) (2 / c)).trans (le_max_right (1 : ℝ) _)
      have hb : 2 / γ ≤ (t : ℝ) := by linarith
      have := (div_le_iff₀ hγ).mp hb
      nlinarith
    have hcA : 2 ≤ c * (clusters s t : ℝ) := by
      have h := (le_max_right (2 / γ) (2 / c)).trans (le_max_right (1 : ℝ) _)
      have hb : 2 / c ≤ (t : ℝ) := by linarith
      have := (div_le_iff₀ hc).mp hb
      nlinarith
    have hR : 2 ≤ γ * (t : ℝ) ^ (s + 2) :=
      hγt.trans (mul_le_mul_of_nonneg_left hp₂ hγ.le)
    have hR₁ : (1 : ℝ) ≤ clusterSize s γ t := by exact_mod_cast clusterSize_pos s γ t hR
    have hsq : (1 : ℝ) ≤ (clusterSize s γ t : ℝ) ^ 2 := by nlinarith
    refine ⟨hR, hcA.trans ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ c * (clusters s t : ℝ) by positivity)]

end ParameterGrowth

end SteinerLowerBound

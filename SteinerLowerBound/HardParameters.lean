module

public import SteinerLowerBound.HardFamily
public import SteinerLowerBound.MasterBound
public import SteinerLowerBound.MetricComparison.Parameters

@[expose] public section

namespace SteinerLowerBound

open HardDistribution ParameterGrowth

namespace HardFamily.Family

variable {η : ℝ} {s : ℕ}

noncomputable def radiusThreshold (f : HardFamily.Family η s) : ℝ :=
  16 * MetricComparison.parameterScale f.d f.H0 f.weights.bound

theorem radius_properties (f : HardFamily.Family η s) {R : ℝ}
    (hR : f.radiusThreshold ≤ R) :
    0 < R ∧
      2 * f.H0 * f.weights.bound ^ f.d ≤ (f.d : ℝ) * R ∧
      anchorConstant f.d f.H0 f.weights.bound / R ≤ 1 / 2 := by
  let L := MetricComparison.parameterScale f.d f.H0 f.weights.bound
  have hL : 1 ≤ L := by
    dsimp [L, MetricComparison.parameterScale]
    linarith [abs_nonneg (f.H0 * f.weights.bound ^ f.d),
      abs_nonneg (anchorConstant f.d f.H0 f.weights.bound),
      abs_nonneg (24 * (f.H0 * f.weights.bound ^ f.d) * (f.d.choose 3 : ℝ) / f.d)]
  have hA : f.H0 * f.weights.bound ^ f.d ≤ L := by
    dsimp [L, MetricComparison.parameterScale]
    linarith [le_abs_self (f.H0 * f.weights.bound ^ f.d),
      abs_nonneg (anchorConstant f.d f.H0 f.weights.bound),
      abs_nonneg (24 * (f.H0 * f.weights.bound ^ f.d) * (f.d.choose 3 : ℝ) / f.d)]
  have hB : anchorConstant f.d f.H0 f.weights.bound ≤ L := by
    dsimp [L, MetricComparison.parameterScale]
    linarith [abs_nonneg (f.H0 * f.weights.bound ^ f.d),
      le_abs_self (anchorConstant f.d f.H0 f.weights.bound),
      abs_nonneg (24 * (f.H0 * f.weights.bound ^ f.d) * (f.d.choose 3 : ℝ) / f.d)]
  change 16 * L ≤ R at hR
  have hRp : 0 < R := by linarith
  have hd : (1 : ℝ) ≤ f.d := by exact_mod_cast (show 1 ≤ f.d by have := f.d_ge_four; omega)
  have hmul := mul_le_mul_of_nonneg_right hd hRp.le
  refine ⟨hRp, by nlinarith, ?_⟩
  rw [div_le_iff₀ hRp]
  linarith

structure Conditions (f : HardFamily.Family η s) (γ c : ℝ) (t : ℕ) : Prop where
  index_pos : 1 ≤ t
  clusters_large : 64 ≤ clusters s t
  special_degree : f.d ≤ special f.d s t
  special_large : 16 ≤ special f.d s t
  radius_large : f.radiusThreshold ≤ clusterSize s γ t
  radius_le_special : (clusterSize s γ t : ℝ) ≤ special f.d s t
  log_le_radius : Real.log (special f.d s t) ≤ clusterSize s γ t
  radius_floor : 2 ≤ γ * (t : ℝ) ^ (s + 2)
  query_floor : 2 ≤ c * (clusters s t : ℝ) * (clusterSize s γ t : ℝ) ^ 2

theorem exists_parameters (f : HardFamily.Family η s)
    (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ γ c : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 0 < c ∧ c ≤ 1 ∧
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        f.Conditions γ c t ∧ C * MasterParameters.master f.d s γ c t ≤ ε := by
  have hd : 1 ≤ f.d := by have := f.d_ge_four; omega
  obtain ⟨γ, c, hγ, hγ₁, hc, hc₁, t₀, ht₀⟩ :=
    MasterParameters.exists_small f.d s hd C ε hC hε f.radiusThreshold 64 (max f.d 16)
  refine ⟨γ, c, hγ, hγ₁, hc, hc₁, t₀, ?_⟩
  intro t ht
  obtain ⟨ht₁, hA, hm, hR, hRm, hlog, hRf, hqf, hsmall⟩ := ht₀ t ht
  exact ⟨
    { index_pos := ht₁
      clusters_large := hA
      special_degree := (le_max_left f.d 16).trans hm
      special_large := (le_max_right f.d 16).trans hm
      radius_large := hR
      radius_le_special := hRm
      log_le_radius := hlog
      radius_floor := hRf
      query_floor := hqf },
    hsmall⟩

end HardFamily.Family

end SteinerLowerBound

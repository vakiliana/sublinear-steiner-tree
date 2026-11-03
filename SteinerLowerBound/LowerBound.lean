module

public import SteinerLowerBound.HardInstanceReduction
public import SteinerLowerBound.TranscriptBound

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound

universe u

open HardDistribution ParameterGrowth MetricComparison
open scoped Classical

namespace HardFamily.Family

variable {η : ℝ} {s : ℕ}

noncomputable def comparisonConstant (f : HardFamily.Family η s) : ℝ :=
  TranscriptBound.comparisonConstant f.d s f.H0 f.weights.bound

theorem comparisonConstant_pos (f : HardFamily.Family η s) : 0 < f.comparisonConstant :=
  TranscriptBound.comparisonConstant_pos _ _ _ _

end HardFamily.Family

namespace HardInstance

variable {η : ℝ} {s n : ℕ}

theorem outputs_close (M : HardInstance η s n)
    (hsmall : M.family.comparisonConstant *
      MasterParameters.master M.family.d s M.gamma M.coefficient M.index ≤ 1 / 10)
    (t : DecisionTree (Public.Queries M.Specials M.Clusters M.Slots M.Centers)
      Screening.Reply Bool) (ht : t.NoRepeats)
    (hq : Screening.DecisionTree.Bounded t M.queryBudget) :
    Law.Close (Public.metricOutputLaw M.setup M.family.weights.yes t)
      (Public.metricOutputLaw M.setup M.family.weights.no t) (1 / 10) := by
  let k := M.setup
  have hR : 16 * scale k ≤ k.R := by
    rw [scale_eq_parameters]
    change 16 * parameterScale M.family.d M.family.H0 M.family.weights.bound ≤
      (Fintype.card M.Slots : ℝ)
    simpa only [HardFamily.Family.radiusThreshold, Slots, Fintype.card_fin] using
      M.conditions.radius_large
  have hm : 16 ≤ Fintype.card M.Specials := by
    simpa only [Specials, Fintype.card_fin] using M.conditions.special_large
  have hM : 0 < k.M := by
    change 0 < M.family.weights.bound
    linarith [M.family.bound_ge_one]
  have hhalf : anchorConstant k.d k.H0 k.M / k.R ≤ 1 / 2 := by
    change anchorConstant M.family.d M.family.H0 M.family.weights.bound /
      (Fintype.card M.Slots : ℝ) ≤ 1 / 2
    simpa only [Slots, Fintype.card_fin] using
      (M.family.radius_properties M.conditions.radius_large).2.2
  have hS : Fintype.card M.Specials = k.d * Fintype.card M.Clusters := by
    change Fintype.card (Fin (M.family.d * clusters s M.index)) =
      M.family.d * Fintype.card (Fin (clusters s M.index))
    simp only [Fintype.card_fin]
  have hA : 64 ≤ Fintype.card M.Clusters := by
    simpa only [Clusters, Fintype.card_fin] using M.conditions.clusters_large
  have hC : (Fintype.card M.Centers : ℝ) = (Fintype.card M.Specials : ℝ) * k.R := by
    change (Fintype.card M.Centers : ℝ) =
      (Fintype.card M.Specials : ℝ) * Fintype.card M.Slots
    simp only [Centers, Specials, Slots, Fintype.card_fin, Nat.cast_mul]
  have hRm : k.R ≤ Fintype.card M.Specials := by
    change (Fintype.card M.Slots : ℝ) ≤ Fintype.card M.Specials
    simpa only [Slots, Specials, Fintype.card_fin] using M.conditions.radius_le_special
  have hlog : Real.log (Fintype.card M.Specials) ≤ k.R := by
    change Real.log (Fintype.card M.Specials) ≤ (Fintype.card M.Slots : ℝ)
    simpa only [Slots, Specials, Fintype.card_fin] using M.conditions.log_le_radius
  have hclose := TranscriptBound.metric_outputs_close k
    M.family.weights.yes M.family.weights.no hR hm hM hhalf hS hA rfl hC hRm hlog
    (s + 2) M.family.weights.moments t ht M.queryBudget hq
  apply hclose.mono
  have hbound := TranscriptBound.error_le_balance k s M.queryBudget rfl (by omega)
    (by omega : 0 < Fintype.card M.Clusters) hRm hM.le
  apply hbound.trans
  convert hsmall using 1 <;>
    simp only [HardFamily.Family.comparisonConstant, MasterParameters.master, k,
      queryBudget, Specials, Clusters, Slots, Fintype.card_fin]

end HardInstance

/-- Every sufficiently large size admits a three-distance metric family with
linear many terminals on which every successful randomized estimator needs
`Ω(n^((3s+7)/(2s+5)))` expected distance queries. -/
theorem lower_bound {η : ℝ} (hη : 0 < η) (hη₁ : η < 1) (s : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ D : ℕ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : HardInstance η s n, M.Geometry D ∧ HardInstance.Hard.{u} M κ := by
  obtain ⟨f⟩ := HardFamily.exists_family hη s
  obtain ⟨γ, c, hγ, _, hc, _, t₀, ht₀⟩ :=
    f.exists_parameters f.comparisonConstant (1 / 10) f.comparisonConstant_pos (by norm_num)
  have hd : 1 ≤ f.d := by have := f.d_ge_four; omega
  obtain ⟨κ, hκ, N, hN⟩ := AllSizes.eventual_all_sizes f.d s γ c hd hγ hc t₀
  let D := AllSizes.ratio s * (2 * f.d + 1)
  have hD : 0 < D := by dsimp [D, AllSizes.ratio]; positivity
  refine ⟨κ, hκ, D, hD, N, ?_⟩
  intro n hn
  obtain ⟨t, ht, _, _, _, hbelow, habove, _, hscale⟩ := hN n hn
  obtain ⟨hconditions, hsmall⟩ := ht₀ t ht
  let M : HardInstance η s n :=
    { family := f
      gamma := γ
      coefficient := c
      index := t
      conditions := hconditions
      below := hbelow
      above := habove }
  refine ⟨M, ?_, ?_⟩
  · exact M.geometry
  · exact M.hard_of_outputs_close hη hη₁ κ hscale (M.outputs_close hsmall)

theorem epsilon_lower_bound {η ε : ℝ}
    (hη : 0 < η) (hη₁ : η < 1) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ κ : ℝ, 0 < κ ∧
      ∃ D : ℕ, 0 < D ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ M : HardInstance η s n, M.Geometry D ∧ HardInstance.HardExponent.{u} M κ (3 / 2 - ε) := by
  obtain ⟨s, hs, hb⟩ := Exponents.exists_lowerExponent hε
  obtain ⟨κ, hκ, D, hD, N, hN⟩ := lower_bound.{u} hη hη₁ s
  refine ⟨s, hs, κ, hκ, D, hD, N, ?_⟩
  intro n hn
  obtain ⟨M, hgeometry, hhard⟩ := hN n hn
  exact ⟨M, hgeometry, M.hard_smaller_exponent κ (3 / 2 - ε) hκ.le hb.le hhard⟩

end SteinerLowerBound

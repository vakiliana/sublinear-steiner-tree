module

public import SteinerLowerBound.HardInstance
public import SteinerLowerBound.MetricComparison.PublicLaw
public import SteinerLowerBound.LawOperations

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound.HardInstance

open HardDistribution ParameterGrowth MetricComparison
open scoped Classical ENNReal
open MeasureTheory

universe u

variable {η : ℝ} {s n : ℕ}

noncomputable def offset (M : HardInstance η s n) : ℝ :=
  M.ell * Fintype.card M.Clusters * ((Fintype.card M.Slots : ℝ) - 1)

theorem offset_le_one (M : HardInstance η s n) : M.offset ≤ 1 := by
  simpa only [offset, ell, Clusters, Slots, Fintype.card_fin] using
    ParameterGeometry.offset_le_one (clusters s M.index) (clusterSize s M.gamma M.index)
      (by have := M.conditions.clusters_large; omega)
      (clusterSize_pos s M.gamma M.index M.conditions.radius_floor)

noncomputable def yesCost (M : HardInstance η s n) : ℝ :=
  Testing.yesCost η (Fintype.card M.Specials) M.offset

noncomputable def noCost (M : HardInstance η s n) : ℝ :=
  Testing.noCost η (Fintype.card M.Specials) M.offset

theorem cost_gap (M : HardInstance η s n) (hη : 0 < η) (hη₁ : η < 1) :
    (2 - η) * M.yesCost < M.noCost :=
  Testing.cost_gap hη hη₁ (Nat.cast_nonneg _) (M.offset_le_one.trans_lt (by norm_num))

noncomputable def inputLaw (M : HardInstance η s n) (μ : Law M.family.weights.Carrier) :
    Law M.Input := by
  let sampled := PublicLaw.law (S := M.Specials) (G := M.Clusters)
    (I := M.Slots) (C := M.Centers) M.setup μ
  exact @LawOperations.withFintype M.Input _ _ sampled

theorem public_optimum (M : HardInstance η s n) (ω : M.Input) :
    M.optimum ω = PublicLaw.optimum M.setup M.ell ω :=
  M.optimum_unpadded ω

theorem cost_probabilities (M : HardInstance η s n) (hη : 0 < η) :
    (M.inputLaw M.family.weights.yes).prob {ω | M.yesCost < M.optimum ω} ≤ 1 / 100 ∧
      (M.inputLaw M.family.weights.no).prob {ω | M.optimum ω < M.noCost} ≤ 1 / 100 := by
  have hm : M.family.d ≤ Fintype.card M.Specials := by
    simpa only [Specials, Fintype.card_fin] using M.conditions.special_degree
  have hmass : 2 * M.family.H0 * M.family.weights.bound ^ M.family.d ≤
      (M.family.d : ℝ) * Fintype.card M.Slots := by
    simpa only [Slots, Fintype.card_fin] using
      (M.family.radius_properties M.conditions.radius_large).2.1
  have hS : (Fintype.card M.Specials : ℝ) =
      (M.family.d : ℝ) * Fintype.card M.Clusters := by
    change (Fintype.card (Fin (M.family.d * clusters s M.index)) : ℝ) =
      (M.family.d : ℝ) * Fintype.card (Fin (clusters s M.index))
    simp only [Fintype.card_fin, Nat.cast_mul]
  have hC : (Fintype.card M.Centers : ℝ) =
      (Fintype.card M.Specials : ℝ) * Fintype.card M.Slots := by
    simp only [← Nat.card_eq_fintype_card, Centers, Specials, Slots, Nat.card_fin, Nat.cast_mul]
  have h := PublicLaw.cost_separation (S := M.Specials) (G := M.Clusters)
    (I := M.Slots) (C := M.Centers) M.family hη hm hmass hS hC
    M.ell_pos.le (M.ell_le_one.trans (by norm_num))
  simpa only [inputLaw, LawOperations.prob_withFintype, yesCost, noCost, offset,
    public_optimum] using h

theorem padded_outputs_close (M : HardInstance η s n)
    (htv : ∀ t : DecisionTree (Public.Queries M.Specials M.Clusters M.Slots M.Centers)
        Screening.Reply Bool, t.NoRepeats → Screening.DecisionTree.Bounded t M.queryBudget →
      Law.Close (Public.metricOutputLaw M.setup M.family.weights.yes t)
        (Public.metricOutputLaw M.setup M.family.weights.no t) (1 / 10))
    (t : DecisionTree M.Queries Screening.Reply Bool) (hnr : t.NoRepeats)
    (hb : Screening.DecisionTree.Bounded t M.queryBudget) :
    Law.Close
      ((M.inputLaw M.family.weights.yes).map (fun ω => t.output (M.oracle ω)))
      ((M.inputLaw M.family.weights.no).map (fun ω => t.output (M.oracle ω))) (1 / 10) := by
  let baseTree := MetricComparison.Padding.queryReduction.simulateOutput t
  have hc := htv baseTree (MetricComparison.Padding.simulate_public_noRepeats t hnr)
    (MetricComparison.Padding.simulate_public_bounded t M.queryBudget hb)
  have he (μ : Law M.family.weights.Carrier) :
      ((M.inputLaw μ).map (fun ω => t.output (M.oracle ω))) =
        Public.metricOutputLaw M.setup μ baseTree := by
    rw [inputLaw, LawOperations.map_withFintype, ← PublicLaw.outputLaw_eq_comparison]
    unfold PublicLaw.outputLaw
    congr 1
    funext ω
    exact (MetricComparison.Padding.simulate_public_output ω.2 (M.baseNeighbors ω) t).symm
  rwa [he, he]

theorem hard_of_outputs_close (M : HardInstance η s n) (hη : 0 < η) (hη₁ : η < 1)
    (κ : ℝ) (hscale : κ * (n : ℝ) ^ Exponents.lowerExponent s ≤ (M.queryBudget : ℝ) / 10)
    (htv : ∀ t : DecisionTree (Public.Queries M.Specials M.Clusters M.Slots M.Centers)
        Screening.Reply Bool, t.NoRepeats → Screening.DecisionTree.Bounded t M.queryBudget →
      Law.Close (Public.metricOutputLaw M.setup M.family.weights.yes t)
        (Public.metricOutputLaw M.setup M.family.weights.no t) (1 / 10)) :
    Hard.{u} M κ := by
  have : Nonempty Screening.Reply := ⟨.far⟩
  intro Γ _ coins _ algorithm hqueries hout hgood
  let encoded := fun γ => PublicLaw.RealAnswers.compile M.ell (algorithm γ)
  have hqe (γ : Γ) (ω : M.Input) :
      (encoded γ).queries (M.oracle ω) = (algorithm γ).queries (M.realOracle ω) :=
    PublicLaw.RealAnswers.queries M.ell (algorithm γ) (M.oracle ω)
  have hoe (γ : Γ) (ω : M.Input) :
      (encoded γ).output (M.oracle ω) = (algorithm γ).output (M.realOracle ω) :=
    PublicLaw.RealAnswers.output M.ell (algorithm γ) (M.oracle ω)
  have hqueries' (ω : M.Input) : Measurable (fun γ =>
      (encoded γ).queries (M.oracle ω)) := by
    simpa only [hqe] using hqueries ω
  have hout' (ω : M.Input) : Measurable (fun γ =>
      (encoded γ).output (M.oracle ω)) := by
    simpa only [hoe] using hout ω
  have hgood' (ω : M.Input) : 2 / 3 ≤ coins.real {γ |
      GoodEstimate (2 - η) (M.optimum ω) ((encoded γ).output (M.oracle ω))} := by
    simpa only [hoe] using hgood ω
  obtain ⟨ω, hω⟩ := DistributionalLowerBound.expected_queries
    (M.inputLaw M.family.weights.yes) (M.inputLaw M.family.weights.no) M.oracle M.optimum
    (2 - η) M.yesCost M.noCost (by linarith) (M.cost_gap hη hη₁)
    (M.cost_probabilities hη).1 (M.cost_probabilities hη).2 M.queryBudget M.queryBudget_pos
    (fun t hn hb => M.padded_outputs_close htv t hn hb) coins encoded hqueries' hout' hgood'
  refine ⟨ω, (ENNReal.ofReal_le_ofReal hscale).trans_lt ?_⟩
  simpa only [hqe] using hω

end SteinerLowerBound.HardInstance

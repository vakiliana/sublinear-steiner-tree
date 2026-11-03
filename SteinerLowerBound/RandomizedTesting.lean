module

public import SteinerLowerBound.Testing
public import SteinerLowerBound.ProductProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical ENNReal
open MeasureTheory

namespace RandomizedTesting

variable {Ω Γ : Type*} [Fintype Ω] [MeasurableSpace Γ]

omit [MeasurableSpace Γ] in
theorem indicator_one (P : Γ → Prop) :
    ({γ | P γ}.indicator (fun _ => (1 : ℝ))) = (fun γ => if P γ then 1 else 0) := by
  funext γ
  by_cases h : P γ <;> simp [h]

theorem integrable_indicator (μ : Measure Γ) [IsFiniteMeasure μ] (P : Γ → Prop)
    (hP : MeasurableSet {γ | P γ}) :
    Integrable (fun γ => if P γ then (1 : ℝ) else 0) μ := by
  rw [← indicator_one P]
  exact (integrable_const (1 : ℝ)).indicator hP

theorem integrable_probability (inputs : Law Ω) (μ : Measure Γ) [IsFiniteMeasure μ]
    (P : Γ → Ω → Prop) (hP : ∀ ω, MeasurableSet {γ | P γ ω}) :
    Integrable (fun γ => inputs.prob {ω | P γ ω}) μ := by
  have heq : (fun γ => inputs.prob {ω | P γ ω}) =
      fun γ => ∑ ω, inputs.mass ω * (if P γ ω then (1 : ℝ) else 0) := by
    funext γ
    simpa only [Set.mem_ofPred_eq, Law.expect] using
      Law.prob_eq_expect inputs {ω | P γ ω}
  rw [heq]
  exact integrable_finsetSum _ (fun ω _ =>
    (integrable_indicator μ (fun γ => P γ ω) (hP ω)).const_mul (inputs.mass ω))

theorem fubini (inputs : Law Ω) (μ : Measure Γ) [IsFiniteMeasure μ]
    (P : Γ → Ω → Prop) (hP : ∀ ω, MeasurableSet {γ | P γ ω}) :
    (∫ γ, inputs.prob {ω | P γ ω} ∂μ) =
      inputs.expect (fun ω => μ.real {γ | P γ ω}) := by
  have heq : (fun γ => inputs.prob {ω | P γ ω}) =
      fun γ => ∑ ω, inputs.mass ω * (if P γ ω then (1 : ℝ) else 0) := by
    funext γ
    simpa only [Set.mem_ofPred_eq, Law.expect] using
      Law.prob_eq_expect inputs {ω | P γ ω}
  rw [heq, integral_finsetSum]
  · unfold Law.expect
    apply Finset.sum_congr rfl
    intro ω _
    rw [integral_const_mul]
    congr 1
    rw [← indicator_one (fun γ => P γ ω), integral_indicator_const (1 : ℝ) (hP ω)]
    simp
  · intro ω _
    exact (integrable_indicator μ (fun γ => P γ ω) (hP ω)).const_mul (inputs.mass ω)

theorem expected_query_reduction (inputs : Law Ω) (coins : Measure Γ) [IsProbabilityMeasure coins]
    (queries : Γ → Ω → ℕ) (good truncated : Γ → Ω → Prop)
    (hqueries : ∀ ω, Integrable (fun γ => (queries γ ω : ℝ)) coins)
    (hmeasurable : ∀ ω, MeasurableSet {γ | truncated γ ω})
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hgood : ∀ ω, 2 / 3 ≤ coins.real {γ | good γ ω})
    (hbounded : ∀ γ, inputs.prob {ω | truncated γ ω} ≤ β)
    (hpreserve : ∀ γ ω, good γ ω → queries γ ω ≤ q → truncated γ ω) :
    ∃ ω, (q : ℝ) / 10 < ∫ γ, (queries γ ω : ℝ) ∂coins := by
  classical
  by_contra h
  push Not at h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have htrunc (ω : Ω) : 17 / 30 ≤ coins.real {γ | truncated γ ω} := by
    have hs : {γ | good γ ω} ⊆ {γ | truncated γ ω} ∪ {γ | q < queries γ ω} := by
      intro γ hγ
      by_cases hqγ : queries γ ω ≤ q
      · exact Or.inl (hpreserve γ ω hγ hqγ)
      · exact Or.inr (Nat.lt_of_not_ge hqγ)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (fun γ => Nat.cast_nonneg (queries γ ω))) (hqueries ω) (q : ℝ)
    have htail : coins.real {γ | q < queries γ ω} ≤
        (∫ γ, (queries γ ω : ℝ) ∂coins) / q := by
      have hsub : {γ | q < queries γ ω} ⊆ {γ | (q : ℝ) ≤ (queries γ ω : ℝ)} := by
        intro γ hγ
        exact_mod_cast Nat.le_of_lt hγ
      apply (measureReal_mono hsub).trans
      rw [le_div_iff₀ hq']
      nlinarith
    have htail' : coins.real {γ | q < queries γ ω} ≤ 1 / 10 := by
      apply htail.trans
      rw [div_le_iff₀ hq']
      linarith [h ω]
    have hunion := (measureReal_mono (μ := coins) hs).trans (measureReal_union_le (μ := coins) _ _)
    linarith [hgood ω]
  have hleft := inputs.expect_mono htrunc
  rw [Law.expect_const, ← fubini inputs coins truncated hmeasurable] at hleft
  have hright := integral_mono (integrable_probability inputs coins truncated hmeasurable)
    (integrable_const β) hbounded
  have hr : (∫ γ, inputs.prob {ω | truncated γ ω} ∂coins) ≤ β := by simpa using hright
  linarith

theorem expected_query_lower_bound {Q A : Type*}
    (inputs : Law Ω) (coins : Measure Γ) [IsProbabilityMeasure coins]
    (oracle : Ω → Q → A) (opt : Ω → ℝ) (ratio : ℝ)
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hbounded : ∀ t : DecisionTree Q A ℝ, (∀ o, t.queries o ≤ q) →
      inputs.prob {ω | GoodEstimate ratio (opt ω) (t.output (oracle ω))} ≤ β)
    (algorithm : Γ → DecisionTree Q A ℝ)
    (hqueries : ∀ ω, Integrable (fun γ => ((algorithm γ).queries (oracle ω) : ℝ)) coins)
    (hmeasurable : ∀ ω, MeasurableSet {γ | GoodEstimate ratio (opt ω)
      (((algorithm γ).truncateWith 0 q).output (oracle ω))})
    (hgood : ∀ ω, 2 / 3 ≤ coins.real {γ |
      GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω))}) :
    ∃ ω, (q : ℝ) / 10 < ∫ γ, ((algorithm γ).queries (oracle ω) : ℝ) ∂coins := by
  apply expected_query_reduction inputs coins
    (fun γ ω => (algorithm γ).queries (oracle ω))
    (fun γ ω => GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω)))
    (fun γ ω => GoodEstimate ratio (opt ω)
      (((algorithm γ).truncateWith 0 q).output (oracle ω)))
    hqueries hmeasurable q hq β hβ hgood
  · intro γ
    exact hbounded _ (fun o => (algorithm γ).truncateWith_queries 0 o q)
  · intro γ ω hγω hqueries
    simpa only [(algorithm γ).truncateWith_output 0 (oracle ω) q hqueries] using hγω

theorem expected_query_reduction_extended (inputs : Law Ω) (coins : Measure Γ)
    [IsProbabilityMeasure coins] (queries : Γ → Ω → ℕ) (good truncated : Γ → Ω → Prop)
    (hqueries : ∀ ω, Measurable (fun γ => queries γ ω))
    (hmeasurable : ∀ ω, MeasurableSet {γ | truncated γ ω})
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hgood : ∀ ω, 2 / 3 ≤ coins.real {γ | good γ ω})
    (hbounded : ∀ γ, inputs.prob {ω | truncated γ ω} ≤ β)
    (hpreserve : ∀ γ ω, good γ ω → queries γ ω ≤ q → truncated γ ω) :
    ∃ ω, ENNReal.ofReal ((q : ℝ) / 10) < ∫⁻ γ, (queries γ ω : ℝ≥0∞) ∂coins := by
  classical
  by_cases hint : ∀ ω, Integrable (fun γ => (queries γ ω : ℝ)) coins
  · obtain ⟨ω, hω⟩ := expected_query_reduction inputs coins queries good truncated hint
      hmeasurable q hq β hβ hgood hbounded hpreserve
    have heq := ofReal_integral_eq_lintegral_ofReal (hint ω)
      (Filter.Eventually.of_forall (fun γ => Nat.cast_nonneg (queries γ ω)))
    simp only [ENNReal.ofReal_natCast] at heq
    refine ⟨ω, ?_⟩
    rw [← heq]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hω
  · push Not at hint
    obtain ⟨ω, hω⟩ := hint
    have hm : Measurable (fun γ => (queries γ ω : ℝ)) :=
      (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (hqueries ω)
    have heq := lintegral_ofReal_ne_top_iff_integrable (μ := coins) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun γ => Nat.cast_nonneg (queries γ ω)))
    have htop : (∫⁻ γ, (queries γ ω : ℝ≥0∞) ∂coins) = ∞ := by
      by_contra hne
      apply hω
      apply heq.mp
      simpa only [ENNReal.ofReal_natCast] using hne
    exact ⟨ω, by rw [htop]; exact ENNReal.ofReal_lt_top⟩

theorem expected_query_lower_bound_extended {Q A : Type*}
    (inputs : Law Ω) (coins : Measure Γ) [IsProbabilityMeasure coins]
    (oracle : Ω → Q → A) (opt : Ω → ℝ) (ratio : ℝ)
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hbounded : ∀ t : DecisionTree Q A ℝ, (∀ o, t.queries o ≤ q) →
      inputs.prob {ω | GoodEstimate ratio (opt ω) (t.output (oracle ω))} ≤ β)
    (algorithm : Γ → DecisionTree Q A ℝ)
    (hqueries : ∀ ω, Measurable (fun γ => (algorithm γ).queries (oracle ω)))
    (hmeasurable : ∀ ω, MeasurableSet {γ | GoodEstimate ratio (opt ω)
      (((algorithm γ).truncateWith 0 q).output (oracle ω))})
    (hgood : ∀ ω, 2 / 3 ≤ coins.real {γ |
      GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω))}) :
    ∃ ω, ENNReal.ofReal ((q : ℝ) / 10) <
      ∫⁻ γ, ((algorithm γ).queries (oracle ω) : ℝ≥0∞) ∂coins := by
  apply expected_query_reduction_extended inputs coins
    (fun γ ω => (algorithm γ).queries (oracle ω))
    (fun γ ω => GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω)))
    (fun γ ω => GoodEstimate ratio (opt ω)
      (((algorithm γ).truncateWith 0 q).output (oracle ω)))
    hqueries hmeasurable q hq β hβ hgood
  · intro γ
    exact hbounded _ (fun o => (algorithm γ).truncateWith_queries 0 o q)
  · intro γ ω hγω hqueries
    simpa only [(algorithm γ).truncateWith_output 0 (oracle ω) q hqueries] using hγω

end RandomizedTesting

end SteinerLowerBound

module

public import SteinerLowerBound.QueryBounds
public import SteinerLowerBound.RandomizedTesting

@[expose] public section

namespace SteinerLowerBound

open scoped Classical ENNReal
open MeasureTheory

namespace DistributionalLowerBound

variable {Ω Q A Γ : Type*} [Fintype Ω] [Fintype A] [Nonempty A]

noncomputable def hardLaw (μ ν : Law Ω) : Law Ω :=
  Law.mix (1 / 2) (by norm_num) (by norm_num) μ ν

theorem bounded_success (μ ν : Law Ω) (oracle : Ω → Q → A) (opt : Ω → ℝ)
    (ratio U V : ℝ) (hratio : 0 ≤ ratio) (hgap : ratio * U < V)
    (hy : μ.prob {ω | U < opt ω} ≤ 1 / 100)
    (hn : ν.prob {ω | opt ω < V} ≤ 1 / 100) (q : ℕ)
    (htv : ∀ t : DecisionTree Q A Bool, t.NoRepeats →
      Screening.DecisionTree.Bounded t q →
      Law.Close (μ.map (fun ω => t.output (oracle ω)))
        (ν.map (fun ω => t.output (oracle ω))) (1 / 10))
    (t : DecisionTree Q A ℝ) (ht : ∀ o, t.queries o ≤ q) :
    (hardLaw μ ν).prob {ω | GoodEstimate ratio (opt ω) (t.output (oracle ω))} ≤ 14 / 25 := by
  let test := (t.map (fun r => decide (r ≤ ratio * U))).memoize
  have htest : Screening.DecisionTree.Bounded test q :=
    (t.map (fun r => decide (r ≤ ratio * U))).memoize_bounded q
      (by intro o; simpa only [DecisionTree.queries_map] using ht o)
  have hc := htv test (DecisionTree.memoize_noRepeats _) htest {true}
  have he : (fun ω => decide (t.output (oracle ω) ≤ ratio * U)) ⁻¹' {true} =
      {ω | t.output (oracle ω) ≤ ratio * U} := by
    ext ω
    simp
  have hc' : |μ.prob {ω | t.output (oracle ω) ≤ ratio * U} -
      ν.prob {ω | t.output (oracle ω) ≤ ratio * U}| ≤ 1 / 10 := by
    simpa [Law.prob_map, test, DecisionTree.memoize_output, DecisionTree.output_map, he] using hc
  have h := Testing.estimation_to_testing μ ν opt (fun ω => t.output (oracle ω))
    ratio U V (1 / 10) hratio hgap hc'
  rw [hardLaw, Law.prob_mix]
  linarith

omit [Fintype A] [Nonempty A] in
theorem truncateWith_measurable [MeasurableSpace Γ]
    (algorithm : Γ → DecisionTree Q A ℝ) (oracle : Q → A) (q : ℕ)
    (hq : Measurable (fun γ => (algorithm γ).queries oracle))
    (hout : Measurable (fun γ => (algorithm γ).output oracle)) :
    Measurable (fun γ => ((algorithm γ).truncateWith 0 q).output oracle) := by
  have heq : (fun γ => ((algorithm γ).truncateWith 0 q).output oracle) =
      fun γ => if (algorithm γ).queries oracle ≤ q then (algorithm γ).output oracle else 0 := by
    funext γ
    by_cases h : (algorithm γ).queries oracle ≤ q
    · simp [h, DecisionTree.truncateWith_output _ _ _ _ h]
    · have hnone := ((algorithm γ).truncate_none_iff oracle q).mpr (Nat.lt_of_not_ge h)
      simp [h, DecisionTree.truncateWith, DecisionTree.output_map, hnone]
  rw [heq]
  exact Measurable.ite (measurableSet_le hq measurable_const) hout measurable_const

omit [Fintype A] [Nonempty A] in
theorem truncated_success_measurable [MeasurableSpace Γ]
    (algorithm : Γ → DecisionTree Q A ℝ) (oracle : Q → A) (q : ℕ)
    (opt ratio : ℝ)
    (hq : Measurable (fun γ => (algorithm γ).queries oracle))
    (hout : Measurable (fun γ => (algorithm γ).output oracle)) :
    MeasurableSet {γ | GoodEstimate ratio opt (((algorithm γ).truncateWith 0 q).output oracle)} := by
  have h := truncateWith_measurable algorithm oracle q hq hout
  exact (measurableSet_le measurable_const h).inter (measurableSet_le h measurable_const)

theorem expected_queries [MeasurableSpace Γ]
    (μ ν : Law Ω) (oracle : Ω → Q → A) (opt : Ω → ℝ)
    (ratio U V : ℝ) (hratio : 0 ≤ ratio) (hgap : ratio * U < V)
    (hy : μ.prob {ω | U < opt ω} ≤ 1 / 100)
    (hn : ν.prob {ω | opt ω < V} ≤ 1 / 100) (q : ℕ) (hq : 0 < q)
    (htv : ∀ t : DecisionTree Q A Bool, t.NoRepeats →
      Screening.DecisionTree.Bounded t q →
      Law.Close (μ.map (fun ω => t.output (oracle ω)))
        (ν.map (fun ω => t.output (oracle ω))) (1 / 10))
    (coins : Measure Γ) [IsProbabilityMeasure coins]
    (algorithm : Γ → DecisionTree Q A ℝ)
    (hqueries : ∀ ω, Measurable (fun γ => (algorithm γ).queries (oracle ω)))
    (hout : ∀ ω, Measurable (fun γ => (algorithm γ).output (oracle ω)))
    (hgood : ∀ ω, 2 / 3 ≤ coins.real {γ |
      GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω))}) :
    ∃ ω, ENNReal.ofReal ((q : ℝ) / 10) <
      ∫⁻ γ, ((algorithm γ).queries (oracle ω) : ℝ≥0∞) ∂coins := by
  exact RandomizedTesting.expected_query_lower_bound_extended (hardLaw μ ν) coins
    oracle opt ratio q hq (14 / 25) (by norm_num)
    (fun t ht => bounded_success μ ν oracle opt ratio U V hratio hgap hy hn q htv t ht)
    algorithm hqueries (fun ω => truncated_success_measurable algorithm (oracle ω) q
      (opt ω) ratio (hqueries ω) (hout ω)) hgood

end DistributionalLowerBound

end SteinerLowerBound

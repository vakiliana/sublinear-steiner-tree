module

public import SteinerLowerBound.QueryModel

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

def GoodEstimate (ratio opt estimate : ℝ) : Prop :=
  opt ≤ estimate ∧ estimate ≤ ratio * opt

namespace Testing

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem estimation_to_testing (μ ν : Law Ω) (opt estimate : Ω → ℝ)
    (ratio U V ε : ℝ) (hratio : 0 ≤ ratio) (hgap : ratio * U < V)
    (hclose : |μ.prob {ω | estimate ω ≤ ratio * U} -
      ν.prob {ω | estimate ω ≤ ratio * U}| ≤ ε) :
    (μ.prob {ω | GoodEstimate ratio (opt ω) (estimate ω)} +
      ν.prob {ω | GoodEstimate ratio (opt ω) (estimate ω)}) / 2 ≤
      (1 + ε) / 2 + (μ.prob {ω | U < opt ω} + ν.prob {ω | opt ω < V}) / 2 := by
  let E := {ω | estimate ω ≤ ratio * U}
  have hy : {ω | GoodEstimate ratio (opt ω) (estimate ω)} ⊆ E ∪ {ω | U < opt ω} := by
    intro ω hω
    by_cases h : U < opt ω
    · exact Or.inr h
    · exact Or.inl (hω.2.trans (mul_le_mul_of_nonneg_left (le_of_not_gt h) hratio))
  have hn : {ω | GoodEstimate ratio (opt ω) (estimate ω)} ⊆ Eᶜ ∪ {ω | opt ω < V} := by
    intro ω hω
    by_cases h : opt ω < V
    · exact Or.inr h
    · left
      change ¬estimate ω ≤ ratio * U
      linarith [hω.1, le_of_not_gt h]
  have hy' := (μ.prob_mono hy).trans (μ.prob_union_le E {ω | U < opt ω})
  have hn' := (ν.prob_mono hn).trans (ν.prob_union_le Eᶜ {ω | opt ω < V})
  rw [ν.prob_compl E] at hn'
  have ht := (abs_le.mp hclose).2
  dsimp [E] at *
  linarith

noncomputable def yesCost (η m z : ℝ) : ℝ := z + (1 + η / 50) * m - 2
noncomputable def noCost (η m z : ℝ) : ℝ := z + (2 - η / 50) * m - 2

theorem cost_gap_identity (η m z : ℝ) :
    noCost η m z - (2 - η) * yesCost η m z =
      (47 * η + η ^ 2) / 50 * m + (1 - η) * (2 - z) := by
  unfold noCost yesCost
  ring

theorem cost_gap {η m z : ℝ} (hη₀ : 0 < η) (hη₁ : η < 1)
    (hm : 0 ≤ m) (hz : z < 2) :
    (2 - η) * yesCost η m z < noCost η m z := by
  have hfirst : 0 ≤ (47 * η + η ^ 2) / 50 * m := by positivity
  have hsecond : 0 < (1 - η) * (2 - z) :=
    mul_pos (sub_pos.mpr hη₁) (sub_pos.mpr hz)
  have := cost_gap_identity η m z
  linarith

theorem fubini_prob (μ : Law Ω) (ν : Law Γ) (P : Ω → Γ → Prop) :
    μ.expect (fun ω => ν.prob {γ | P ω γ}) =
      ν.expect (fun γ => μ.prob {ω | P ω γ}) := by
  classical
  simp only [Law.expect, Law.prob, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω γ <;> simp [h, mul_comm]

theorem truncation_success (μ : Law Γ) (queries : Γ → ℕ)
    (good truncated : Set Γ) (q : ℕ) (hq : 0 < q)
    (hpreserve : ∀ γ ∈ good, queries γ ≤ q → γ ∈ truncated) :
    μ.prob good - μ.expect (fun γ => (queries γ : ℝ)) / q ≤ μ.prob truncated := by
  have hsubset : good ⊆ truncated ∪ {γ | q < queries γ} := by
    intro γ hγ
    by_cases h : queries γ ≤ q
    · exact Or.inl (hpreserve γ hγ h)
    · exact Or.inr (Nat.lt_of_not_ge h)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have htail :
      μ.prob {γ | q < queries γ} ≤ μ.expect (fun γ => (queries γ : ℝ)) / q := by
    apply (μ.prob_mono ?_).trans (μ.markov (fun γ => Nat.cast_nonneg (queries γ)) hq')
    intro γ hγ
    exact_mod_cast (Nat.le_of_lt hγ)
  have := (μ.prob_mono hsubset).trans (μ.prob_union_le truncated {γ | q < queries γ})
  linarith

theorem expected_query_reduction (inputs : Law Ω) (coins : Law Γ)
    (queries : Γ → Ω → ℕ) (good truncated : Γ → Ω → Prop)
    (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hgood : ∀ ω, 2 / 3 ≤ coins.prob {γ | good γ ω})
    (hbounded : ∀ γ, inputs.prob {ω | truncated γ ω} ≤ β)
    (hpreserve : ∀ γ ω, good γ ω → queries γ ω ≤ q → truncated γ ω) :
    ∃ ω, (q : ℝ) / 10 < coins.expect (fun γ => (queries γ ω : ℝ)) := by
  classical
  by_contra h
  push Not at h
  have htrunc : ∀ ω, 17 / 30 ≤ coins.prob {γ | truncated γ ω} := by
    intro ω
    have ht := truncation_success coins (fun γ => queries γ ω)
      {γ | good γ ω} {γ | truncated γ ω} q hq (fun γ hγ => hpreserve γ ω hγ)
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have he : coins.expect (fun γ => (queries γ ω : ℝ)) / q ≤ 1 / 10 := by
      rw [div_le_iff₀ hq']
      linarith [h ω]
    linarith [hgood ω]
  have hleft := inputs.expect_mono htrunc
  have hright := coins.expect_mono hbounded
  rw [Law.expect_const] at hleft hright
  rw [fubini_prob inputs coins (fun ω γ => truncated γ ω)] at hleft
  linarith

theorem expected_query_lower_bound {Q A : Type*}
    (inputs : Law Ω) (coins : Law Γ) (oracle : Ω → Q → A)
    (opt : Ω → ℝ) (ratio : ℝ) (q : ℕ) (hq : 0 < q) (β : ℝ) (hβ : β < 17 / 30)
    (hbounded : ∀ t : DecisionTree Q A ℝ,
      (∀ o, t.queries o ≤ q) →
      inputs.prob {ω | GoodEstimate ratio (opt ω) (t.output (oracle ω))} ≤ β)
    (algorithm : Γ → DecisionTree Q A ℝ)
    (hgood : ∀ ω, 2 / 3 ≤ coins.prob
      {γ | GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω))}) :
    ∃ ω, (q : ℝ) / 10 <
      coins.expect (fun γ => ((algorithm γ).queries (oracle ω) : ℝ)) := by
  apply expected_query_reduction inputs coins
    (fun γ ω => (algorithm γ).queries (oracle ω))
    (fun γ ω => GoodEstimate ratio (opt ω) ((algorithm γ).output (oracle ω)))
    (fun γ ω => GoodEstimate ratio (opt ω)
      (((algorithm γ).truncateWith 0 q).output (oracle ω)))
    q hq β hβ hgood
  · intro γ
    exact hbounded _ (fun o => (algorithm γ).truncateWith_queries 0 o q)
  · intro γ ω hγω hqueries
    simpa only [(algorithm γ).truncateWith_output 0 (oracle ω) q hqueries] using hγω

end Testing

end SteinerLowerBound

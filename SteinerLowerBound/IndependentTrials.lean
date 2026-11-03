module

public import SteinerLowerBound.ProductProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω U : Type*} [Fintype Ω] [Fintype U]

theorem finite_union_bound (μ : Law Ω) (P : U → Ω → Prop) :
    μ.prob {ω | ∃ u, P u ω} ≤ ∑ u, μ.prob {ω | P u ω} := by
  classical
  simp only [prob]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ u, P u ω
  · obtain ⟨u, hu⟩ := h
    simp only [Set.mem_ofPred_eq, show ∃ u, P u ω from ⟨u, hu⟩, ↓reduceIte]
    have hb := Finset.single_le_sum
      (f := fun v => if P v ω then μ.mass ω else 0)
      (fun v _ => by split_ifs <;> simp_all [μ.nonneg ω]) (Finset.mem_univ u)
    simpa only [hu, ↓reduceIte] using hb
  · simp only [Set.mem_ofPred_eq, h, ↓reduceIte]
    exact Finset.sum_nonneg fun u _ => by split_ifs <;> simp_all

theorem expect_exp_indicator (μ : Law Ω) (P : Ω → Prop) :
    μ.expect (fun ω => Real.exp (if P ω then 1 else 0)) =
      1 + (Real.exp 1 - 1) * μ.prob {ω | P ω} := by
  classical
  have h (ω : Ω) :
      Real.exp (if P ω then 1 else 0) = 1 + (Real.exp 1 - 1) * (if P ω then 1 else 0) := by
    by_cases hP : P ω <;> simp [hP]
  simp_rw [h, expect_add, expect_const, expect_const_mul]
  congr 1
  congr 1
  symm
  exact prob_eq_expect μ {ω | P ω}

end Law

namespace IndependentTrials

variable {Ω U : Type*} [Fintype Ω] [Fintype U]

noncomputable def count (P : U → Ω → Prop) (w : U → Ω) : ℕ :=
  (Finset.univ.filter fun u => P u (w u)).card

noncomputable def mean (μ : U → Law Ω) (P : U → Ω → Prop) : ℝ :=
  ∑ u, (μ u).prob {ω | P u ω}

theorem mean_nonneg (μ : U → Law Ω) (P : U → Ω → Prop) : 0 ≤ mean μ P :=
  Finset.sum_nonneg fun u _ => (μ u).prob_nonneg _

theorem exp_count (μ : U → Law Ω) (P : U → Ω → Prop) :
    (Law.pi μ).expect (fun w => Real.exp (count P w)) =
      ∏ u, (1 + (Real.exp 1 - 1) * (μ u).prob {ω | P u ω}) := by
  classical
  have hc (w : U → Ω) :
      (count P w : ℝ) = ∑ u, if P u (w u) then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [count]
  have h (w : U → Ω) :
      Real.exp (count P w) = ∏ u, Real.exp (if P u (w u) then 1 else 0) := by
    rw [hc, Real.exp_sum]
  simp_rw [h]
  rw [Law.expect_pi_product μ (fun u ω => Real.exp (if P u ω then 1 else 0))]
  exact Finset.prod_congr rfl fun u _ => Law.expect_exp_indicator (μ u) (P u)

theorem exp_count_le (μ : U → Law Ω) (P : U → Ω → Prop) :
    (Law.pi μ).expect (fun w => Real.exp (count P w)) ≤
      Real.exp ((Real.exp 1 - 1) * mean μ P) := by
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [exp_count]
  calc
    _ ≤ ∏ u, Real.exp ((Real.exp 1 - 1) * (μ u).prob {ω | P u ω}) := by
      apply Finset.prod_le_prod₀
      · intro u _
        exact add_nonneg zero_le_one (mul_nonneg he ((μ u).prob_nonneg _))
      · intro u _
        simpa [add_comm] using Real.add_one_le_exp ((Real.exp 1 - 1) * (μ u).prob {ω | P u ω})
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]; rfl

theorem tail (μ : U → Law Ω) (P : U → Ω → Prop) (B : ℝ) :
    (Law.pi μ).prob {w | B ≤ (count P w : ℝ)} ≤
      Real.exp ((Real.exp 1 - 1) * mean μ P - B) := by
  have hs : {w : U → Ω | B ≤ (count P w : ℝ)} ⊆
      {w | Real.exp B ≤ Real.exp (count P w)} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    exact Real.exp_le_exp.mpr hw
  calc
    _ ≤ (Law.pi μ).prob {w | Real.exp B ≤ Real.exp (count P w)} := Law.prob_mono _ hs
    _ ≤ (Law.pi μ).expect (fun w => Real.exp (count P w)) / Real.exp B :=
      Law.markov _ (fun w => (Real.exp_pos _).le) (Real.exp_pos B)
    _ ≤ Real.exp ((Real.exp 1 - 1) * mean μ P) / Real.exp B :=
      div_le_div_of_nonneg_right (exp_count_le μ P) (Real.exp_pos B).le
    _ = _ := (Real.exp_sub _ _).symm

theorem tail_mean_bound (μ : U → Law Ω) (P : U → Ω → Prop) (M v : ℝ)
    (hM : mean μ P ≤ M) :
    (Law.pi μ).prob {w | Real.exp 1 * M + v ≤ (count P w : ℝ)} ≤ Real.exp (-v) := by
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hM₀ : 0 ≤ M := (mean_nonneg μ P).trans hM
  have hb := mul_le_mul_of_nonneg_left hM he
  exact (tail μ P _).trans (Real.exp_le_exp.mpr (by nlinarith))

end IndependentTrials

end SteinerLowerBound

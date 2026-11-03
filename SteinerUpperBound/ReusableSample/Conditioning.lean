module

public import SteinerUpperBound.ReusableSample.Margins

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

namespace Probability

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]

noncomputable def experiment (μ : Law A) (K : A → Law B) : Law (A × B) :=
  μ.bind fun x => (K x).map fun τ => (x, τ)

theorem experiment_mass (μ : Law A) (K : A → Law B) (x : A) (τ : B) :
    (experiment μ K).mass (x, τ) = μ.mass x * (K x).mass τ := by
  simp only [experiment, Law.bind, Law.expect, Law.map, Prod.mk.injEq, ite_and]
  simp

theorem experiment_marginal (μ : Law A) (K : A → Law B) :
    (experiment μ K).map Prod.snd = μ.bind K := by
  rw [experiment, LawOperations.map_bind]
  congr 1
  funext x
  rw [LawOperations.map_comp]
  exact LawOperations.map_id (K x)

theorem slice_total (J : Law (A × B)) (π : Law B)
    (hm : J.map Prod.snd = π) (τ : B) :
    (∑ x, J.mass (x, τ)) = π.mass τ := by
  have h := congrArg (fun μ : Law B => μ.mass τ) hm
  simpa only [Law.map, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] using h

noncomputable def posterior (J : Law (A × B)) (π : Law B)
    (hm : J.map Prod.snd = π) (τ : B) (hτ : 0 < π.mass τ) : Law A where
  mass x := J.mass (x, τ) / π.mass τ
  nonneg x := div_nonneg (J.nonneg _) hτ.le
  total := by
    rw [← Finset.sum_div, slice_total J π hm τ, div_self hτ.ne']

theorem posterior_expect (J : Law (A × B)) (π : Law B)
    (hm : J.map Prod.snd = π) (τ : B) (hτ : 0 < π.mass τ) (f : A → ℝ) :
    (posterior J π hm τ hτ).expect f = posteriorMean J π τ f := by
  simp only [Law.expect, posterior, posteriorMean, div_mul_eq_mul_div, Finset.sum_div]

noncomputable def conditionalBad (J : Law (A × B)) (π : Law B)
    (G : A → B → Prop) (τ : B) : ℝ :=
  (∑ x, if G x τ then J.mass (x, τ) else 0) / π.mass τ

theorem conditionalBad_nonneg (J : Law (A × B)) (π : Law B)
    (G : A → B → Prop) (τ : B) : 0 ≤ conditionalBad J π G τ := by
  apply div_nonneg _ (π.nonneg τ)
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [J.nonneg]

theorem conditionalBad_eq (J : Law (A × B)) (π : Law B)
    (hm : J.map Prod.snd = π) (τ : B) (hτ : 0 < π.mass τ) (G : A → B → Prop) :
    conditionalBad J π G τ = (posterior J π hm τ hτ).prob {x | G x τ} := by
  simp only [conditionalBad, Law.prob, posterior, Set.mem_ofPred_eq, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem expect_conditionalBad_le (J : Law (A × B)) (π : Law B) (G : A → B → Prop) :
    π.expect (conditionalBad J π G) ≤ J.prob {z | G z.1 z.2} := by
  calc
    _ ≤ ∑ τ, ∑ x, if G x τ then J.mass (x, τ) else 0 := by
      apply Finset.sum_le_sum
      intro τ _
      by_cases hz : π.mass τ = 0
      · simp only [hz, zero_mul]
        exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp [J.nonneg]
      · dsimp [conditionalBad]
        rw [mul_div_cancel₀ _ hz]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Law.prob, Fintype.sum_prod_type, Set.mem_ofPred_eq]

theorem conditionalBad_markov (J : Law (A × B)) (π : Law B)
    (G : A → B → Prop) (d ζ : ℝ) (hζ : 0 < ζ)
    (hd : J.prob {z | G z.1 z.2} ≤ d) :
    π.prob {τ | ζ < conditionalBad J π G τ} ≤ d / ζ := by
  exact (π.markov_gt (conditionalBad_nonneg J π G) hζ).trans
    (div_le_div_of_nonneg_right ((expect_conditionalBad_le J π G).trans hd) hζ.le)

theorem expect_lower_good (μ : Law A) (f : A → ℝ) (G : A → Prop) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, G x → a ≤ f x) :
    a * (1 - μ.prob {x | ¬ G x}) ≤ μ.expect f := by
  have hc : μ.prob {x | G x} = 1 - μ.prob {x | ¬ G x} := by
    have h := μ.prob_compl {x | G x}
    change μ.prob {x | ¬ G x} = 1 - μ.prob {x | G x} at h
    linarith
  rw [← hc]
  simp only [Law.prob, Law.expect, Finset.mul_sum, Set.mem_ofPred_eq]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : G x
  · simp only [hx, ↓reduceIte]
    nlinarith [μ.nonneg x, hg x hx]
  · simp only [hx, ↓reduceIte, mul_zero]
    exact mul_nonneg (μ.nonneg x) (hf x)

theorem expect_upper_good (μ : Law A) (f : A → ℝ) (G : A → Prop) (a : ℝ)
    (ha : 0 ≤ a) (hf : ∀ x, f x ≤ 1) (hg : ∀ x, G x → f x ≤ a) :
    μ.expect f ≤ a + μ.prob {x | ¬ G x} := by
  have hh : μ.expect f ≤ μ.expect (fun x => a + if G x then 0 else 1) := by
    apply μ.expect_mono
    intro x
    by_cases hx : G x
    · simpa only [hx, ↓reduceIte, add_zero] using hg x hx
    · simp only [hx, ↓reduceIte]
      linarith [hf x]
  rw [Law.expect_add, Law.expect_const] at hh
  have he : μ.expect (fun x => if G x then 0 else 1) = μ.prob {x | ¬ G x} := by
    rw [Law.prob_eq_expect]
    apply congrArg μ.expect
    funext x
    by_cases hx : G x <;> simp [hx]
  rwa [he] at hh

noncomputable def sampleMean [Nonempty I] (X : I → A) (f : A → ℝ) : ℝ :=
  (Law.uniform I).expect fun i => f (X i)

omit [Fintype A] in
theorem sampleMean_nonneg [Nonempty I] (X : I → A) (f : A → ℝ) (hf : ∀ u, 0 ≤ f u) :
    0 ≤ sampleMean X f :=
  (Law.uniform I).expect_nonneg fun i => hf (X i)

omit [Fintype A] in
theorem sampleMean_le_one [Nonempty I] (X : I → A) (f : A → ℝ) (hf : ∀ u, f u ≤ 1) :
    sampleMean X f ≤ 1 := by
  exact ((Law.uniform I).expect_mono fun i => hf (X i)).trans_eq
    ((Law.uniform I).expect_const 1)

theorem slice_expect (J : Law (A × B)) (τ : B) (f : A → ℝ) :
    (∑ u, J.mass (u, τ) * f u) = J.expect (fun z => if z.2 = τ then f z.1 else 0) := by
  simp only [Law.expect, Fintype.sum_prod_type, mul_ite, mul_zero]
  simp

theorem averageJoint_slice [Nonempty I] (ν : Law A) (K : (I → A) → Law B)
    (τ : B) (f : A → ℝ) :
    (∑ u, (averageJoint ν K).mass (u, τ) * f u) =
      ∑ x, (experiment (ν.iid I) K).mass (x, τ) * sampleMean x f := by
  rw [slice_expect, slice_expect]
  simp only [averageJoint, oldJoint, experiment, Law.expect_bind, Law.expect_map]
  rw [expect_comm (Law.uniform I) (ν.iid I)]
  apply congrArg (ν.iid I).expect
  funext x
  rw [expect_comm (Law.uniform I) (K x)]
  apply congrArg (K x).expect
  funext v
  by_cases hv : v = τ
  · simp only [hv, ↓reduceIte]
    rfl
  · simp only [hv, ↓reduceIte, Law.expect_const]

theorem posterior_sampleMean [Nonempty I] (ν : Law A) (K : (I → A) → Law B)
    (τ : B) (hτ : 0 < ((ν.iid I).bind K).mass τ) (f : A → ℝ) :
    (posterior (experiment (ν.iid I) K) ((ν.iid I).bind K)
      (experiment_marginal _ _) τ hτ).expect (fun x => sampleMean x f) =
      posteriorMean (averageJoint ν K) ((ν.iid I).bind K) τ f := by
  rw [posterior_expect, posteriorMean, posteriorMean, averageJoint_slice]

end Probability

noncomputable def indicator {U : Type*} (A : Finset U) (u : U) : ℝ :=
  if u ∈ A then 1 else 0

theorem indicator_nonneg {U : Type*} (A : Finset U) (u : U) : 0 ≤ indicator A u := by
  unfold indicator
  split_ifs <;> norm_num

theorem indicator_le_one {U : Type*} (A : Finset U) (u : U) : indicator A u ≤ 1 := by
  unfold indicator
  split_ifs <;> norm_num

theorem sampleMean_indicator {U : Type*} {Ns : ℕ} [Nonempty (Fin Ns)]
    (X : Fin Ns → U) (A : Finset U) :
    Probability.sampleMean X (indicator A) = liveCount (fun i => some (X i)) A / Ns := by
  simp only [Probability.sampleMean, Law.expect, Law.uniform, Fintype.card_fin,
    liveCount, contains_some, indicator, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem uniform_indicator {U : Type*} [Fintype U] [Nonempty U] (A : Finset U) :
    (Law.uniform U).expect (indicator A) = (A.card : ℝ) / Fintype.card U := by
  simp only [Law.expect, Law.uniform, indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun u => u ∈ A) = A := by ext u; simp
  rw [he]
  simp [div_eq_mul_inv]

end SteinerUpperBound.ReusableSample

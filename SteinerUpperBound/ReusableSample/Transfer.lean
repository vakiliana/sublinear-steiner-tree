module

public import SteinerUpperBound.ReusableSample.Tree
public import SteinerLowerBound.DeferredSampling

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

namespace Probability

variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I]

def Dominated (μ ν : Law A) (a d : ℝ) : Prop :=
  ∀ E, μ.prob E ≤ a * ν.prob E + d

noncomputable def hockey (μ ν : Law A) (a : ℝ) : ℝ :=
  ∑ x, max (μ.mass x - a * ν.mass x) 0

theorem hockey_nonneg (μ ν : Law A) (a : ℝ) : 0 ≤ hockey μ ν a :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem hockey_eq (μ ν : Law A) (a : ℝ) :
    hockey μ ν a = μ.prob {x | a * ν.mass x ≤ μ.mass x} -
      a * ν.prob {x | a * ν.mass x ≤ μ.mass x} := by
  simp only [hockey, Law.prob, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : a * ν.mass x ≤ μ.mass x
  · simp [h]
  · simp [h, max_eq_right (by linarith : μ.mass x - a * ν.mass x ≤ 0)]

theorem Dominated.hockey_le {μ ν : Law A} {a d : ℝ}
    (h : Dominated μ ν a d) : hockey μ ν a ≤ d := by
  rw [hockey_eq]
  linarith [h {x | a * ν.mass x ≤ μ.mass x}]

theorem weighted_difference_le (x y : A → ℝ) (f : A → ℝ)
    (hf₀ : ∀ u, 0 ≤ f u) (hf₁ : ∀ u, f u ≤ 1) :
    (∑ u, (x u - y u) * f u) ≤ ∑ u, max (x u - y u) 0 := by
  apply Finset.sum_le_sum
  intro u _
  by_cases h : y u ≤ x u
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith [hf₁ u]
  · rw [max_eq_right (by linarith : x u - y u ≤ 0)]
    nlinarith [hf₀ u]

theorem Dominated.expect {μ ν : Law A} {a d : ℝ} (h : Dominated μ ν a d)
    (f : A → ℝ) (hf₀ : ∀ u, 0 ≤ f u) (hf₁ : ∀ u, f u ≤ 1) :
    μ.expect f ≤ a * ν.expect f + d := by
  have hh := (weighted_difference_le μ.mass (fun u => a * ν.mass u) f hf₀ hf₁).trans
    h.hockey_le
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at hh
  unfold Law.expect
  linarith

theorem Dominated.map {μ ν : Law A} {a d : ℝ} (h : Dominated μ ν a d)
    (f : A → B) : Dominated (μ.map f) (ν.map f) a d := by
  intro E
  simpa only [Law.prob_map] using h (f ⁻¹' E)

theorem Dominated.bind_same (μ : Law A) (k l : A → Law B) (a d : ℝ)
    (h : ∀ x, Dominated (k x) (l x) a d) :
    Dominated (μ.bind k) (μ.bind l) a d := by
  intro E
  simp only [Law.prob_bind]
  calc
    _ ≤ μ.expect (fun x => a * (l x).prob E + d) := μ.expect_mono fun x => h x E
    _ = _ := by rw [Law.expect_add, Law.expect_const_mul, Law.expect_const]

theorem bind_const (μ : Law A) (ν : Law B) : μ.bind (fun _ => ν) = ν := by
  apply LawOperations.ext_mass
  intro b
  exact μ.expect_const _

theorem expect_comm (μ : Law A) (ν : Law B) (f : A → B → ℝ) :
    μ.expect (fun x => ν.expect (f x)) = ν.expect (fun y => μ.expect (fun x => f x y)) := by
  simp only [Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem iid_resample (ν : Law A) (i : I) (f : (I → A) → ℝ) :
    (ν.iid I).expect (fun x => ν.expect (fun y => f (Function.update x i y))) =
      (ν.iid I).expect f := by
  have h := Law.expect_adaptive_coordinate (fun _ : I => ν) i
    (fun y x => f (Function.update x i y)) (by intro a x b; simp)
  have hs : (fun x : I → A => f (Function.update x i (x i))) = f := by
    funext x
    rw [Function.update_eq_self]
  rw [hs] at h
  rw [expect_comm]
  exact h.symm

noncomputable def product (ν : Law A) (π : Law B) : Law (A × B) :=
  ν.bind fun u => π.map fun τ => (u, τ)

theorem product_mass (ν : Law A) (π : Law B) (u : A) (τ : B) :
    (product ν π).mass (u, τ) = ν.mass u * π.mass τ := by
  simp only [product, Law.bind, Law.expect, Law.map, Prod.mk.injEq, ite_and]
  simp

noncomputable def oldJoint (ν : Law A) (K : (I → A) → Law B) (i : I) : Law (A × B) :=
  (ν.iid I).bind fun x => (K x).map fun τ => (x i, τ)

noncomputable def replacedJoint (ν : Law A) (K : (I → A) → Law B) (i : I) :
    Law (A × B) :=
  (ν.iid I).bind fun x => ν.bind fun y =>
    (K (Function.update x i y)).map fun τ => (x i, τ)

theorem replacedJoint_eq_product (ν : Law A) (K : (I → A) → Law B) (i : I) :
    replacedJoint ν K i = product ν ((ν.iid I).bind K) := by
  apply LawOperations.ext_prob
  intro E
  simp only [replacedJoint, product, Law.prob_bind, Law.prob_map]
  have h := Law.expect_adaptive_coordinate (fun _ : I => ν) i
    (fun u x => ν.expect fun y =>
      (K (Function.update x i y)).prob {τ | (u, τ) ∈ E})
    (by intro u x z; simp)
  change (ν.iid I).expect (fun x => ν.expect fun y =>
      (K (Function.update x i y)).prob {τ | (x i, τ) ∈ E}) = _
  change (ν.iid I).expect (fun x => ν.expect fun y =>
      (K (Function.update x i y)).prob {τ | (x i, τ) ∈ E}) =
    ν.expect (fun u => (ν.iid I).expect fun x => (K x).prob {τ | (u, τ) ∈ E})
  change (ν.iid I).expect (fun x => ν.expect fun y =>
      (K (Function.update x i y)).prob {τ | (x i, τ) ∈ E}) =
    ν.expect (fun u => (ν.iid I).expect fun x => ν.expect fun y =>
      (K (Function.update x i y)).prob {τ | (u, τ) ∈ E}) at h
  rw [h]
  apply congrArg ν.expect
  funext u
  exact iid_resample ν i (fun x => (K x).prob {τ | (u, τ) ∈ E})

/-- The old coordinate and the new transcript are independent. Stability is
integrated before conditioning, so its additive error is not multiplied by
the number of records or by the size of the universe. -/
theorem oldJoint_stable (ν : Law A) (K : (I → A) → Law B) (a d : ℝ)
    (h : ∀ x i y, Dominated (K x) (K (Function.update x i y)) a d)
    (i : I) :
    Dominated (oldJoint ν K i) (product ν ((ν.iid I).bind K)) a d ∧
      Dominated (product ν ((ν.iid I).bind K)) (oldJoint ν K i) a d := by
  have hb x y : Dominated
      ((K x).map fun τ => (x i, τ))
      ((K (Function.update x i y)).map fun τ => (x i, τ)) a d :=
    (h x i y).map _
  have hr x y : Dominated
      ((K (Function.update x i y)).map fun τ => (x i, τ))
      ((K x).map fun τ => (x i, τ)) a d := by
    have hh := h (Function.update x i y) i (x i)
    simpa only [Function.update_idem, Function.update_eq_self] using hh.map
      (fun τ => (x i, τ))
  have hforward := Dominated.bind_same (ν.iid I)
    (fun x => (K x).map fun τ => (x i, τ))
    (fun x => ν.bind fun y => (K (Function.update x i y)).map fun τ => (x i, τ))
    a d (fun x => by
      simpa only [bind_const] using Dominated.bind_same ν
        (fun _ => (K x).map fun τ => (x i, τ))
        (fun y => (K (Function.update x i y)).map fun τ => (x i, τ)) a d (hb x))
  have hreverse := Dominated.bind_same (ν.iid I)
    (fun x => ν.bind fun y => (K (Function.update x i y)).map fun τ => (x i, τ))
    (fun x => (K x).map fun τ => (x i, τ))
    a d (fun x => by
      simpa only [bind_const] using Dominated.bind_same ν
        (fun y => (K (Function.update x i y)).map fun τ => (x i, τ))
        (fun _ => (K x).map fun τ => (x i, τ)) a d (hr x))
  change Dominated (oldJoint ν K i) (replacedJoint ν K i) a d at hforward
  change Dominated (replacedJoint ν K i) (oldJoint ν K i) a d at hreverse
  rw [replacedJoint_eq_product] at hforward hreverse
  exact ⟨hforward, hreverse⟩

noncomputable def averageJoint [Nonempty I] (ν : Law A) (K : (I → A) → Law B) :
    Law (A × B) :=
  (Law.uniform I).bind (oldJoint ν K)

theorem averageJoint_marginal [Nonempty I] (ν : Law A) (K : (I → A) → Law B) :
    (averageJoint ν K).map Prod.snd = (ν.iid I).bind K := by
  have hi (i : I) : (oldJoint ν K i).map Prod.snd = (ν.iid I).bind K := by
    rw [oldJoint, LawOperations.map_bind]
    congr 1
    funext x
    rw [LawOperations.map_comp]
    exact LawOperations.map_id (K x)
  rw [averageJoint, LawOperations.map_bind]
  simp_rw [hi]
  exact bind_const _ _

theorem averageJoint_stable [Nonempty I] (ν : Law A) (K : (I → A) → Law B) (a d : ℝ)
    (h : ∀ x i y, Dominated (K x) (K (Function.update x i y)) a d) :
    Dominated (averageJoint ν K) (product ν ((ν.iid I).bind K)) a d ∧
      Dominated (product ν ((ν.iid I).bind K)) (averageJoint ν K) a d := by
  constructor
  · simpa only [bind_const, averageJoint] using Dominated.bind_same (Law.uniform I)
      (oldJoint ν K) (fun _ => product ν ((ν.iid I).bind K)) a d
      (fun i => (oldJoint_stable ν K a d h i).1)
  · simpa only [bind_const, averageJoint] using Dominated.bind_same (Law.uniform I)
      (fun _ => product ν ((ν.iid I).bind K)) (oldJoint ν K) a d
      (fun i => (oldJoint_stable ν K a d h i).2)

noncomputable def posteriorMean (J : Law (A × B)) (π : Law B)
    (τ : B) (f : A → ℝ) : ℝ :=
  (∑ u, J.mass (u, τ) * f u) / π.mass τ

noncomputable def discrepancy (J P : Law (A × B)) (a : ℝ) (τ : B) : ℝ :=
  ∑ u, max (J.mass (u, τ) - a * P.mass (u, τ)) 0

noncomputable def badness (J P : Law (A × B)) (π : Law B) (a : ℝ) (τ : B) : ℝ :=
  (discrepancy J P a τ + discrepancy P J a τ) / π.mass τ

theorem discrepancy_nonneg (J P : Law (A × B)) (a : ℝ) (τ : B) :
    0 ≤ discrepancy J P a τ :=
  Finset.sum_nonneg fun _ _ => le_max_right _ _

theorem badness_nonneg (J P : Law (A × B)) (π : Law B) (a : ℝ) (τ : B) :
    0 ≤ badness J P π a τ :=
  div_nonneg (add_nonneg (discrepancy_nonneg _ _ _ _) (discrepancy_nonneg _ _ _ _))
    (π.nonneg τ)

theorem expect_badness_le (J P : Law (A × B)) (π : Law B) (a d : ℝ)
    (h : Dominated J P a d) (h' : Dominated P J a d) :
    π.expect (badness J P π a) ≤ 2 * d := by
  have hs : π.expect (badness J P π a) ≤ hockey J P a + hockey P J a := by
    calc
      _ ≤ ∑ τ, (discrepancy J P a τ + discrepancy P J a τ) := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hz : π.mass τ = 0
        · simp only [hz, zero_mul]
          exact add_nonneg (discrepancy_nonneg _ _ _ _) (discrepancy_nonneg _ _ _ _)
        · dsimp [badness]
          rw [mul_div_cancel₀ _ hz]
      _ = _ := by
        simp only [discrepancy, hockey, Finset.sum_add_distrib, Fintype.sum_prod_type]
        congr 1 <;> rw [Finset.sum_comm]
  linarith [h.hockey_le, h'.hockey_le]

def Transferred (J : Law (A × B)) (π : Law B) (ν : Law A) (a ζ : ℝ) (τ : B) : Prop :=
  0 < π.mass τ → ∀ f : A → ℝ, (∀ u, 0 ≤ f u) → (∀ u, f u ≤ 1) →
    posteriorMean J π τ f ≤ a * ν.expect f + ζ ∧
      ν.expect f ≤ a * posteriorMean J π τ f + ζ

theorem transferred_of_badness (J : Law (A × B)) (π : Law B) (ν : Law A)
    (a ζ : ℝ) (τ : B) (h : badness J (product ν π) π a τ ≤ ζ) :
    Transferred J π ν a ζ τ := by
  intro hτ f hf₀ hf₁
  have hd := discrepancy_nonneg J (product ν π) a τ
  have hd' := discrepancy_nonneg (product ν π) J a τ
  have hh : discrepancy J (product ν π) a τ +
      discrepancy (product ν π) J a τ ≤ ζ * π.mass τ :=
    (div_le_iff₀ hτ).mp h
  have h₁ := weighted_difference_le (fun u => J.mass (u, τ))
    (fun u => a * (product ν π).mass (u, τ)) f hf₀ hf₁
  have h₂ := weighted_difference_le (fun u => (product ν π).mass (u, τ))
    (fun u => a * J.mass (u, τ)) f hf₀ hf₁
  simp only [product_mass, sub_mul, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum] at h₁ h₂
  have hprod : (∑ u, ν.mass u * (π.mass τ * f u)) = π.mass τ * ν.expect f := by
    simp only [Law.expect, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hprod] at h₁ h₂
  dsimp [discrepancy] at hh hd hd'
  simp only [product_mass] at hh hd hd'
  constructor
  · rw [posteriorMean, div_le_iff₀ hτ]
    nlinarith
  · have he : a * posteriorMean J π τ f =
        (a * ∑ u, J.mass (u, τ) * f u) / π.mass τ := by
      simp [posteriorMean, mul_div_assoc]
    rw [he]
    have hb : (ν.expect f - ζ) * π.mass τ ≤ a * ∑ u, J.mass (u, τ) * f u := by
      nlinarith
    have hb' := (le_div_iff₀ hτ).mpr hb
    linarith

/-- Simultaneous posterior transfer for every bounded test function. -/
theorem posterior_transfer (J : Law (A × B)) (π : Law B) (ν : Law A)
    (a d ζ : ℝ) (hζ : 0 < ζ)
    (h : Dominated J (product ν π) a d)
    (h' : Dominated (product ν π) J a d) :
    π.prob {τ | ¬ Transferred J π ν a ζ τ} ≤ 2 * d / ζ := by
  have hs : {τ | ¬ Transferred J π ν a ζ τ} ⊆
      {τ | ζ < badness J (product ν π) π a τ} := by
    intro τ hτ
    by_contra hb
    exact hτ (transferred_of_badness J π ν a ζ τ (le_of_not_gt hb))
  calc
    _ ≤ π.prob {τ | ζ < badness J (product ν π) π a τ} := π.prob_mono hs
    _ ≤ π.expect (badness J (product ν π) π a) / ζ :=
      π.markov_gt (badness_nonneg _ _ _ _) hζ
    _ ≤ 2 * d / ζ := div_le_div_of_nonneg_right (expect_badness_le J _ π a d h h') hζ.le

end Probability

end SteinerUpperBound.ReusableSample

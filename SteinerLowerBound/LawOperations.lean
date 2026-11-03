module

public import SteinerLowerBound.CategoricalCoupling

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace LawOperations

def withFintype {Ω : Type*} (i j : Fintype Ω) (μ : @Law Ω i) : @Law Ω j := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  exact μ

theorem prob_withFintype {Ω : Type*} (i j : Fintype Ω) (μ : @Law Ω i) (E : Set Ω) :
    @Law.prob Ω j (withFintype i j μ) E = @Law.prob Ω i μ E := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

theorem map_withFintype {Ω Γ : Type*} [Fintype Γ]
    (i j : Fintype Ω) (μ : @Law Ω i) (f : Ω → Γ) :
    @Law.map Ω Γ j _ (withFintype i j μ) f = @Law.map Ω Γ i _ μ f := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

variable {Ω Γ Δ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ]

theorem ext_mass (μ ν : Law Ω) (h : ∀ ω, μ.mass ω = ν.mass ω) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

theorem ext_prob (μ ν : Law Ω) (h : ∀ E, μ.prob E = ν.prob E) : μ = ν := by
  apply ext_mass
  intro ω
  simpa only [CategoricalCoupling.probability_atom] using h {ω}

theorem map_comp (μ : Law Ω) (f : Ω → Γ) (g : Γ → Δ) :
    (μ.map f).map g = μ.map (fun ω => g (f ω)) := by
  apply ext_prob
  intro E
  simp only [Law.prob_map, Set.preimage_preimage]

theorem map_id (μ : Law Ω) : μ.map id = μ := by
  apply ext_prob
  intro E
  simp [Law.prob_map]

theorem map_bind (μ : Law Ω) (k : Ω → Law Γ) (f : Γ → Δ) :
    (μ.bind k).map f = μ.bind (fun ω => (k ω).map f) := by
  apply ext_prob
  intro E
  simp only [Law.prob_map, Law.prob_bind]

theorem bind_assoc (μ : Law Ω) (k : Ω → Law Γ) (l : Γ → Law Δ) :
    (μ.bind k).bind l = μ.bind (fun ω => (k ω).bind l) := by
  apply ext_prob
  intro E
  simp only [Law.prob_bind, Law.expect_bind]

theorem bind_comm (μ : Law Ω) (ν : Law Γ) (k : Ω → Γ → Law Δ) :
    μ.bind (fun ω => ν.bind (k ω)) = ν.bind (fun γ => μ.bind (fun ω => k ω γ)) := by
  apply ext_mass
  intro δ
  simp only [Law.bind, Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem bind_good (μ : Law Ω) (k l : Ω → Law Γ) (G : Set Ω)
    (ε : ℝ) (hε : 0 ≤ ε) (h : ∀ ω ∈ G, Law.Close (k ω) (l ω) ε) :
    Law.Close (μ.bind k) (μ.bind l) (ε + μ.prob Gᶜ) := by
  classical
  have hall (ω : Ω) : Law.Close (k ω) (l ω) (ε + if ω ∈ G then 0 else 1) := by
    by_cases hω : ω ∈ G
    · simpa only [hω, ↓reduceIte, add_zero] using h ω hω
    · exact (Law.close_one _ _).mono (by simp only [hω, ↓reduceIte]; linarith)
  have hind :
      μ.expect (fun ω => if ω ∈ G then (0 : ℝ) else 1) = μ.prob Gᶜ := by
    rw [Law.prob_eq_expect]
    apply congrArg
    funext ω
    by_cases hω : ω ∈ G <;> simp [hω]
  simpa only [Law.expect_add, Law.expect_const, hind] using
    Law.Close.bind_same μ k l (fun ω => ε + if ω ∈ G then 0 else 1) hall

theorem map_equiv_mass (μ : Law Ω) (e : Ω ≃ Γ) (γ : Γ) :
    (μ.map e).mass γ = μ.mass (e.symm γ) := by
  classical
  simp [Law.map, ← e.eq_symm_apply]

end LawOperations

namespace LawOperations

variable {U A B C : Type*} [Fintype U] [Fintype A] [Fintype B] [Fintype C]

noncomputable local instance : DecidableEq (C × U) := Classical.decEq _

theorem pi_uncurry (μ : C → U → Law A) :
    (Law.pi (fun c => Law.pi (μ c))).map (Equiv.curry C U A).symm =
      Law.pi (fun cu : C × U => μ cu.1 cu.2) := by
  apply ext_mass
  intro o
  rw [map_equiv_mass]
  simp only [Law.pi]
  rw [Fintype.prod_prod_type]
  rfl

theorem pi_map (μ : C → Law A) (f : C → A → B) :
    (Law.pi μ).map (fun a c => f c (a c)) = Law.pi (fun c => (μ c).map (f c)) := by
  classical
  apply ext_mass
  intro b
  simp only [Law.map, Law.pi]
  rw [Fintype.prod_sum (fun c a => if f c a = b c then (μ c).mass a else 0)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (fun c => f c (a c)) = b
  · subst b
    simp
  · have hex : ∃ c, f c (a c) ≠ b c := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    obtain ⟨c, hc⟩ := hex
    have hp : (∏ c, if f c (a c) = b c then (μ c).mass (a c) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by simp [hc])
    simp [h, hp]

theorem pi_bind (μ : C → Law A) (k : C → A → Law B) :
    Law.pi (fun c => (μ c).bind (k c)) =
      (Law.pi μ).bind (fun a => Law.pi (fun c => k c (a c))) := by
  apply ext_mass
  intro b
  simp only [Law.pi, Law.bind, Law.expect]
  rw [Fintype.prod_sum (fun c a => (μ c).mass a * (k c a).mass (b c))]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.prod_mul_distrib

end LawOperations

namespace CategoricalCoupling

variable {U : Type*} [Fintype U]

noncomputable def characteristic (H : Finset U) : U → Bool := fun u => decide (u ∈ H)

theorem characteristic_selected (b : U → Bool) : characteristic (selected b) = b := by
  funext u
  cases hb : b u <;> simp [characteristic, selected, hb]

theorem independent_characteristic (p : U → Rate) :
    (independent p).map characteristic = Law.pi (fun u => bernoulli (p u)) := by
  rw [independent, LawOperations.map_comp]
  have h : (fun b : U → Bool => characteristic (selected b)) = id :=
    funext characteristic_selected
  rw [h, LawOperations.map_id]

theorem categorical_function_close (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1) :
    Law.Close ((categorical p hs).map characteristic) (Law.pi (fun u => bernoulli (p u)))
      ((∑ u, (p u : ℝ)) ^ 2) := by
  rw [← independent_characteristic]
  exact (categorical_independent_close p hs).map characteristic

end CategoricalCoupling

end SteinerLowerBound

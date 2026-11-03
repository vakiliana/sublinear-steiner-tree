module

public import SteinerLowerBound.AdaptiveProposals
public import SteinerLowerBound.FiniteVariation
public import SteinerLowerBound.ProductProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace CategoricalCoupling

variable {U : Type*} [Fintype U]

noncomputable def bernoulli (p : Rate) : Law Bool where
  mass b := if b then (p : ℝ) else 1 - (p : ℝ)
  nonneg b := by cases b <;> simp [p.property.1, sub_nonneg.mpr p.property.2]
  total := by simp

noncomputable def selected (b : U → Bool) : Finset U :=
  Finset.univ.filter (fun u => b u = true)

noncomputable def independent (p : U → Rate) : Law (Finset U) :=
  (Law.pi (fun u => bernoulli (p u))).map selected

noncomputable def categorical (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1) : Law (Finset U) :=
  (Law.withNone (fun u => (p u : ℝ)) (fun u => (p u).property.1) hs).map
    (fun x => x.elim ∅ (fun u => {u}))

theorem probability_atom {Ω : Type*} [Fintype Ω] (μ : Law Ω) (ω : Ω) :
    μ.prob {ω} = μ.mass ω := by simp [Law.prob]

theorem independent_mass (p : U → Rate) (H : Finset U) :
    (independent p).mass H = ∏ u, if u ∈ H then (p u : ℝ) else 1 - (p u : ℝ) := by
  classical
  rw [← probability_atom, independent, Law.prob_map]
  have he : selected ⁻¹' ({H} : Set (Finset U)) =
      {b : U → Bool | ∀ u, if u ∈ H then b u = true else b u = false} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq,
      selected, Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h u
      by_cases hu : u ∈ H
      · simpa only [hu, ↓reduceIte] using (h u).mpr hu
      · have hb : b u ≠ true := fun hb => hu ((h u).mp hb)
        simpa only [hu, ↓reduceIte] using Bool.eq_false_iff.mpr hb
    · intro h u
      by_cases hu : u ∈ H
      · have hb : b u = true := by simpa [hu] using h u
        simp [hu, hb]
      · have hb : b u = false := by simpa [hu] using h u
        simp [hu, hb]
  rw [he, Law.prob_pi_all (fun u => bernoulli (p u))
    (fun u b => if u ∈ H then b = true else b = false)]
  apply Finset.prod_congr rfl
  intro u _
  by_cases hu : u ∈ H <;> simp [hu, Law.prob, bernoulli]

theorem categorical_empty (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1) :
    (categorical p hs).mass ∅ = 1 - ∑ u, (p u : ℝ) := by
  simp [categorical, Law.map, Law.withNone, Fintype.sum_option]

theorem categorical_singleton (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1) (u : U) :
    (categorical p hs).mass {u} = (p u : ℝ) := by
  simp [categorical, Law.map, Law.withNone, Fintype.sum_option]

theorem categorical_other (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1)
    (H : Finset U) (hH₀ : H ≠ ∅) (hH₁ : ∀ u, {u} ≠ H) :
    (categorical p hs).mass H = 0 := by
  simp [categorical, Law.map, Law.withNone, Fintype.sum_option, hH₀.symm, hH₁]

omit [Fintype U] in
theorem prod_complements_lower (p : U → Rate) (s : Finset U) :
    1 - (∑ u ∈ s, (p u : ℝ)) ≤ ∏ u ∈ s, (1 - (p u : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert u s hu ih =>
      rw [Finset.sum_insert hu, Finset.prod_insert hu]
      have h := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (p u).property.2)
      have hs : 0 ≤ ∑ v ∈ s, (p v : ℝ) := Finset.sum_nonneg fun v _ => (p v).property.1
      nlinarith [mul_nonneg (p u).property.1 hs]

theorem independent_empty (p : U → Rate) :
    1 - ∑ u, (p u : ℝ) ≤ (independent p).mass ∅ := by
  rw [independent_mass]
  simpa using prod_complements_lower p Finset.univ

theorem independent_singleton (p : U → Rate) (u : U) :
    (independent p).mass {u} =
      (p u : ℝ) * ∏ v ∈ Finset.univ.erase u, (1 - (p v : ℝ)) := by
  classical
  rw [independent_mass, ← Finset.mul_prod_erase _ _ (Finset.mem_univ u)]
  simp only [Finset.mem_singleton, ↓reduceIte]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  simp [(Finset.mem_erase.mp hv).1]

theorem singleton_le (p : U → Rate) (u : U) :
    (independent p).mass {u} ≤ (p u : ℝ) := by
  rw [independent_singleton]
  have hprod : (∏ v ∈ Finset.univ.erase u, (1 - (p v : ℝ))) ≤ 1 :=
    Finset.prod_le_one₀ (fun v _ => sub_nonneg.mpr (p v).property.2)
      (fun v _ => by linarith [(p v).property.1])
  nlinarith [(p u).property.1]

theorem singleton_deficit (p : U → Rate) (u : U) :
    (p u : ℝ) - (independent p).mass {u} ≤
      (p u : ℝ) * ∑ v, (p v : ℝ) := by
  classical
  rw [independent_singleton]
  have hsum : (∑ v ∈ Finset.univ.erase u, (p v : ℝ)) ≤ ∑ v, (p v : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun v _ _ => (p v).property.1)
  have hp := prod_complements_lower p (Finset.univ.erase u)
  have hprod : 1 - (∑ v, (p v : ℝ)) ≤ ∏ v ∈ Finset.univ.erase u, (1 - (p v : ℝ)) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hprod (p u).property.1
  nlinarith

theorem categorical_independent_close (p : U → Rate) (hs : ∑ u, (p u : ℝ) ≤ 1) :
    Law.Close (categorical p hs) (independent p) ((∑ u, (p u : ℝ)) ^ 2) := by
  classical
  let K : Finset (Finset U) := Finset.univ.image (fun u => {u})
  have hin : ∀ H ∈ K, (independent p).mass H ≤ (categorical p hs).mass H := by
    intro H hH
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hH
    rw [categorical_singleton]
    exact singleton_le p u
  have hout : ∀ H ∉ K, (categorical p hs).mass H ≤ (independent p).mass H := by
    intro H hH
    by_cases hzero : H = ∅
    · subst H
      rw [categorical_empty]
      exact independent_empty p
    · have hnot (u : U) : {u} ≠ H := by
        intro hu
        exact hH (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, hu⟩)
      rw [categorical_other p hs H hzero hnot]
      exact (independent p).nonneg H
  have hb : (∑ H ∈ K, ((categorical p hs).mass H - (independent p).mass H)) ≤
      (∑ u, (p u : ℝ)) ^ 2 := by
    change (∑ H ∈ Finset.univ.image (fun u => {u}),
      ((categorical p hs).mass H - (independent p).mass H)) ≤ _
    rw [Finset.sum_image]
    · simp only [categorical_singleton]
      calc
        _ ≤ ∑ u, (p u : ℝ) * ∑ v, (p v : ℝ) :=
          Finset.sum_le_sum (fun u _ => singleton_deficit p u)
        _ = _ := by rw [← Finset.sum_mul]; ring
    · intro u _ v _ h
      exact Finset.singleton_inj.mp h
  exact (Law.close_of_dominated_except _ _ K hin hout).mono hb

end CategoricalCoupling

end SteinerLowerBound

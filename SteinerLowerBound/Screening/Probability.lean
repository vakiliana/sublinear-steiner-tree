module

public import SteinerLowerBound.Screening.Bookkeeping

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem sum_prob_fiber (μ : Law Ω) (f : Ω → Γ) (E : Set Ω) :
    (∑ γ, μ.prob {ω | f ω = γ ∧ ω ∈ E}) = μ.prob E := by
  classical
  simp only [prob, Set.mem_ofPred_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ E <;> simp [h]

theorem fiber_bound (μ : Law Ω) (f : Ω → Γ) (E : Set Ω) (F B : ℝ)
    (h : ∀ γ, F * μ.prob {ω | f ω = γ ∧ ω ∈ E} ≤
      B * μ.prob {ω | f ω = γ}) :
    F * μ.prob E ≤ B := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun γ _ => h γ)
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_prob_fiber] at hs
  have he : (∑ γ, μ.prob {ω | f ω = γ}) = 1 := by
    simpa using sum_prob_fiber μ f Set.univ
  simpa only [he, mul_one] using hs

theorem weighted_fiber_bound (μ : Law Ω) (f : Ω → Γ) (E : Set Ω)
    (w : Γ → ℝ) (F B : ℝ) (hw : ∀ γ, 0 ≤ w γ)
    (h : ∀ γ, F * μ.prob {ω | f ω = γ ∧ ω ∈ E} ≤
      B * w γ * μ.prob {ω | f ω = γ}) :
    F * μ.prob E ≤ B * μ.expect (fun ω => w (f ω)) := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun γ _ => h γ)
  rw [← Finset.mul_sum, sum_prob_fiber] at hs
  have he : (∑ γ, B * w γ * μ.prob {ω | f ω = γ}) =
      B * μ.expect (fun ω => w (f ω)) := by
    simp only [prob, expect, Set.mem_ofPred_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    simp [mul_comm, mul_left_comm, mul_assoc]
  rwa [he] at hs

variable {C A : Type*} [Fintype C] [Fintype A]

noncomputable local instance (c : C) : DecidableEq {j : C // j ≠ c} := Classical.decEq _

noncomputable def splice (c : C) (a : A) (r : {j : C // j ≠ c} → A) : C → A :=
  (Equiv.funSplitAt c A).symm (a, r)

@[simp]
theorem splice_self (c : C) (a : A) (r : {j : C // j ≠ c} → A) :
    splice c a r c = a := by simp [splice, Equiv.funSplitAt, Equiv.piSplitAt]

@[simp]
theorem splice_other (c : C) (a : A) (r : {j : C // j ≠ c} → A)
    (j : {j : C // j ≠ c}) : splice c a r j = r j := by
  simp [splice, Equiv.funSplitAt, Equiv.piSplitAt, j.property]

theorem splice_update (c : C) (a b : A) (r : {j : C // j ≠ c} → A) :
    Function.update (splice c a r) c b = splice c b r := by
  classical
  funext j
  by_cases hj : j = c
  · subst j
    simp
  · simp [splice, Equiv.funSplitAt, Equiv.piSplitAt, hj]

theorem mass_pi_splice (k : C → Law A) (c : C) (a : A)
    (r : {j : C // j ≠ c} → A) :
    (pi k).mass (splice c a r) =
      (k c).mass a * (pi (fun j : {j : C // j ≠ c} => k j)).mass r := by
  classical
  change (∏ j, (k j).mass (splice c a r j)) = _
  rw [Fintype.prod_eq_mul_prod_compl c]
  rw [Finset.prod_subtype (p := fun j : C => j ≠ c)
    ({c}ᶜ : Finset C) (by intro j; simp)]
  simp only [splice_self, splice_other]
  rfl

theorem expect_pi_split_screening (k : C → Law A) (c : C) (f : (C → A) → ℝ) :
    (pi k).expect f =
      (pi (fun j : {j : C // j ≠ c} => k j)).expect
        (fun r => (k c).expect (fun a => f (splice c a r))) := by
  classical
  calc
    _ = ∑ ar : A × ({j : C // j ≠ c} → A),
        (pi k).mass (splice c ar.1 ar.2) * f (splice c ar.1 ar.2) :=
      Fintype.sum_equiv (Equiv.funSplitAt c A) _ _ (by
        intro h
        change (pi k).mass h * f h =
          (pi k).mass ((Equiv.funSplitAt c A).symm ((Equiv.funSplitAt c A) h)) *
            f ((Equiv.funSplitAt c A).symm ((Equiv.funSplitAt c A) h))
        simp only [Equiv.symm_apply_apply])
    _ = _ := by
      simp only [mass_pi_splice, Fintype.sum_prod_type, expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem prob_pi_split (k : C → Law A) (c : C) (E : Set (C → A)) :
    (pi k).prob E =
      (pi (fun j : {j : C // j ≠ c} => k j)).expect
        (fun r => (k c).prob {a | splice c a r ∈ E}) := by
  rw [prob_eq_expect, expect_pi_split_screening k c]
  simp only [prob_eq_expect, Set.mem_ofPred_eq]

theorem expect_pi_resample (k : C → Law A) (c : C) (f : (C → A) → ℝ) :
    (pi k).expect f =
      (pi k).expect (fun h => (k c).expect (fun a => f (Function.update h c a))) := by
  rw [expect_pi_split_screening k c f, expect_pi_split_screening k c]
  simp only [splice_update, expect_const]

theorem prob_pi_erasure_posterior (k : C → Law (Option A)) (c : C)
    (p : ℝ) (hp : 0 ≤ p) (habs : 1 / 2 ≤ (k c).mass none)
    (hmark : (k c).prob {a | a ≠ none} ≤ p)
    (E : Set (C → Option A))
    (herase : ∀ h ∈ E, Function.update h c none ∈ E) :
    (pi k).prob (E ∩ {h | h c ≠ none}) ≤ 2 * p * (pi k).prob E := by
  classical
  rw [prob_pi_split k c, prob_pi_split k c]
  rw [← expect_const_mul]
  apply expect_mono
  intro r
  have hh := TwoAnchor.erasure_posterior (k c) p hp habs hmark
    {a | splice c a r ∈ E} (by
      intro a ha
      simpa only [Set.mem_ofPred_eq, splice_update] using herase _ ha)
  have he : {a | splice c a r ∈ E ∧ a ≠ none} =
      {a | splice c a r ∈ E} ∩ {a | a ≠ none} := by ext a; rfl
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, splice_self]
  rw [he]
  exact hh

theorem prob_pi_erasure_mark (k : C → Law A) (c : C) (a₀ : A)
    (M : Set A) (p : ℝ) (hp : 0 ≤ p) (hmark : (k c).prob M ≤ p)
    (E E₀ : Set (C → A))
    (herase : ∀ h ∈ E, h c ∈ M ∧ Function.update h c a₀ ∈ E₀) :
    (pi k).prob E ≤ p * (pi k).prob {h | Function.update h c a₀ ∈ E₀} := by
  classical
  rw [prob_pi_split k c, prob_pi_split k c, ← expect_const_mul]
  apply expect_mono
  intro r
  by_cases h₀ : splice c a₀ r ∈ E₀
  · have hsub : {a | splice c a r ∈ E} ⊆ M := by
      intro a ha
      simpa only [splice_self] using (herase _ ha).1
    have hbound := ((k c).prob_mono hsub).trans hmark
    simpa [splice_update, h₀] using hbound
  · have he : {a | splice c a r ∈ E} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have hh := (herase _ ha).2
      exact h₀ (by simpa only [splice_update] using hh)
    simp only [he, prob_empty, Set.mem_ofPred_eq, splice_update, h₀,
      Set.setOf_false, prob_empty, mul_zero, le_refl]

theorem prob_pi_erasure_domination (k : C → Law A) (c : C) (a₀ : A)
    (r : ℝ) (hr : 0 ≤ r) (ha : r ≤ (k c).mass a₀) (E : Set (C → A)) :
    r * (pi k).prob {h | Function.update h c a₀ ∈ E} ≤ (pi k).prob E := by
  classical
  rw [prob_pi_split k c, prob_pi_split k c, ← expect_const_mul]
  apply expect_mono
  intro rest
  by_cases he : splice c a₀ rest ∈ E
  · have hs : {a₀} ⊆ {a | splice c a rest ∈ E} := by
      simpa using he
    have hm := (k c).prob_mono hs
    have hmass : (k c).prob {a₀} = (k c).mass a₀ := by simp [prob]
    rw [hmass] at hm
    simpa [splice_update, he] using ha.trans hm
  · simpa [splice_update, he] using (k c).prob_nonneg {a | splice c a rest ∈ E}

end Law

end SteinerLowerBound

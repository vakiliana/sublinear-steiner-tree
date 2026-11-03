module

public import SteinerLowerBound.ProductProbability
public import SteinerLowerBound.QueryModel

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω U : Type*} [Fintype Ω] [Fintype U]

noncomputable def splitAt (u : U) : (U → Ω) ≃ Ω × ({v // v ≠ u} → Ω) :=
  Equiv.funSplitAt u Ω

omit [Fintype Ω] [Fintype U] in
theorem splitAt_same (u : U) (a : Ω) (b : {v // v ≠ u} → Ω) :
    (splitAt u).symm (a, b) u = a := by
  simp [splitAt, Equiv.funSplitAt, Equiv.piSplitAt, Equiv.symm]

omit [Fintype Ω] [Fintype U] in
theorem splitAt_ne (u : U) (a : Ω) (b : {v // v ≠ u} → Ω) (v : {v // v ≠ u}) :
    (splitAt u).symm (a, b) v.val = b v := by
  simp [splitAt, Equiv.funSplitAt, Equiv.piSplitAt, Equiv.symm, v.property]

theorem expect_pi_split (μ : U → Law Ω) (u : U) (f : (U → Ω) → ℝ) :
    (pi μ).expect f = ∑ a, (μ u).mass a *
      ∑ b : {v // v ≠ u} → Ω,
        (∏ v : {v // v ≠ u}, (μ v.val).mass (b v)) *
          f ((splitAt u).symm (a, b)) := by
  let e := splitAt (Ω := Ω) u
  have hm (a : Ω) (b : {v // v ≠ u} → Ω) :
      (∏ v, (μ v).mass (e.symm (a, b) v)) =
        (μ u).mass a * ∏ v : {v // v ≠ u}, (μ v.val).mass (b v) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u)]
    rw [show e.symm (a, b) u = a from splitAt_same u a b]
    congr 1
    rw [Finset.prod_subtype (p := fun v : U => v ≠ u) (Finset.univ.erase u) (by intro v; simp)]
    apply Finset.prod_congr rfl
    intro v _
    exact congrArg (μ v.val).mass (splitAt_ne u a b v)
  simp only [expect, pi]
  calc
    _ = ∑ z : Ω × ({v // v ≠ u} → Ω),
        (∏ v, (μ v).mass (e.symm z v)) * f (e.symm z) :=
      Fintype.sum_equiv e _ _ (fun w => by simp)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [hm, Finset.mul_sum, mul_assoc]
      rfl

theorem expect_pi_irrelevant (μ : U → Law Ω) (u : U) (f : (U → Ω) → ℝ)
    (hf : ∀ w a, f (Function.update w u a) = f w) (a : Ω) :
    (pi μ).expect f =
      ∑ b : {v // v ≠ u} → Ω,
        (∏ v : {v // v ≠ u}, (μ v.val).mass (b v)) *
          f ((splitAt u).symm (a, b)) := by
  let e := splitAt (Ω := Ω) u
  have he (a' : Ω) (b : {v // v ≠ u} → Ω) :
      e.symm (a', b) = Function.update (e.symm (a, b)) u a' := by
    funext v
    by_cases hv : v = u
    · subst v
      simp [e, splitAt_same]
    · simpa only [e, Function.update_of_ne hv] using
        (splitAt_ne u a' b ⟨v, hv⟩).trans (splitAt_ne u a b ⟨v, hv⟩).symm
  rw [expect_pi_split μ u f]
  have hb (a' : Ω) (b : {v // v ≠ u} → Ω) :
      f ((splitAt u).symm (a', b)) = f ((splitAt u).symm (a, b)) := by
    change f (e.symm (a', b)) = f (e.symm (a, b))
    rw [he, hf]
  calc
    _ = ∑ a', (μ u).mass a' *
        ∑ b : {v // v ≠ u} → Ω,
          (∏ v : {v // v ≠ u}, (μ v.val).mass (b v)) * f ((splitAt u).symm (a, b)) := by
      apply Finset.sum_congr rfl
      intro a' _
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [hb]
    _ = _ := by rw [← Finset.sum_mul, (μ u).total, one_mul]

theorem expect_adaptive_coordinate (μ : U → Law Ω) (u : U)
    (f : Ω → (U → Ω) → ℝ)
    (hf : ∀ a w b, f a (Function.update w u b) = f a w) :
    (pi μ).expect (fun w => f (w u) w) =
      ∑ a, (μ u).mass a * (pi μ).expect (f a) := by
  rw [expect_pi_split μ u (fun w => f (w u) w)]
  apply Finset.sum_congr rfl
  intro a _
  rw [expect_pi_irrelevant μ u (f a) (hf a) a]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [splitAt_same]

end Law

namespace DecisionTree

variable {Q A R : Type*} [Fintype A]

noncomputable def used : DecisionTree Q A R → Finset Q
  | .leaf _ => ∅
  | .query q next => insert q (Finset.univ.biUnion fun a => (next a).used)

def NoRepeats : DecisionTree Q A R → Prop
  | .leaf _ => True
  | .query q next => (∀ a, (next a).NoRepeats) ∧ ∀ a, q ∉ (next a).used

theorem output_agree_used (t : DecisionTree Q A R) (o o' : Q → A)
    (h : ∀ q ∈ t.used, o q = o' q) : t.output o = t.output o' := by
  induction t with
  | leaf => rfl
  | query q next ih =>
      have hq : o q = o' q := h q (Finset.mem_insert_self _ _)
      simp only [output, hq]
      apply ih
      intro q' hq'
      exact h q' (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨o' q, Finset.mem_univ _, hq'⟩))

theorem output_update (t : DecisionTree Q A R) (o : Q → A) (q : Q) (a : A)
    (hq : q ∉ t.used) : t.output (Function.update o q a) = t.output o := by
  classical
  apply output_agree_used
  intro q' hq'
  have hne : q' ≠ q := by intro h; subst q'; exact hq hq'
  rw [Function.update_of_ne hne]

noncomputable def runLaw [Fintype R] (μ : Q → Law A) : DecisionTree Q A R → Law R
  | .leaf r => Law.pure r
  | .query q next => (μ q).bind (fun a => (next a).runLaw μ)

theorem deferred_sampling [Fintype Q] [Fintype R] (μ : Q → Law A)
    (t : DecisionTree Q A R) (ht : t.NoRepeats) (E : Set R) :
    (Law.pi μ).prob {o | t.output o ∈ E} = (t.runLaw μ).prob E := by
  classical
  induction t with
  | leaf r => by_cases hr : r ∈ E <;> simp [output, runLaw, Law.prob_pure, hr]
  | query q next ih =>
      change (Law.pi μ).prob {o | (next (o q)).output o ∈ E} = _
      have hprob :
          (Law.pi μ).prob {o | (next (o q)).output o ∈ E} =
            (Law.pi μ).expect (fun o => if (next (o q)).output o ∈ E then 1 else 0) := by
        simpa only [Set.mem_ofPred_eq] using
          Law.prob_eq_expect (Law.pi μ) {o | (next (o q)).output o ∈ E}
      rw [hprob]
      rw [Law.expect_adaptive_coordinate μ q (fun a o => if (next a).output o ∈ E then 1 else 0)
        (fun a o b => by rw [output_update _ _ _ _ (ht.2 a)])]
      have hbranch (a : A) :
          (Law.pi μ).expect (fun o => if (next a).output o ∈ E then 1 else 0) =
            ((next a).runLaw μ).prob E := by
        simpa only [Law.prob_eq_expect, Set.mem_ofPred_eq] using ih a (ht.1 a)
      simp_rw [hbranch]
      rw [runLaw, Law.prob_bind]
      rfl

end DecisionTree

end SteinerLowerBound

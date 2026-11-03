module

public import SteinerLowerBound.Screening.Erasure

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {B A C T : Type*} [Fintype B] [Fintype A] [Fintype C] [Fintype T]

noncomputable def starSupports (support : A → Finset T) (h : C → Option A) (c : C) :
    Finset T := (h c).elim ∅ support

noncomputable def eraseData (c : C) (x : B × (C → Option A)) : B × (C → Option A) :=
  (x.1, Function.update x.2 c none)

theorem starSupports_erase (support : A → Finset T) (h : C → Option A) (c : C) :
    starSupports support (Function.update h c none) =
      Function.update (starSupports support h) c ∅ := by
  classical
  funext c'
  by_cases hc : c' = c
  · subst c'
    simp [starSupports]
  · simp [starSupports, Function.update_of_ne hc]

theorem shuffled_erasure_mark (μ : Law B) (k : B → C → Law (Option A)) (c : C)
    (M : B → Equiv.Perm T → Set (Option A)) (p : ℝ) (hp : 0 ≤ p)
    (hmark : ∀ b π, (k b c).prob (M b π) ≤ p)
    (E E₀ : Set ((B × (C → Option A)) × Equiv.Perm T))
    (herase : ∀ ω ∈ E, ω.1.2 c ∈ M ω.1.1 ω.2 ∧
      (eraseData c ω.1, ω.2) ∈ E₀) :
    (shuffledLaw (T := T) (Law.conditionalProduct μ k)).prob E ≤
      p * (shuffledLaw (T := T)
        ((Law.conditionalProduct μ k).map (eraseData c))).prob E₀ := by
  rw [Law.prob_shuffled_map, Law.prob_shuffled_conditionalProduct,
    Law.prob_shuffled_conditionalProduct, ← Law.expect_const_mul]
  apply μ.expect_mono
  intro b
  rw [← Law.expect_const_mul]
  apply Law.expect_mono
  intro π
  exact Law.prob_pi_erasure_mark (k b) c none (M b π) p hp (hmark b π)
    {h | ((b, h), π) ∈ E} {h | ((b, h), π) ∈ E₀}
    (fun h hh => herase ((b, h), π) hh)

theorem shuffled_erasure_domination (μ : Law B) (k : B → C → Law (Option A))
    (c : C) (r : ℝ) (hr : 0 ≤ r) (ha : ∀ b, r ≤ (k b c).mass none)
    (E : Set ((B × (C → Option A)) × Equiv.Perm T)) :
    r * (shuffledLaw (T := T)
      ((Law.conditionalProduct μ k).map (eraseData c))).prob E ≤
        (shuffledLaw (T := T) (Law.conditionalProduct μ k)).prob E := by
  rw [Law.prob_shuffled_map, Law.prob_shuffled_conditionalProduct,
    Law.prob_shuffled_conditionalProduct, ← Law.expect_const_mul]
  apply μ.expect_mono
  intro b
  rw [← Law.expect_const_mul]
  apply Law.expect_mono
  intro π
  exact Law.prob_pi_erasure_domination (k b) c none r hr (ha b)
    {h | ((b, h), π) ∈ E}

theorem shuffled_erasure_posterior (μ : Law B) (k : B → C → Law (Option A))
    (c : C) (p : ℝ) (hp : 0 ≤ p)
    (ha : ∀ b, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b, (k b c).prob {a | a ≠ none} ≤ p)
    (E : Set ((B × (C → Option A)) × Equiv.Perm T))
    (herase : ∀ ω ∈ E, (eraseData c ω.1, ω.2) ∈ E) :
    (shuffledLaw (T := T) (Law.conditionalProduct μ k)).prob
        (E ∩ {ω | ω.1.2 c ≠ none}) ≤
      2 * p * (shuffledLaw (T := T) (Law.conditionalProduct μ k)).prob E := by
  rw [Law.prob_shuffled_conditionalProduct, Law.prob_shuffled_conditionalProduct,
    ← Law.expect_const_mul]
  apply μ.expect_mono
  intro b
  rw [← Law.expect_const_mul]
  apply Law.expect_mono
  intro π
  have hh := Law.prob_pi_erasure_posterior (k b) c p hp (ha b) (hmark b)
    {h | ((b, h), π) ∈ E} (fun h hh => herase ((b, h), π) hh)
  convert hh using 1
  apply congrArg (Law.prob (Law.pi (k b)))
  ext h
  rfl

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem unseen_center_prefix_bound (μ : Law B) (k : B → C → Law (Option A))
    (F : B → C → Finset (Terminal S G I)) (support : A → Finset (Terminal S G I))
    (c : C) (p : ℝ) (hp : 0 ≤ p)
    (ha : ∀ b, 1 / 2 ≤ (k b c).mass none)
    (hmark : ∀ b, (k b c).prob {a | a ≠ none} ≤ p)
    (r : Record (Query (Terminal S G I) C) Reply) :
    (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob
      {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
        (TwoAnchor.positives (relabel ω.2 (F ω.1.1))
          (relabel ω.2 (starSupports support ω.1.2)) (centerHistory (questions r)) c).card ≤ 2 ∧
            ω.1.2 c ≠ none} ≤
      2 * p * (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob
        {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} := by
  classical
  let E := {ω : (B × (C → Option A)) × Equiv.Perm (Terminal S G I) |
    Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
      (TwoAnchor.positives (relabel ω.2 (F ω.1.1))
        (relabel ω.2 (starSupports support ω.1.2)) (centerHistory (questions r)) c).card ≤ 2}
  have he := shuffled_erasure_posterior μ k c p hp ha hmark E (by
    intro ω hω
    change Compatible (queryAnswer ω.2 (F ω.1.1)
      (starSupports support (Function.update ω.1.2 c none))) r ∧ _
    rw [starSupports_erase]
    refine ⟨erase_compatible _ _ _ r c hω.2 hω.1, ?_⟩
    change (TwoAnchor.positives (relabel ω.2 (F ω.1.1))
      (relabel ω.2 (starSupports support (Function.update ω.1.2 c none)))
      (centerHistory (questions r)) c).card ≤ 2
    rw [starSupports_erase, relabel_update, TwoAnchor.positives_of_observations
      (relabel ω.2 (F ω.1.1)) _ (relabel ω.2 (starSupports support ω.1.2))
      (centerHistory (questions r))
      (TwoAnchor.erase_observations _ _ _ c hω.2)]
    exact hω.2)
  have hmono := (shuffledLaw (T := Terminal S G I) (Law.conditionalProduct μ k)).prob_mono
    (show E ⊆ {ω | Compatible
      (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r} from fun _ h => h.1)
  have heq : E ∩ {ω | ω.1.2 c ≠ none} =
      {ω | Compatible (queryAnswer ω.2 (F ω.1.1) (starSupports support ω.1.2)) r ∧
        (TwoAnchor.positives (relabel ω.2 (F ω.1.1))
          (relabel ω.2 (starSupports support ω.1.2)) (centerHistory (questions r)) c).card ≤ 2 ∧
            ω.1.2 c ≠ none} := by
    ext ω
    simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [heq] at he
  exact he.trans (mul_le_mul_of_nonneg_left hmono (by positivity))

end Screening

end SteinerLowerBound

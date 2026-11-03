module

public import SteinerLowerBound.Screening.ClusterProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {T C : Type*} [Fintype T]

theorem relabel_update (π : Equiv.Perm T) (H : C → Finset T) (c : C) :
    relabel π (Function.update H c ∅) = Function.update (relabel π H) c ∅ := by
  classical
  funext c'
  by_cases hc : c' = c
  · subst c'
    simp [relabel]
  · simp [relabel, Function.update_of_ne hc]

theorem centerHistory_append (h k : List (Query T C)) :
    centerHistory (h ++ k) = centerHistory h ++ centerHistory k := by
  simp [centerHistory, List.filterMap_append]

theorem erase_answer_split (F H : C → Finset T)
    (h k : List (C × T)) (c : C) (u : T)
    (hp : (TwoAnchor.positives F H (h ++ [(c, u)] ++ k) c).card ≤ 2) :
    TwoAnchor.answer F (Function.update H c ∅) h c u = TwoAnchor.answer F H h c u := by
  classical
  have hh := TwoAnchor.erase_answers F H (h ++ [(c, u)] ++ k) c hp
    ⟨h.length, by simp only [List.length_append, List.length_singleton]; omega⟩
  simpa [List.append_assoc, List.take_append_of_le_length (Nat.le_refl h.length),
    List.get_eq_getElem, List.getElem_append_right (Nat.le_refl h.length)] using hh

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem erase_public_observations (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C)) (c : C)
    (hp : (TwoAnchor.positives (relabel π F) (relabel π H) (centerHistory h) c).card ≤ 2) :
    observations π F (Function.update H c ∅) h = observations π F H h := by
  classical
  funext i
  have hsplit : h.take i.val ++ [h.get i] ++ h.drop (i.val + 1) = h := by
    rw [List.get_eq_getElem, ← List.concat_eq_append, List.take_concat_get i.isLt,
      List.take_append_drop]
  cases he : h.get i with
  | tt u v => simp only [observations, he, queryAnswer]
  | cc c c' => simp only [observations, he, queryAnswer]
  | ct c' u =>
      by_cases hc : c' = c
      · subst c'
        have hcanon : centerHistory h =
            centerHistory (h.take i.val) ++ [(c, u)] ++ centerHistory (h.drop (i.val + 1)) := by
          conv_lhs => rw [← hsplit]
          simp only [he, centerHistory, List.filterMap_append, List.filterMap_cons,
            List.filterMap_nil, List.singleton_append]
        have ha := erase_answer_split (relabel π F) (relabel π H)
          (centerHistory (h.take i.val)) (centerHistory (h.drop (i.val + 1))) c u
          (hcanon ▸ hp)
        simp only [observations, he, queryAnswer, relabel_update, ha]
      · have ha : TwoAnchor.answer (relabel π F) (relabel π (Function.update H c ∅))
            (centerHistory (h.take i.val)) c' u =
          TwoAnchor.answer (relabel π F) (relabel π H)
            (centerHistory (h.take i.val)) c' u := by
          unfold TwoAnchor.answer
          apply Bool.decide_congr
          simp only [relabel_update, Function.update_of_ne hc]
        simp only [observations, he, queryAnswer, ha]

theorem erase_compatible (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I))
    (r : Record (Query (Terminal S G I) C) Reply) (c : C)
    (hp : (TwoAnchor.positives (relabel π F) (relabel π H) (centerHistory (questions r)) c).card ≤ 2)
    (hr : Compatible (queryAnswer π F H) r) :
    Compatible (queryAnswer π F (Function.update H c ∅)) r := by
  rw [compatible_iff_observations] at hr ⊢
  rw [erase_public_observations π F H (questions r) c hp]
  exact hr

theorem counterLabels_mono (π : Equiv.Perm (Terminal S G I))
    (F F' : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (hF : ∀ c, F c ⊆ F' c) (u : Terminal S G I) :
    counterLabels π F h u ⊆ counterLabels π F' h u := by
  intro x hx
  obtain ⟨hxo, c, hc, hu⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxo, c, hc, hF c hu⟩

theorem erase_screenable (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) (L : ℝ) (c : C)
    (hu : Screenable π F H h u L) :
    Screenable π F (Function.update H c ∅) h u L := by
  classical
  have hsub : ∀ c', Function.update H c ∅ c' ⊆ H c' := by
    intro c'
    by_cases hc : c' = c
    · subst c'
      simp
    · simp [Function.update_of_ne hc]
  refine ⟨hu.1, ?_, ?_⟩
  · intro c' hc
    exact ⟨(hu.2.1 c' hc).1, fun hh => (hu.2.1 c' hc).2 (hsub c' hh)⟩
  · have hh := Finset.card_le_card (counterLabels_mono π _ H h hsub u)
    have hh' : ((counterLabels π (Function.update H c ∅) h u).card : ℝ) ≤
        (counterLabels π H h u).card := by exact_mod_cast hh
    linarith [hu.2.2]

theorem low_positive_before_lucky (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (hF : Supported F) (hH : Supported H)
    (hcard : ∀ c, (F c).card ≤ 2)
    (hFH : ∀ c, (H c).Nonempty → F c ⊆ H c)
    (h : List (Query (Terminal S G I) C))
    (hn : (analyze π F H D t R h).stop = none) (c : C) (u : Terminal S G I)
    (hu : u ∉ (analyze π F H D t R h).exposed) (huH : π u ∈ H c) :
    (TwoAnchor.positives (relabel π F) (relabel π H) (centerHistory h) c).card ≤ 2 := by
  by_contra hp
  have hfull := third_positive_star_exposed π F H h _
    (analyze_contacts π F H D t R hF hH h hn)
    (analyze_closed π F H D t R h) hcard hFH c (by omega)
  exact hu (hfull ((mem_relabel _ _ _ _).mpr huH))

end Screening

namespace Law

variable {B A C T : Type*} [Fintype B] [Fintype A] [Fintype C] [Fintype T]

noncomputable def conditionalProduct (μ : Law B) (k : B → C → Law A) : Law (B × (C → A)) where
  mass x := μ.mass x.1 * (pi (k x.1)).mass x.2
  nonneg x := mul_nonneg (μ.nonneg _) ((pi _).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, (pi _).total, mul_one]
    exact μ.total

theorem expect_shuffled (μ : Law B) (f : B × Equiv.Perm T → ℝ) :
    (Screening.shuffledLaw (T := T) μ).expect f =
      μ.expect (fun b => (uniform (Equiv.Perm T)).expect (fun π => f (b, π))) := by
  simp only [expect, Screening.shuffledLaw, uniform, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]

theorem prob_shuffled (μ : Law B) (E : Set (B × Equiv.Perm T)) :
    (Screening.shuffledLaw (T := T) μ).prob E =
      μ.expect (fun b => (uniform (Equiv.Perm T)).prob {π | (b, π) ∈ E}) := by
  rw [prob_eq_expect, expect_shuffled]
  simp only [prob_eq_expect, Set.mem_ofPred_eq]

theorem expect_conditionalProduct (μ : Law B) (k : B → C → Law A) (f : B × (C → A) → ℝ) :
    (conditionalProduct μ k).expect f =
      μ.expect (fun b => (pi (k b)).expect (fun h => f (b, h))) := by
  simp only [expect, conditionalProduct, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem prob_shuffled_conditionalProduct (μ : Law B) (k : B → C → Law A)
    (E : Set ((B × (C → A)) × Equiv.Perm T)) :
    (Screening.shuffledLaw (T := T) (conditionalProduct μ k)).prob E =
      μ.expect (fun b => (uniform (Equiv.Perm T)).expect (fun π =>
        (pi (k b)).prob {h | ((b, h), π) ∈ E})) := by
  classical
  rw [prob_shuffled, expect_conditionalProduct]
  apply congrArg (Law.expect μ)
  funext b
  simp only [expect, prob, Set.mem_ofPred_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro h _
  by_cases he : ((b, h), π) ∈ E <;> simp [he, mul_comm]

theorem prob_shuffled_map (μ : Law B) {D : Type*} [Fintype D]
    (f : B → D) (E : Set (D × Equiv.Perm T)) :
    (Screening.shuffledLaw (T := T) (μ.map f)).prob E =
      (Screening.shuffledLaw (T := T) μ).prob {ω | (f ω.1, ω.2) ∈ E} := by
  rw [prob_shuffled, expect_map, prob_shuffled]
  rfl

end Law

end SteinerLowerBound

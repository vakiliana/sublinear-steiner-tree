module

public import SteinerLowerBound.FiniteProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace TwoAnchor

variable {S C : Type*} [Fintype S]

noncomputable def queried (h : List (C × S)) (c : C) : Finset S :=
  Finset.univ.filter (fun u => (c, u) ∈ h)

def active (F : C → Finset S) (h : List (C × S)) (c : C) : Prop :=
  (F c).card = 2 ∧ F c ⊆ queried h c

noncomputable def blocked (F : C → Finset S) (h : List (C × S)) (c : C) : Finset S :=
  Finset.univ.filter (fun u => u ∉ F c ∧
    ∃ i : Fin h.length, h.get i = (c, u) ∧ ¬active F (h.take i.val) c)

noncomputable def answer (F H : C → Finset S) (h : List (C × S)) (c : C) (u : S) : Bool :=
  decide (u ∈ F c ∨
    (active F h c ∧ Disjoint (H c) (blocked F h c) ∧ u ∈ H c))

noncomputable def positives (F H : C → Finset S) (h : List (C × S)) (c : C) : Finset S :=
  (F c ∩ queried h c) ∪ Finset.univ.filter (fun u =>
    ∃ i : Fin h.length, h.get i = (c, u) ∧ answer F H (h.take i.val) c u = true)

theorem queried_take_subset (h : List (C × S)) (n : ℕ) (c : C) :
    queried (h.take n) c ⊆ queried h c := by
  intro u hu
  simp only [queried, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact List.mem_of_mem_take hu

theorem anchor_positive (F H : C → Finset S) (h : List (C × S)) (c : C) (u : S)
    (hu : u ∈ F c) : answer F H h c u = true := by
  simp [answer, hu]

theorem mem_positives_iff (F H : C → Finset S) (h : List (C × S)) (c : C) (u : S) :
    u ∈ positives F H h c ↔
      ∃ i : Fin h.length, h.get i = (c, u) ∧ answer F H (h.take i.val) c u = true := by
  classical
  constructor
  · intro hu
    rcases Finset.mem_union.mp hu with hu | hu
    · obtain ⟨hF, hq⟩ := Finset.mem_inter.mp hu
      have hmem : (c, u) ∈ h := (Finset.mem_filter.mp hq).2
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
      exact ⟨i, hi, anchor_positive F H _ c u hF⟩
    · exact (Finset.mem_filter.mp hu).2
  · intro hu
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)

theorem positive_is_anchor (F H : C → Finset S) (h : List (C × S)) (c : C)
    (hcount : (positives F H h c).card ≤ 2) (i : Fin h.length) (u : S)
    (hquery : h.get i = (c, u)) (hans : answer F H (h.take i.val) c u = true) :
    u ∈ F c := by
  classical
  by_contra hu
  have ha : active F (h.take i.val) c := by
    have h' : active F (h.take i.val) c ∧
        Disjoint (H c) (blocked F (h.take i.val) c) ∧ u ∈ H c := by
      simpa [answer, hu] using hans
    exact h'.1
  have hF : F c ⊆ positives F H h c := by
    intro v hv
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr
      ⟨hv, queried_take_subset h i.val c (ha.2 hv)⟩)
  have hup : u ∈ positives F H h c :=
    Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨i, hquery, hans⟩⟩)
  have hsub : insert u (F c) ⊆ positives F H h c :=
    Finset.insert_subset_iff.mpr ⟨hup, hF⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hu, ha.1] at hcard
  omega

theorem erase_answers (F H : C → Finset S) (h : List (C × S)) (c : C)
    (hcount : (positives F H h c).card ≤ 2) (i : Fin h.length) :
    answer F (Function.update H c ∅) (h.take i.val) (h.get i).1 (h.get i).2 =
      answer F H (h.take i.val) (h.get i).1 (h.get i).2 := by
  classical
  rcases hq : h.get i with ⟨c', u⟩
  by_cases hc : c' = c
  · subst c'
    by_cases hans : answer F H (h.take i.val) c u = true
    · have hu := positive_is_anchor F H h c hcount i u hq hans
      exact (anchor_positive F (Function.update H c ∅) _ c u hu).trans hans.symm
    · have hu : u ∉ F c := by
        intro hu
        exact hans (anchor_positive F H _ c u hu)
      have horig : answer F H (h.take i.val) c u = false := Bool.eq_false_iff.mpr hans
      rw [horig]
      simp [answer, hu]
  · simp only [answer, Function.update_of_ne hc]

noncomputable def observations (F H : C → Finset S) (h : List (C × S)) :
    Fin h.length → Bool :=
  fun i => answer F H (h.take i.val) (h.get i).1 (h.get i).2

theorem erase_observations (F H : C → Finset S) (h : List (C × S)) (c : C)
    (hcount : (positives F H h c).card ≤ 2) :
    observations F (Function.update H c ∅) h = observations F H h := by
  funext i
  exact erase_answers F H h c hcount i

theorem positives_of_observations (F H H' : C → Finset S) (h : List (C × S))
    (heq : observations F H h = observations F H' h) (c : C) :
    positives F H h c = positives F H' h c := by
  classical
  ext u
  rw [mem_positives_iff, mem_positives_iff]
  constructor
  · rintro ⟨i, hi, ha⟩
    refine ⟨i, hi, ?_⟩
    have he := congrFun heq i
    simp only [observations, hi] at he
    exact he ▸ ha
  · rintro ⟨i, hi, ha⟩
    refine ⟨i, hi, ?_⟩
    have he := congrFun heq i
    simp only [observations, hi] at he
    exact he.symm ▸ ha

theorem erasure_posterior {Ω : Type*} [Fintype Ω] (μ : Law (Option Ω))
    (p : ℝ) (hp : 0 ≤ p) (habsent : 1 / 2 ≤ μ.mass none)
    (hpresent : μ.prob {x | x ≠ none} ≤ p) (E : Set (Option Ω))
    (herase : ∀ x ∈ E, none ∈ E) :
    μ.prob (E ∩ {x | x ≠ none}) ≤ 2 * p * μ.prob E := by
  classical
  by_cases hn : none ∈ E
  · have hpoint : μ.prob {none} = μ.mass none := by simp [Law.prob]
    have hmono : μ.prob {none} ≤ μ.prob E :=
      μ.prob_mono (Set.singleton_subset_iff.mpr hn)
    have hupper : μ.prob (E ∩ {x | x ≠ none}) ≤ p :=
      (μ.prob_mono Set.inter_subset_right).trans hpresent
    nlinarith
  · have he : E = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hn (herase x hx)
    simp [he]

theorem unseen_star_posterior {Ω : Type*} [Fintype Ω] (μ : Law (Option Ω))
    (support : Ω → Finset S) (p : ℝ) (hp : 0 ≤ p)
    (habsent : 1 / 2 ≤ μ.mass none) (hpresent : μ.prob {x | x ≠ none} ≤ p)
    (F H target : C → Finset S) (h : List (C × S)) (c : C)
    (hcount : (positives F target h c).card ≤ 2) :
    let realization := fun x : Option Ω => Function.update H c
      (x.elim ∅ support)
    let E := {x | observations F (realization x) h = observations F target h}
    μ.prob (E ∩ {x | x ≠ none}) ≤ 2 * p * μ.prob E := by
  classical
  dsimp only
  apply erasure_posterior μ p hp habsent hpresent
  intro x hx
  have hpos : (positives F (Function.update H c (x.elim ∅ support)) h c).card ≤ 2 := by
    rw [positives_of_observations F _ target h hx]
    exact hcount
  have he := erase_observations F (Function.update H c (x.elim ∅ support)) h c hpos
  simpa only [Set.mem_ofPred_eq, Function.update_idem, Option.elim_none] using he.trans hx

end TwoAnchor

end SteinerLowerBound

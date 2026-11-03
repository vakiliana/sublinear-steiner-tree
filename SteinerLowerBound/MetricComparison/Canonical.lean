module

public import SteinerLowerBound.MetricComparison.PostActivation

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S C : Type*} [Fintype S]

theorem queried_append_mem (qs : List (C × S)) (q : C × S) (c : C) (u : S) :
    u ∈ TwoAnchor.queried (qs ++ [q]) c ↔
      u ∈ TwoAnchor.queried qs c ∨ q = (c, u) := by
  simp only [TwoAnchor.queried, Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_append, List.mem_singleton]
  tauto

theorem blocked_append_mem (F : C → Finset S) (qs : List (C × S))
    (q : C × S) (c : C) (u : S) :
    u ∈ TwoAnchor.blocked F (qs ++ [q]) c ↔
      u ∈ TwoAnchor.blocked F qs c ∨
        (q = (c, u) ∧ u ∉ F c ∧ ¬TwoAnchor.active F qs c) := by
  classical
  simp only [TwoAnchor.blocked, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu, i, hi, ha⟩
    by_cases hlt : i.val < qs.length
    · left
      refine ⟨hu, ⟨i.val, hlt⟩, ?_, ?_⟩
      · simpa only [List.get_eq_getElem, List.getElem_append_left hlt] using hi
      · simpa only [List.take_append_of_le_length hlt.le] using ha
    · right
      have hlast : i.val = qs.length := by
        have hh := i.isLt
        simp only [List.length_append, List.length_singleton] at hh
        omega
      refine ⟨?_, hu, ?_⟩
      · simpa only [List.get_eq_getElem, hlast, List.getElem_append_right (le_refl _),
          Nat.sub_self, List.getElem_cons_zero] using hi
      · simpa only [hlast, List.take_append_of_le_length (le_refl _), List.take_length] using ha
  · rintro (⟨hu, i, hi, ha⟩ | ⟨hq, hu, ha⟩)
    · refine ⟨hu, ⟨i.val, by simp only [List.length_append, List.length_singleton]; omega⟩,
        ?_, ?_⟩
      · simpa only [List.get_eq_getElem, List.getElem_append_left i.isLt] using hi
      · simpa only [List.take_append_of_le_length i.isLt.le] using ha
    · refine ⟨hu, ⟨qs.length, by simp⟩, ?_, ?_⟩
      · simpa only [List.get_eq_getElem, List.getElem_append_right (le_refl _),
          Nat.sub_self, List.getElem_cons_zero] using hq
      · simpa only [List.take_append_of_le_length (le_refl _), List.take_length] using ha

def Represents (F H : C → Finset S) (qs : List (C × S)) (h : C → History S) : Prop :=
  ∀ c, (h c).Valid ∧ (h c).gatedCompatible (F c) (F c ∪ H c) ∧
    TwoAnchor.queried qs c = (h c).positive ∪ (h c).negative ∧
      TwoAnchor.blocked F qs c =
        if 2 ≤ (h c).positive.card then (h c).blocked else (h c).negative

theorem represents_initial (F H : C → Finset S) :
    Represents F H [] (fun _ => History.initial) := by
  intro c
  simp [History.Valid, History.initial, History.gatedCompatible,
    History.compatible, TwoAnchor.queried, TwoAnchor.blocked]

theorem active_iff_two (F H : C → Finset S) (qs : List (C × S))
    (h : C → History S) (hr : Represents F H qs h) (c : C) :
    TwoAnchor.active F qs c ↔ 2 ≤ (h c).positive.card := by
  classical
  obtain ⟨hv, hc, hq, _⟩ := hr c
  by_cases hp : (h c).positive.card ≤ 1
  · have hc' : (h c).compatible (F c) := by
      simpa only [History.gatedCompatible, hp, ↓reduceIte] using hc
    have hna : ¬TwoAnchor.active F qs c := by
      rintro ⟨hcard, hsub⟩
      have hFP : F c ⊆ (h c).positive := by
        intro u hu
        have hh := hsub hu
        rw [hq] at hh
        rcases Finset.mem_union.mp hh with hh | hh
        · exact hh
        · exact False.elim (Finset.disjoint_left.mp hc'.2 hu hh)
      have hh := Finset.card_le_card hFP
      rw [hcard] at hh
      omega
    simp only [hna, show ¬2 ≤ (h c).positive.card by omega]
  · have hp₂ : 2 ≤ (h c).positive.card := by omega
    have ha : TwoAnchor.active F qs c := by
      by_cases hp' : (h c).positive.card = 2
      · have hc' : F c = (h c).positive := by
          have hh := hc
          simp only [History.gatedCompatible, hp, hp', ↓reduceIte] at hh
          exact hh.1
        refine ⟨by simpa only [hc'] using hp', ?_⟩
        rw [hc', hq]
        exact Finset.subset_union_left
      · have hc' : F c = (h c).anchors := by
          have hh := hc
          simp only [History.gatedCompatible, hp, hp', ↓reduceIte] at hh
          exact hh.1
        refine ⟨?_, ?_⟩
        · rw [hc', hv.2.2.1, min_eq_right hp₂]
        · rw [hc', hq]
          exact hv.2.1.trans Finset.subset_union_left
    simp only [ha, hp₂]

theorem represented_answer (F H : C → Finset S) (qs : List (C × S))
    (h : C → History S) (hr : Represents F H qs h) (c : C) (u : S) :
    (h c).gatedAnswer (F c) (F c ∪ H c) u = TwoAnchor.answer F H qs c u := by
  classical
  have ha := active_iff_two F H qs h hr c
  obtain ⟨hv, hc, _, hb⟩ := hr c
  by_cases hp : 2 ≤ (h c).positive.card
  · have hFP : F c ⊆ (h c).positive := by
      by_cases htwo : (h c).positive.card = 2
      · have he : F c = (h c).positive := by
          have hh : ¬(h c).positive.card ≤ 1 := by omega
          have hc' := hc
          simp only [History.gatedCompatible, hh, htwo, ↓reduceIte] at hc'
          exact hc'.1
        rw [he]
      · have he : F c = (h c).anchors := by
          have hh : ¬(h c).positive.card ≤ 1 := by omega
          have hc' := hc
          simp only [History.gatedCompatible, hh, htwo, ↓reduceIte] at hc'
          exact hc'.1
        rw [he]
        exact hv.2.1
    have hFb : Disjoint (F c) (h c).blocked :=
      Finset.disjoint_of_subset_left hFP
        (Finset.disjoint_of_subset_right hv.2.2.2.1 hv.1)
    rw [if_pos hp] at hb
    simp only [History.gatedAnswer, TwoAnchor.answer]
    apply decide_eq_decide.mpr
    simp only [(ha.mpr hp), hp, hb, true_and, Finset.disjoint_union_left,
      hFb, Finset.mem_union]
    tauto
  · have hna : ¬TwoAnchor.active F qs c := fun h => hp (ha.mp h)
    simp [History.gatedAnswer, TwoAnchor.answer, hp, hna]

theorem represents_append (F H : C → Finset S) (hF : ∀ c, (F c).card ≤ 2)
    (qs : List (C × S)) (h : C → History S) (hr : Represents F H qs h)
    (c : C) (u : S) (hf : (h c).Fresh u) (b : Bool)
    (hb : (h c).gatedAnswer (F c) (F c ∪ H c) u = b) :
    Represents F H (qs ++ [(c, u)]) (Function.update h c ((h c).update u b)) := by
  classical
  intro i
  by_cases hic : i = c
  · subst i
    rw [Function.update_self]
    obtain ⟨hv, hc, hq, hblocked⟩ := hr c
    refine ⟨(h c).update_valid u b hv hf,
      (History.gatedCompatible_update (h c) u b hv hf _ _ (hF c)
        Finset.subset_union_left).mpr ⟨hc, hb⟩, ?_, ?_⟩
    · ext v
      rw [queried_append_mem, hq]
      cases b <;>
        simp only [History.update, Bool.false_eq_true, ↓reduceIte,
          Finset.mem_union, Finset.mem_insert, Prod.mk.injEq, true_and] <;> tauto
    · ext v
      rw [blocked_append_mem, hblocked]
      have hact := active_iff_two F H qs h hr c
      by_cases hp : (h c).positive.card ≤ 1
      · have hnp : ¬2 ≤ (h c).positive.card := by omega
        have hna : ¬TwoAnchor.active F qs c := fun hh => hnp (hact.mp hh)
        cases b
        · have hu : u ∉ F c := by
            simpa only [History.gatedAnswer, hnp, false_and, or_false,
              decide_eq_false_iff_not] using hb
          by_cases hvu : v = u
          · subst v
            simp [History.update, hnp, hna, hu]
          · simp [History.update, hnp, hna, hvu, Ne.symm hvu]
        · have hu : u ∈ F c := by
            simpa only [History.gatedAnswer, hnp, false_and, or_false,
              decide_eq_true_eq] using hb
          have hcard : (insert u (h c).positive).card = (h c).positive.card + 1 :=
            Finset.card_insert_of_notMem hf.1
          by_cases hp₀ : (h c).positive.card = 0
          · by_cases hvu : v = u
            · subst v
              simp [History.update, hnp, hna, hu, hcard, hp₀]
            · simp [History.update, hnp, hna, hu, hcard, hp₀, hvu, Ne.symm hvu]
          · have hp₁ : (h c).positive.card = 1 := by omega
            by_cases hvu : v = u
            · subst v
              simp [History.update, hnp, hna, hu, hcard, hp₁]
            · simp [History.update, hnp, hna, hu, hcard, hp₁, hvu, Ne.symm hvu]
      · have hp₂ : 2 ≤ (h c).positive.card := by omega
        have ha : TwoAnchor.active F qs c := hact.mpr hp₂
        have hpn : (h c).positive.card ≠ 1 := by omega
        cases b
        · simp [History.update, hp₂, ha]
        · have hcard : (insert u (h c).positive).card = (h c).positive.card + 1 :=
            Finset.card_insert_of_notMem hf.1
          simp [History.update, hp₂, ha, hpn, hcard, show 2 ≤ (h c).positive.card + 1 by omega]
  · simp only [Function.update_of_ne hic]
    obtain ⟨hv, hc, hq, hblocked⟩ := hr i
    refine ⟨hv, hc, ?_, ?_⟩
    · ext v
      rw [queried_append_mem]
      simp only [Prod.mk.injEq, Ne.symm hic, false_and, or_false, hq]
    · ext v
      rw [blocked_append_mem]
      simp only [Prod.mk.injEq, Ne.symm hic, false_and, or_false, hblocked]

noncomputable def canonicalRun
    (schedule : Control C (History S) → Option (C × S)) (F H : C → Finset S) :
    (n : ℕ) → Control C (History S) → List (C × S) → Answers n
  | 0, _, _ => ()
  | n + 1, x, qs =>
    let b := match schedule x with
      | none => false
      | some (c, u) => TwoAnchor.answer F H qs c u
    let qs' := match schedule x with
      | none => qs
      | some q => qs ++ [q]
    (b, canonicalRun schedule F H n
      (Control.advance (History.memory S) schedule x b) qs')

theorem run_eq_canonical {Ω : Type*}
    (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule)
    (σ : C → GatedState S k.d) (n : ℕ)
    (x : Control C (History S)) (qs : List (C × S))
    (hr : Represents (fun c => fillerNeighbors (σ c).1)
      (fun c => potentialSupport (σ c).2) qs x.history) :
    (gatedObserver k w hsmall).run schedule σ n x =
      canonicalRun schedule (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) n x qs := by
  induction n generalizing x qs with
  | zero => rfl
  | succ n ih =>
    have hx : x.Valid (History.memory S) := fun c => (hr c).1
    cases he : schedule x with
    | none =>
      simp only [Observer.run, Observer.globalAnswer, he, canonicalRun]
      apply congrArg (Prod.mk false)
      apply ih
      simpa only [Control.advance, he] using hr
    | some cu =>
      rcases cu with ⟨c, u⟩
      have ha := represented_answer (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) qs x.history hr c u
      change (x.history c).gatedAnswer (fillerNeighbors (σ c).1) (jointSupport (σ c)) u =
        TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) qs c u at ha
      simp only [Observer.run, Observer.globalAnswer, he, gatedObserver, canonicalRun]
      rw [ha]
      apply congrArg (Prod.mk _)
      apply ih
      simp only [Control.advance, he]
      exact represents_append _ _ (fun c => filler_card_le_two (σ c).1)
        qs x.history hr c u (hs x hx c u he) _ ha

noncomputable def canonicalObservationLaw {Ω : Type*} [Fintype C]
    (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (schedule : Control C (History S) → Option (C × S)) (q : ℕ) : Law (Answers q) :=
  (gatedCentersLaw k w hsmall).map (fun σ =>
    canonicalRun schedule (fun c => fillerNeighbors (σ c).1)
      (fun c => potentialSupport (σ c).2) q (Control.initial (History.memory S)) [])

theorem observationLaw_eq_canonical {Ω : Type*} [Fintype C]
    (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule) (q : ℕ) :
    (gatedObserver k w hsmall).observationLaw schedule q =
      canonicalObservationLaw k w hsmall schedule q := by
  unfold Observer.observationLaw canonicalObservationLaw gatedCentersLaw
  congr 1
  funext σ
  exact run_eq_canonical k w hsmall schedule hs σ q _ _
    (represents_initial _ _)

end SteinerLowerBound.MetricComparison

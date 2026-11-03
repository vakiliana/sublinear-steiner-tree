module

public import SteinerLowerBound.Screening.NoticeProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem counter_increment_le_one (π : Equiv.Perm (Terminal S G I))
    (H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (q : Query (Terminal S G I) C) (u : Terminal S G I) :
    (counterLabels π H (h ++ [q]) u).card ≤ (counterLabels π H h u).card + 1 := by
  rw [counterLabels_append]
  have hh := Finset.card_union_le (counterLabels π H h u) (counterLabels π H [q] u)
  have hq : (counterLabels π H [q] u).card ≤ 1 := by
    cases q with
    | tt => simp [counterLabels]
    | cc => simp [counterLabels]
    | ct c x =>
        rw [counterLabels_singleton_ct]
        split_ifs <;> simp
  omega

theorem counter_increment_source (π : Equiv.Perm (Terminal S G I))
    (H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (q : Query (Terminal S G I) C) (u : Terminal S G I)
    (hi : (counterLabels π H h u).card < (counterLabels π H (h ++ [q]) u).card) :
    ∃ c x, q = .ct c x ∧ π u ∈ H c := by
  classical
  rw [counterLabels_append] at hi
  cases q with
  | tt => simp [counterLabels] at hi
  | cc => simp [counterLabels] at hi
  | ct c x =>
      refine ⟨c, x, rfl, ?_⟩
      by_contra hu
      rw [counterLabels_singleton_ct] at hi
      simp [hu] at hi

noncomputable def relevantIncrements (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    Finset (Terminal S G I) :=
  let s := analyze π F H D t R h
  if s.stop = none ∧ ¬Lucky π H s.exposed q then
    Finset.univ.filter fun u => u ∉ s.exposed ∧
      (counterLabels π H h u).card < (counterLabels π H (h ++ [q]) u).card else ∅

theorem advance_exposed_mono (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C) :
    s.exposed ⊆ (advance π F H D t R h s q).exposed := by
  rcases advance_exposed_cases π F H D t R h s q with he | he
  · rw [he]
  · rw [he]
    exact addNotices_mono _ _ _ _

theorem starCounter_witness (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (s : Book (Terminal S G I))
    (q : Query (Terminal S G I) C) (hn : s.stop = none)
    (hl : ¬Lucky π H s.exposed q)
    (hs : (advance π F H D t R h s q).stop = some .starCounter) :
    ∃ u, u ∉ (advance π F H D t R h s q).exposed ∧
      t ≤ (counterLabels π H (h ++ [q]) u).card := by
  classical
  simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte] at hs ⊢
  split_ifs at hs with hm hx hN hQ
  · cases hs
  · obtain ⟨u, _, hu, hb⟩ := hx
    exact ⟨u, hu, hb⟩
  · cases hs
  · cases hs

theorem star_counter_charging (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    ((analyze π F H D t R h).stop = none →
      ∀ u, u ∉ (analyze π F H D t R h).exposed →
        ((counterLabels π H h u).card : ℝ) ≤
          historyCharge (fun h q => ((relevantIncrements π F H D t R h q).card : ℝ)) h) ∧
    ((analyze π F H D t R h).stop = some .starCounter →
      (t : ℝ) ≤ historyCharge (fun h q => ((relevantIncrements π F H D t R h q).card : ℝ)) h) := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [Book.initial, counterLabels]
  | append_singleton h q ih =>
      rw [analyze_append, historyCharge_append]
      let s := analyze π F H D t R h
      by_cases hn : s.stop = none
      · by_cases hl : Lucky π H s.exposed q
        · have hs : (advance π F H D t R h s q).stop = some .lucky := by
            simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte]
          constructor
          · intro hnone
            have hh : (some StopKind.lucky : Option StopKind) = none := hs.symm.trans hnone
            cases hh
          · intro hstar
            have hh : (some StopKind.lucky : Option StopKind) = some .starCounter := hs.symm.trans hstar
            cases hh
        · have gain (u : Terminal S G I)
              (hu : u ∉ (advance π F H D t R h s q).exposed) :
              ((counterLabels π H (h ++ [q]) u).card : ℝ) ≤
                historyCharge (fun h q => ((relevantIncrements π F H D t R h q).card : ℝ)) h +
                  (relevantIncrements π F H D t R h q).card := by
            have hout : u ∉ s.exposed := fun hh => hu (advance_exposed_mono π F H D t R h s q hh)
            have hp := ih.1 hn u hout
            by_cases hi : (counterLabels π H h u).card < (counterLabels π H (h ++ [q]) u).card
            · have hum : u ∈ relevantIncrements π F H D t R h q := by
                dsimp only [relevantIncrements]
                rw [if_pos ⟨hn, hl⟩]
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hout, hi⟩
              have hcard : (1 : ℝ) ≤ (relevantIncrements π F H D t R h q).card := by
                exact_mod_cast Finset.card_pos.mpr ⟨u, hum⟩
              have hone : ((counterLabels π H (h ++ [q]) u).card : ℝ) ≤
                  (counterLabels π H h u).card + 1 := by exact_mod_cast counter_increment_le_one π H h q u
              linarith
            · have hh : ((counterLabels π H (h ++ [q]) u).card : ℝ) ≤
                  (counterLabels π H h u).card := by exact_mod_cast Nat.le_of_not_gt hi
              have hc : (0 : ℝ) ≤ (relevantIncrements π F H D t R h q).card := Nat.cast_nonneg _
              linarith
          refine ⟨fun _ u hu => gain u hu, ?_⟩
          intro hs
          obtain ⟨u, hu, hb⟩ := starCounter_witness π F H D t R h s q hn hl hs
          have hb' : (t : ℝ) ≤ (counterLabels π H (h ++ [q]) u).card := by exact_mod_cast hb
          exact hb'.trans (gain u hu)
      · have he : advance π F H D t R h s q = s := by
          simp only [advance, hn, ne_eq, not_false_eq_true, ↓reduceIte]
        have hz : relevantIncrements π F H D t R h q = ∅ := by
          dsimp only [relevantIncrements]
          rw [if_neg (fun hh => hn hh.1)]
        rw [he, hz, Finset.card_empty, Nat.cast_zero, add_zero]
        exact ⟨fun hh => False.elim (hn hh), ih.2⟩

end Screening

end SteinerLowerBound

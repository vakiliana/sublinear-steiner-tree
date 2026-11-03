module

public import SteinerLowerBound.Screening.Transposition

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

noncomputable def externalLabels (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (g : G) : Finset (Terminal S G I) :=
  Finset.univ.filter fun x => x ∉ clusterLabels π g ∧
    ∃ v ∈ clusterLabels π g, Query.tt x v ∈ h ∨ Query.tt v x ∈ h

noncomputable def clusterExchanges (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u : Terminal S G I) (g : G) :
    Finset (Terminal S G I) :=
  ordinaryLabels π \ (clusterLabels π g ∪ marked π h ∪
    externalLabels π h g ∪ neighborClusters π h u)

theorem clusterExchanges_card (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u : Terminal S G I) (g : G) :
    Fintype.card G * Fintype.card I ≤ (clusterExchanges π h u g).card +
      Fintype.card I + (marked π h).card + (externalLabels π h g).card +
        degree h u * Fintype.card I := by
  classical
  have hc := Finset.card_le_card_sdiff_add_card (s := ordinaryLabels π)
    (t := clusterLabels π g ∪ marked π h ∪ externalLabels π h g ∪ neighborClusters π h u)
  have hu := Finset.card_union_le
    (clusterLabels π g ∪ marked π h ∪ externalLabels π h g) (neighborClusters π h u)
  have hu' := Finset.card_union_le (clusterLabels π g ∪ marked π h) (externalLabels π h g)
  have hu'' := Finset.card_union_le (clusterLabels π g) (marked π h)
  have hn := neighborClusters_card_le π h u
  rw [card_ordinaryLabels] at hc
  rw [card_clusterLabels] at hu''
  change _ ≤ (clusterExchanges π h u g).card + _ at hc
  omega

theorem unmarked_exchange_tt (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u x : Terminal S G I)
    (hu : u ∉ marked π h) (hx : x ∉ marked π h)
    (hfarU : ∀ v, Query.tt u v ∈ h ∨ Query.tt v u ∈ h → ¬SameCluster π x v)
    (hfarX : ∀ v, Query.tt x v ∈ h ∨ Query.tt v x ∈ h → ¬SameCluster π u v) :
    ∀ a b, Query.tt a b ∈ h → a ≠ b →
      (SameCluster π a b ↔ SameCluster (exchangeLabels π u x) a b) := by
  classical
  intro a b hab hne
  by_cases hau : a = u
  · subst a
    have hold := unmarked_pair π h hu hne (Or.inl hab)
    by_cases hbx : b = x
    · subst b
      have hnew : ¬SameCluster (exchangeLabels π u x) u x := by
        simpa [SameCluster, exchangeLabels_apply] using
          (fun hh => hold ((sameCluster_comm π _ _).mp hh))
      exact iff_of_false hold hnew
    · have hbu : b ≠ u := hne.symm
      have hnew : ¬SameCluster (exchangeLabels π u x) u b := by
        simpa [SameCluster, exchangeLabels_apply,
          Equiv.swap_apply_of_ne_of_ne hbu hbx] using hfarU b (Or.inl hab)
      exact iff_of_false hold hnew
  · by_cases hax : a = x
    · subst a
      have hold := unmarked_pair π h hx hne (Or.inl hab)
      by_cases hbu : b = u
      · subst b
        have hnew : ¬SameCluster (exchangeLabels π u x) x u := by
          simpa [SameCluster, exchangeLabels_apply] using
            (fun hh => hold ((sameCluster_comm π _ _).mp hh))
        exact iff_of_false hold hnew
      · have hbx : b ≠ x := hne.symm
        have hnew : ¬SameCluster (exchangeLabels π u x) x b := by
          simpa [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hbu hbx] using hfarX b (Or.inl hab)
        exact iff_of_false hold hnew
    · by_cases hbu : b = u
      · subst b
        have hold : ¬SameCluster π a u := by
          intro hh
          exact unmarked_pair π h hu hne.symm (Or.inr hab)
            ((sameCluster_comm π _ _).mp hh)
        have hnew : ¬SameCluster (exchangeLabels π u x) a u := by
          simpa [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hau hax] using
              (fun hh => hfarU a (Or.inr hab) ((sameCluster_comm π _ _).mp hh))
        exact iff_of_false hold hnew
      · by_cases hbx : b = x
        · subst b
          have hold : ¬SameCluster π a x := by
            intro hh
            exact unmarked_pair π h hx hne.symm (Or.inr hab)
              ((sameCluster_comm π _ _).mp hh)
          have hnew : ¬SameCluster (exchangeLabels π u x) a x := by
            simpa [SameCluster, exchangeLabels_apply,
              Equiv.swap_apply_of_ne_of_ne hau hax] using
                (fun hh => hfarX a (Or.inr hab) ((sameCluster_comm π _ _).mp hh))
          exact iff_of_false hold hnew
        · simp only [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hau hax, Equiv.swap_apply_of_ne_of_ne hbu hbx]

theorem cluster_exchange_observations (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (hF : Supported F) (hH : Supported H) (u : Terminal S G I) (g : G)
    (hug : u ∈ clusterLabels π g) (hum : u ∉ marked π h)
    (x : Terminal S G I) (hx : x ∈ clusterExchanges π h u g) :
    observations π F H h = observations (exchangeLabels π u x) F H h := by
  classical
  obtain ⟨hxo, hxe⟩ := Finset.mem_sdiff.mp hx
  have hxg : x ∉ clusterLabels π g := fun hm => hxe (by simp [hm])
  have hxm : x ∉ marked π h := fun hm => hxe (by simp [hm])
  have hxn : x ∉ neighborClusters π h u := fun hn => hxe (by simp [hn])
  have hxx : x ∉ externalLabels π h g := fun hh => hxe (by simp [hh])
  have huo : ¬specialPosition (π u) := by
    have hh := (mem_clusterLabels π g u).mp hug
    intro hs
    rw [clusterPosition_of_special hs] at hh
    cases hh
  have hxo' : ¬specialPosition (π x) := (mem_ordinaryLabels π x).mp hxo
  have hfarU (v : Terminal S G I) (hv : Query.tt u v ∈ h ∨ Query.tt v u ∈ h) :
      ¬SameCluster π x v := by
    intro hs
    exact hxn ((mem_neighborClusters π h u x).mpr
      ⟨v, (mem_ttNeighbors h u v).mpr hv, hs⟩)
  have hfarX (v : Terminal S G I) (hv : Query.tt x v ∈ h ∨ Query.tt v x ∈ h) :
      ¬SameCluster π u v := by
    rintro ⟨g', hug', hvg'⟩
    have hgg : g' = g := by
      have hug'' := (mem_clusterLabels π g u).mp hug
      rw [hug''] at hug'
      exact (Option.some.inj hug').symm
    subst g'
    exact hxx (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hxg, v, (mem_clusterLabels π g v).mpr hvg', hv⟩)
  have agrees (L : C → Finset (Terminal S G I)) (hL : Supported L) :
      TwoAnchor.AgreesOn (centerHistory h) (relabel π L)
        (relabel (exchangeLabels π u x) L) :=
    relabel_agrees_of_avoids π L _ u x (fun c _ _ _ =>
      ⟨fun hh => huo (hL c _ hh), fun hh => hxo' (hL c _ hh)⟩)
  exact observations_congr π _ F H h
    (unmarked_exchange_tt π h u x hum hxm hfarU hfarX) (agrees F hF) (agrees H hH)

noncomputable def clusterMates (π : Equiv.Perm (Terminal S G I)) (v : Terminal S G I) :
    Finset (Terminal S G I) :=
  match clusterPosition (π v) with
  | none => ∅
  | some g => clusterLabels π g

theorem card_clusterMates_le (π : Equiv.Perm (Terminal S G I)) (v : Terminal S G I) :
    (clusterMates π v).card ≤ Fintype.card I := by
  unfold clusterMates
  cases clusterPosition (π v) <;> simp

theorem mem_clusterMates (π : Equiv.Perm (Terminal S G I)) (v x : Terminal S G I) :
    x ∈ clusterMates π v ↔ SameCluster π x v := by
  classical
  unfold clusterMates SameCluster
  cases he : clusterPosition (π v) with
  | none => simp
  | some g => simp [mem_clusterLabels, eq_comm]

variable {Ξ : Type*} [Fintype Ξ]

theorem cluster_prefix_bound (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (h : List (Query (Terminal S G I) C)) (a : Fin h.length → Reply)
    (u v : Terminal S G I) (L : ℝ)
    (E : Set (Ξ × Equiv.Perm (Terminal S G I)))
    (hE : ∀ ω ∈ E, observations ω.2 (F ω.1) (H ω.1) h = a ∧
      u ∉ marked ω.2 h ∧ u ≠ v ∧
        ∃ g, u ∈ clusterLabels ω.2 g ∧ v ∈ clusterLabels ω.2 g ∧
          (Fintype.card I : ℝ) + (marked ω.2 h).card + (externalLabels ω.2 h g).card +
            degree h u * Fintype.card I ≤ L) :
    ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (shuffledLaw (T := Terminal S G I) μ).prob E ≤
      Fintype.card I * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | observations ω.2 (F ω.1) (H ω.1) h = a} := by
  classical
  let good := fun ω : Ξ × Equiv.Perm (Terminal S G I) =>
    if hω : ω ∈ E then
      clusterExchanges ω.2 h u (Classical.choose (hE ω hω).2.2.2) else ∅
  have good_eq (ω : Ξ × Equiv.Perm (Terminal S G I)) (hω : ω ∈ E) :
      good ω = clusterExchanges ω.2 h u (Classical.choose (hE ω hω).2.2.2) := by
    simp [good, hω]
  apply switching μ E _ u good (fun ω => clusterMates ω.2 v) _ (Fintype.card I)
  · intro ω hω
    have hg := Classical.choose_spec (hE ω hω).2.2.2
    have hc := clusterExchanges_card ω.2 h u (Classical.choose (hE ω hω).2.2.2)
    rw [good_eq ω hω]
    have hc' : (Fintype.card G * Fintype.card I : ℝ) ≤
        (clusterExchanges ω.2 h u (Classical.choose (hE ω hω).2.2.2)).card +
          Fintype.card I + (marked ω.2 h).card +
            (externalLabels ω.2 h (Classical.choose (hE ω hω).2.2.2)).card +
              degree h u * Fintype.card I := by exact_mod_cast hc
    linarith [hg.2.2]
  · intro ω
    exact_mod_cast card_clusterMates_le ω.2 v
  · intro ω hω x hx
    rw [good_eq ω hω] at hx
    have hg := Classical.choose_spec (hE ω hω).2.2.2
    have he := cluster_exchange_observations ω.2 (F ω.1) (H ω.1) h
      (hF ω.1) (hH ω.1) u (Classical.choose (hE ω hω).2.2.2)
        hg.1 (hE ω hω).2.1 x hx
    exact he.symm.trans (hE ω hω).1
  · intro ω hω x hx
    rw [good_eq ω hω] at hx
    have hg := Classical.choose_spec (hE ω hω).2.2.2
    have hxg : x ∉ clusterLabels ω.2 (Classical.choose (hE ω hω).2.2.2) := by
      intro hh
      exact (Finset.mem_sdiff.mp hx).2
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hh)))
    have hvu : v ≠ u := (hE ω hω).2.2.1.symm
    have hvx : v ≠ x := fun he => hxg (he ▸ hg.2.1)
    change x ∈ clusterMates (exchangeLabels ω.2 u x) v
    rw [mem_clusterMates]
    simp only [SameCluster, exchangeLabels_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hvu hvx]
    exact ⟨Classical.choose (hE ω hω).2.2.2,
      (mem_clusterLabels _ _ _).mp hg.1, (mem_clusterLabels _ _ _).mp hg.2.1⟩

end Screening

end SteinerLowerBound

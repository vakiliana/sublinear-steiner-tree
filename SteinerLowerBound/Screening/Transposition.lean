module

public import SteinerLowerBound.Screening.Counters

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

theorem special_exchange_tt (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u x : Terminal S G I)
    (hu : specialPosition (π u)) (hx : x ∉ marked π h)
    (hn : x ∉ neighborClusters π h u) :
    ∀ a b, Query.tt a b ∈ h → a ≠ b →
      (SameCluster π a b ↔ SameCluster (exchangeLabels π u x) a b) := by
  classical
  have hfar (v : Terminal S G I) (hv : Query.tt u v ∈ h ∨ Query.tt v u ∈ h) :
      ¬SameCluster π x v := by
    intro hs
    exact hn ((mem_neighborClusters π h u x).mpr
      ⟨v, (mem_ttNeighbors h u v).mpr hv, hs⟩)
  have hsu (v : Terminal S G I) : ¬SameCluster π u v :=
    not_sameCluster_of_special_left π hu v
  have hsu' (v : Terminal S G I) : ¬SameCluster π v u :=
    fun hv => hsu v ((sameCluster_comm π _ _).mp hv)
  intro a b hab hne
  by_cases hau : a = u
  · subst a
    by_cases hbx : b = x
    · subst b
      have hnew : ¬SameCluster (exchangeLabels π u x) u x := by
        simpa [SameCluster, exchangeLabels_apply] using hsu' x
      exact iff_of_false (hsu x) hnew
    · have hbu : b ≠ u := hne.symm
      have hnew : ¬SameCluster (exchangeLabels π u x) u b := by
        simpa [SameCluster, exchangeLabels_apply,
          Equiv.swap_apply_of_ne_of_ne hbu hbx] using hfar b (Or.inl hab)
      exact iff_of_false (hsu b) hnew
  · by_cases hax : a = x
    · subst a
      have hold : ¬SameCluster π x b := unmarked_pair π h hx hne (Or.inl hab)
      by_cases hbu : b = u
      · subst b
        have hnew : ¬SameCluster (exchangeLabels π u x) x u := by
          simpa [SameCluster, exchangeLabels_apply] using hsu x
        exact iff_of_false hold hnew
      · have hbx : b ≠ x := hne.symm
        have hnew : ¬SameCluster (exchangeLabels π u x) x b := by
          simpa [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hbu hbx] using hsu b
        exact iff_of_false hold hnew
    · by_cases hbu : b = u
      · subst b
        have hnew : ¬SameCluster (exchangeLabels π u x) a u := by
          have hf := fun hh => hfar a (Or.inr hab) ((sameCluster_comm π _ _).mp hh)
          simpa [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hau hax] using hf
        exact iff_of_false (hsu' a) hnew
      · by_cases hbx : b = x
        · subst b
          have hold : ¬SameCluster π a x := by
            intro hs
            exact unmarked_pair π h hx hne.symm (Or.inr hab)
              ((sameCluster_comm π _ _).mp hs)
          have hnew : ¬SameCluster (exchangeLabels π u x) a x := by
            simpa [SameCluster, exchangeLabels_apply,
              Equiv.swap_apply_of_ne_of_ne hau hax] using hsu' a
          exact iff_of_false hold hnew
        · simp only [SameCluster, exchangeLabels_apply,
            Equiv.swap_apply_of_ne_of_ne hau hax, Equiv.swap_apply_of_ne_of_ne hbu hbx]

theorem special_exchange_observations (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) (hu : specialPosition (π u)) (hq : Quiet π F H h u)
    (hF : Supported F) (hH : Supported H)
    (x : Terminal S G I) (hx : x ∈ specialExchanges π F H h u) :
    observations π F H h = observations (exchangeLabels π u x) F H h := by
  classical
  obtain ⟨hxo, hxe⟩ := Finset.mem_sdiff.mp hx
  have hxm : x ∉ marked π h := fun hm => hxe (by simp [hm])
  have hxn : x ∉ neighborClusters π h u := fun hn => hxe (by simp [hn])
  have hxbF : x ∉ counterLabels π F h u := fun hb => hxe (by simp [hb])
  have hxbH : x ∉ counterLabels π H h u := fun hb => hxe (by simp [hb])
  have hxo' : ¬specialPosition (π x) := (mem_ordinaryLabels π x).mp hxo
  have avoids {L : C → Finset (Terminal S G I)}
      (hL : Supported L) (hqL : ∀ c, Query.ct c u ∈ h → π u ∉ L c)
      (hxbL : x ∉ counterLabels π L h u) :
      ∀ c v, (c, v) ∈ centerHistory h → v = u ∨ v = x → π u ∉ L c ∧ π x ∉ L c := by
    intro c v hv huv
    refine ⟨?_, fun hh => hxo' (hL c (π x) hh)⟩
    rcases huv with hvu | hvx
    · subst v
      exact hqL c ((mem_centerHistory h c u).mp hv)
    · subst v
      intro hh
      exact hxbL (Finset.mem_filter.mpr
        ⟨hxo, c, (mem_centerHistory h c x).mp hv, hh⟩)
  apply observations_congr π _ F H h (special_exchange_tt π h u x hu hxm hxn)
  · exact relabel_agrees_of_avoids π F _ u x
      (avoids hF (fun c hc => (hq c hc).1) hxbF)
  · exact relabel_agrees_of_avoids π H _ u x
      (avoids hH (fun c hc => (hq c hc).2) hxbH)

variable {Ξ : Type*} [Fintype Ξ]

def Screenable (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) (L : ℝ) : Prop :=
  specialPosition (π u) ∧ Quiet π F H h u ∧
    ((marked π h).card : ℝ) + degree h u * Fintype.card I +
      (counterLabels π F h u).card + (counterLabels π H h u).card ≤ L

theorem screenable_exchange_count (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) (L : ℝ) (hu : Screenable π F H h u L) :
    (Fintype.card G * Fintype.card I : ℝ) - L ≤
      (specialExchanges π F H h u).card := by
  have hc := specialExchanges_card π F H h u
  have hc' : (Fintype.card G * Fintype.card I : ℝ) ≤
      (specialExchanges π F H h u).card + (marked π h).card +
        degree h u * Fintype.card I + (counterLabels π F h u).card +
          (counterLabels π H h u).card := by exact_mod_cast hc
  linarith [hu.2.2]

theorem restricted_special_exchange (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (h : List (Query (Terminal S G I) C)) (a : Fin h.length → Reply)
    (u : Terminal S G I) (J : Ξ → Finset (Terminal S G I)) (B L : ℝ)
    (hJ : ∀ ξ, ((J ξ).card : ℝ) ≤ B)
    (E : Set (Ξ × Equiv.Perm (Terminal S G I)))
    (hE : ∀ ω ∈ E, observations ω.2 (F ω.1) (H ω.1) h = a ∧
      Screenable ω.2 (F ω.1) (H ω.1) h u L ∧ ω.2 u ∈ J ω.1) :
    ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (shuffledLaw (T := Terminal S G I) μ).prob E ≤
      B * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | observations ω.2 (F ω.1) (H ω.1) h = a} := by
  classical
  apply switching μ E _ u
    (fun ω => specialExchanges ω.2 (F ω.1) (H ω.1) h u)
    (fun ω => (J ω.1).map ω.2.symm.toEmbedding) _ B
  · intro ω hω
    exact screenable_exchange_count _ _ _ _ _ _ (hE ω hω).2.1
  · intro ω
    simpa using hJ ω.1
  · intro ω hω x hx
    have hs := special_exchange_observations ω.2 (F ω.1) (H ω.1) h u
      (hE ω hω).2.1.1 (hE ω hω).2.1.2.1 (hF ω.1) (hH ω.1) x hx
    exact hs.symm.trans (hE ω hω).1
  · intro ω hω x hx
    simp only [switch, Finset.mem_map_equiv, Equiv.symm_symm, exchangeLabels_apply,
      Equiv.swap_apply_right]
    exact (hE ω hω).2.2

theorem special_prefix_bound (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (h : List (Query (Terminal S G I) C)) (a : Fin h.length → Reply)
    (u : Terminal S G I) (L : ℝ) :
    ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (shuffledLaw (T := Terminal S G I) μ).prob
          {ω | observations ω.2 (F ω.1) (H ω.1) h = a ∧
            Screenable ω.2 (F ω.1) (H ω.1) h u L} ≤
      Fintype.card S * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | observations ω.2 (F ω.1) (H ω.1) h = a} := by
  apply restricted_special_exchange μ F H hF hH h a u
    (fun _ => Finset.univ.map (Function.Embedding.inl : S ↪ Terminal S G I))
    (Fintype.card S) L (by intro ξ; simp)
  intro ω hω
  refine ⟨hω.1, hω.2, ?_⟩
  have hs : specialPosition (ω.2 u) := hω.2.1
  cases he : ω.2 u with
  | inl s => simp [he]
  | inr p => simp [he, specialPosition] at hs

theorem anchor_prefix_bound (μ : Law Ξ)
    (F H : Ξ → C → Finset (Terminal S G I))
    (hF : ∀ ξ, Supported (F ξ)) (hH : ∀ ξ, Supported (H ξ))
    (hcard : ∀ ξ c, (F ξ c).card ≤ 2)
    (h : List (Query (Terminal S G I) C)) (a : Fin h.length → Reply)
    (u : Terminal S G I) (c : C) (L : ℝ) :
    ((Fintype.card G * Fintype.card I : ℝ) - L) *
        (shuffledLaw (T := Terminal S G I) μ).prob
          {ω | observations ω.2 (F ω.1) (H ω.1) h = a ∧
            Screenable ω.2 (F ω.1) (H ω.1) h u L ∧ ω.2 u ∈ F ω.1 c} ≤
      2 * (shuffledLaw (T := Terminal S G I) μ).prob
        {ω | observations ω.2 (F ω.1) (H ω.1) h = a} := by
  apply restricted_special_exchange μ F H hF hH h a u (fun ξ => F ξ c) 2 L
  · intro ξ
    exact_mod_cast hcard ξ c
  · intro ω hω
    exact hω

end Screening

end SteinerLowerBound

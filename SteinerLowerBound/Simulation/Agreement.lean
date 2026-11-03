module

public import SteinerLowerBound.Simulation.Simulator

@[expose] public section

namespace SteinerLowerBound.Simulation.Public

open scoped Classical
open HardDistribution
open MetricComparison.Public

variable {S G I C Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def internalFillers (F : C → Filler S) : C → Finset (Terminal S G I) :=
  internalSupport (fun c => fillerNeighbors (F c))

noncomputable def internalStars (d : ℕ) (H : C → Option (Subsets S d)) :
    C → Finset (Terminal S G I) :=
  internalSupport (fun c => (H c).elim ∅ Subtype.val)

noncomputable def actualAnswer (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) :=
  Screening.queryAnswer π (internalFillers F) (internalStars d H)

noncomputable def actualBook (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) : Screening.Book (Terminal S G I) :=
  Screening.analyze π (internalFillers F) (internalStars d H) D t R h

theorem internalSupport_supported (L : C → Finset S) :
    Screening.Supported (internalSupport (G := G) (I := I) L) := by
  intro c u hu
  obtain ⟨s, _, rfl⟩ := Finset.mem_map.mp hu
  trivial

theorem ready_closed (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (s : SimState S G I C d) (hc : s.cache.Consistent (bits d H))
    (hr : Ready (access π d F) (support π d) s) (hn : s.stop = none) :
    TwoAnchor.Closed (fillers π F) (stars π d H) s.exposed := by
  intro c hv
  obtain ⟨x, hx, hxc, hxb, hxs⟩ := visible_candidate π d F H ha s.exposed c hv
  have hxr := (hr hn).1 hx
  have hxk := (hc.2 x hxr).mpr hxb
  intro u hu
  apply (hr hn).2
  exact Finset.mem_biUnion.mpr ⟨x, hxk, hxs.symm ▸ hu⟩

theorem closed_access (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d))
    (B : Finset (Terminal S G I)) (hB : TwoAnchor.Closed (fillers π F) (stars π d H) B) :
    ∀ Q ⊆ B, ∀ x ∈ access π d F Q, bits d H x = true → support π d x ⊆ B := by
  intro Q hQ x hx hb
  obtain ⟨hv, hs⟩ := candidate_visible π d F H Q x hx hb
  rw [hs]
  exact hB x.1 (TwoAnchor.visible_mono _ _ hQ x.1 hv)

theorem close_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (cap : ℕ) (s : SimState S G I C d)
    (hs : Safe (access π d F) (support π d) cap s)
    (hc : s.cache.Consistent (bits d H)) (hn : s.stop = none)
    (hK : vertices (support π d) s.cache.kept ⊆ s.exposed)
    (hcap : (TwoAnchor.closure (fillers π F) (stars π d H) s.exposed).card ≤ cap) :
    let r := (close (access π d F) (support π d) cap (cap + 1) s).output (bits d H)
    r.stop = none ∧ r.noticed = s.noticed ∧
      r.exposed = TwoAnchor.closure (fillers π F) (stars π d H) s.exposed := by
  classical
  let B := TwoAnchor.closure (fillers π F) (stars π d H) s.exposed
  have hQB : s.exposed ⊆ B := TwoAnchor.subset_closure _ _ _
  have hB := TwoAnchor.closure_closed (fillers π F) (stars π d H) s.exposed
  have hb := close_bounded (access π d F) (support π d) cap (cap + 1) s (bits d H) B
    (by omega) hn hQB (hK.trans hQB) hcap (closed_access π d F H B hB)
  have hsp := close_spec (access π d F) (support π d) (access_mono π d F)
    cap (cap + 1) s hs (by omega)
  have hp := Spec.output _ _ _ _ hsp (bits d H)
  have hcc := Spec.consistent _ _ _ _ hsp (bits d H) hc
  refine ⟨hb.1, hp.2.2.1, Finset.Subset.antisymm hb.2 ?_⟩
  exact TwoAnchor.closure_minimal _ _ _ _ hp.2.2.2.1
    (ready_closed π d F H ha _ hcc hp.2.1 hb.1)

theorem cachedBit_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hn : s.stop = none)
    (h : List (Query (Terminal S G I) C)) (c : C) (u : Terminal S G I)
    (hanchors : TwoAnchor.active (fillers π F) (Screening.centerHistory h) c →
      fillers π F c ⊆ s.exposed)
    (hunlucky : u ∈ stars π d H c → u ∈ s.exposed) :
    cachedBit π d F s.cache h c u =
      TwoAnchor.answer (fillers π F) (stars π d H) (Screening.centerHistory h) c u := by
  classical
  unfold cachedBit TwoAnchor.answer
  apply decide_eq_decide.mpr
  constructor
  · rintro (hu | ⟨hact, x, hx, hxc, hdis, hux⟩)
    · exact Or.inl hu
    · have hxr := hs.1.read_subset (hc.1 hx)
      have hxb := (hc.2 x (hc.1 hx)).mp hx
      obtain ⟨_, he⟩ := candidate_visible π d F H s.requested x hxr hxb
      rw [hxc] at he
      exact Or.inr ⟨hact, he ▸ hdis, he ▸ hux⟩
  · rintro (hu | ⟨hact, hdis, huH⟩)
    · exact Or.inl hu
    · by_cases huF : u ∈ fillers π F c
      · exact Or.inl huF
      have hv := TwoAnchor.visible_of_third (fillers π F) (stars π d H) s.exposed c
        hact.1 (hanchors hact) (stars_anchored π d F H ha c ⟨u, huH⟩)
        u huH (hunlucky huH) huF
      obtain ⟨x, hx, hxc, hxb, he⟩ := visible_candidate π d F H ha s.exposed c hv
      have hxk := (hc.2 x ((hs.2.1 hn).1 hx)).mpr hxb
      exact Or.inr ⟨hact, x, hxk, hxc, he.symm ▸ hdis, he.symm ▸ huH⟩

theorem answer_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hn : s.stop = none)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (hcontacts : Screening.ContactsExposed π (internalFillers F) (internalStars d H) h s.exposed)
    (hlucky : ¬Screening.Lucky π (internalStars d H) s.exposed q) :
    answer π d F s.cache h q = actualAnswer π d F H h q := by
  classical
  cases q with
  | tt u v => rfl
  | cc c c' => rfl
  | ct c u =>
      have hanchors : TwoAnchor.active (fillers π F) (Screening.centerHistory h) c →
          fillers π F c ⊆ s.exposed := by
        rw [fillers_eq_relabel]
        exact Screening.active_anchors_exposed π (internalFillers F) (internalStars d H)
          h s.exposed hcontacts c
      have hunlucky : u ∈ stars π d H c → u ∈ s.exposed := by
        intro hu
        by_contra huQ
        rw [stars_eq_relabel] at hu
        have hmem := (Screening.mem_relabel _ _ _ _).mp hu
        exact hlucky ⟨c, u, rfl,
          internalSupport_supported _ c _ hmem, huQ, hmem⟩
      have he := cachedBit_actual π d F H ha R s hs hc hn h c u hanchors hunlucky
      simp only [answer, actualAnswer, Screening.queryAnswer]
      rw [he, fillers_eq_relabel, stars_eq_relabel]
      rfl

def Corresponds {d : ℕ} (s : SimState S G I C d) (b : Screening.Book (Terminal S G I)) : Prop :=
  s.stop = none ∧ s.noticed = b.noticed ∧ s.exposed = b.exposed

theorem addNotices_noticed_mono (L J : C → Finset (Terminal S G I))
    (b : Screening.Book (Terminal S G I)) (l : List (Terminal S G I)) :
    b.noticed ⊆ (Screening.addNotices L J b l).noticed := by
  classical
  induction l generalizing b with
  | nil => exact Finset.Subset.rfl
  | cons u l ih =>
      apply Finset.Subset.trans (s₂ := (Screening.addNotice L J b u).noticed) _ (ih _)
      by_cases hu : u ∈ b.exposed
      · simp only [Screening.addNotice, hu, ↓reduceIte]
        exact Finset.Subset.rfl
      · simp only [Screening.addNotice, hu, ↓reduceIte]
        exact Finset.subset_insert _ _

theorem noticeOne_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (u : Terminal S G I) (s : SimState S G I C d)
    (b : Screening.Book (Terminal S G I))
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hm : Corresponds s b)
    (hN : (Screening.addNotice (fillers π F) (stars π d H) b u).noticed.card ≤ R)
    (hQ : (Screening.addNotice (fillers π F) (stars π d H) b u).exposed.card ≤ 2 * R) :
    Corresponds ((noticeOne (access π d F) (support π d) R u s).output (bits d H))
      (Screening.addNotice (fillers π F) (stars π d H) b u) := by
  classical
  by_cases hu : u ∈ b.exposed
  · have hus : u ∈ s.exposed := hm.2.2.symm ▸ hu
    rw [noticeOne, if_pos (Or.inr hus)]
    simpa only [DecisionTree.output, Screening.addNotice, hu, ↓reduceIte] using hm
  have hus : u ∉ s.exposed := by simpa only [hm.2.2] using hu
  rw [noticeOne, if_neg (by simp [hm.1, hus])]
  dsimp only
  have hN' : (insert u s.noticed).card ≤ R := by
    simpa only [Screening.addNotice, hu, ↓reduceIte, hm.2.1] using hN
  rw [if_neg (Nat.not_lt.mpr hN')]
  let r : SimState S G I C d :=
    {s with noticed := insert u s.noticed, exposed := insert u s.exposed}
  have hr : Safe (access π d F) (support π d) (2 * R) r := by
    refine ⟨hs.1.requested_cap,
      hs.1.requested_subset.trans (Finset.subset_insert _ _),
      hs.1.read_subset, hs.1.kept_subset, ?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with h | hv
    · subst v
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    · rcases Finset.mem_union.mp (hs.1.cover hv) with hn | hk
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hn)
      · exact Finset.mem_union_right _ hk
  have hcap : (TwoAnchor.closure (fillers π F) (stars π d H) r.exposed).card ≤ 2 * R := by
    simpa only [Screening.addNotice, hu, ↓reduceIte, r, hm.2.2] using hQ
  have hclose := close_actual π d F H ha (2 * R) r hr hc hm.1
    (((hs.2.1 hm.1).2).trans (Finset.subset_insert _ _)) hcap
  refine ⟨hclose.1, ?_, ?_⟩
  · rw [hclose.2.1]
    simp only [r, Screening.addNotice, hu, ↓reduceIte, hm.2.1]
  · rw [hclose.2.2]
    simp only [r, Screening.addNotice, hu, ↓reduceIte, hm.2.2]

theorem noticeList_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (l : List (Terminal S G I)) (s : SimState S G I C d)
    (b : Screening.Book (Terminal S G I))
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hm : Corresponds s b)
    (hN : (Screening.addNotices (fillers π F) (stars π d H) b l).noticed.card ≤ R)
    (hQ : (Screening.addNotices (fillers π F) (stars π d H) b l).exposed.card ≤ 2 * R) :
    Corresponds ((noticeList (access π d F) (support π d) R l s).output (bits d H))
      (Screening.addNotices (fillers π F) (stars π d H) b l) := by
  induction l generalizing s b with
  | nil => exact hm
  | cons u l ih =>
      let b' := Screening.addNotice (fillers π F) (stars π d H) b u
      have hN' : b'.noticed.card ≤ R :=
        (Finset.card_le_card (addNotices_noticed_mono _ _ b' l)).trans hN
      have hQ' : b'.exposed.card ≤ 2 * R :=
        (Finset.card_le_card (Screening.addNotices_mono _ _ b' l)).trans hQ
      have hm' := noticeOne_actual π d F H ha R u s b hs hc hm hN' hQ'
      have hsp := noticeOne_spec (access π d F) (support π d) (access_mono π d F) R u s hs
      have hs' := Spec.output _ _ _ _ hsp (bits d H)
      have hc' := Spec.consistent _ _ _ _ hsp (bits d H) hc
      rw [noticeList, output_bind]
      exact ih _ b' hs' hc' hm' hN hQ

theorem advance_none_data (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (b : Screening.Book (Terminal S G I))
    (q : Query (Terminal S G I) C)
    (hn : (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).stop = none) :
    let b' := Screening.addNotices (fillers π F) (stars π d H) b
      (Screening.noticeOrder (Screening.noticeCandidates π (internalFillers F)
        (internalStars d H) D t h q b.exposed))
    (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).noticed = b'.noticed ∧
      (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).exposed = b'.exposed ∧
      b'.noticed.card ≤ R ∧ b'.exposed.card ≤ 2 * R := by
  classical
  obtain ⟨hold, hl, _, _⟩ :=
    Screening.advance_none π (internalFillers F) (internalStars d H) D t R h b q hn
  rw [fillers_eq_relabel, stars_eq_relabel]
  unfold Screening.advance at hn ⊢
  simp only [hold, ne_eq, not_true_eq_false, hl, ↓reduceIte] at hn ⊢
  split_ifs at hn ⊢ <;> simp_all [internalFillers, internalStars]

theorem actualBook_prefix_none (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h k : List (Query (Terminal S G I) C))
    (hn : (actualBook π d F H D t R (h ++ k)).stop = none) :
    (actualBook π d F H D t R h).stop = none := by
  induction k using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using hn
  | append_singleton k q ih =>
      rw [actualBook, ← List.append_assoc, Screening.analyze_append] at hn
      exact ih (Screening.advance_none π (internalFillers F) (internalStars d H)
        D t R (h ++ k) _ q hn).1

end SteinerLowerBound.Simulation.Public

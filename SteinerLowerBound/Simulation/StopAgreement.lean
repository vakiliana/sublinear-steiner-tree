module

public import SteinerLowerBound.Simulation.RunAgreement

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical

variable {T X : Type*}

theorem noticeList_stopped (D : Finset T → Finset X) (support : X → Finset T)
    (R : ℕ) (l : List T) (s : State T X) (hs : s.stop ≠ none) :
    noticeList D support R l s = .leaf s := by
  induction l with
  | nil => rfl
  | cons u l ih =>
      rw [noticeList, noticeOne, if_pos (Or.inl hs), bind, ih]

namespace Public

open HardDistribution
open MetricComparison.Public

variable {S G I C Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem run_stopped (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) (algorithm : DecisionTree (Query (Terminal S G I) C) Reply Z)
    (h : List (Query (Terminal S G I) C)) (s : SimState S G I C d)
    (hs : s.stop ≠ none) (o : Candidate S C d → Bool) :
    ((run π d F D t R algorithm h s).output o).state = s := by
  cases algorithm with
  | leaf => rfl
  | query q next => rw [run, if_pos hs]; rfl

theorem close_actual_or_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (cap : ℕ) (s : SimState S G I C d)
    (hs : Safe (access π d F) (support π d) cap s)
    (hc : s.cache.Consistent (bits d H)) (hn : s.stop = none)
    (hK : vertices (support π d) s.cache.kept ⊆ s.exposed) :
    let r := (close (access π d F) (support π d) cap (cap + 1) s).output (bits d H)
    r.stop = some .closure ∨
      (r.stop = none ∧ r.noticed = s.noticed ∧
        r.exposed = TwoAnchor.closure (fillers π F) (stars π d H) s.exposed) := by
  classical
  let r := (close (access π d F) (support π d) cap (cap + 1) s).output (bits d H)
  by_cases hr : r.stop = some .closure
  · exact Or.inl hr
  right
  have hsp := close_spec (access π d F) (support π d) (access_mono π d F)
    cap (cap + 1) s hs (by omega)
  have hp := Spec.output _ _ _ _ hsp (bits d H)
  have hn' : r.stop = none := by
    rcases hp.2.2.2.2.1 with h | h
    · exact h.trans hn
    · exact False.elim (hr h)
  have hcc := Spec.consistent _ _ _ _ hsp (bits d H) hc
  let B := TwoAnchor.closure (fillers π F) (stars π d H) s.exposed
  have hQB : s.exposed ⊆ B := TwoAnchor.subset_closure _ _ _
  have hB := TwoAnchor.closure_closed (fillers π F) (stars π d H) s.exposed
  have hupper := close_protected (access π d F) (support π d) cap (cap + 1)
    s (bits d H) B hQB (hK.trans hQB) (closed_access π d F H B hB)
  refine ⟨hn', hp.2.2.1, Finset.Subset.antisymm hupper ?_⟩
  exact TwoAnchor.closure_minimal _ _ _ _ hp.2.2.2.1
    (ready_closed π d F H ha _ hcc hp.2.1 hn')

theorem noticeOne_actual_or_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (u : Terminal S G I) (s : SimState S G I C d)
    (b : Screening.Book (Terminal S G I))
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hm : Corresponds s b)
    (hN : (Screening.addNotice (fillers π F) (stars π d H) b u).noticed.card ≤ R) :
    let r := (noticeOne (access π d F) (support π d) R u s).output (bits d H)
    r.stop = some .closure ∨
      Corresponds r (Screening.addNotice (fillers π F) (stars π d H) b u) := by
  classical
  by_cases hu : u ∈ b.exposed
  · have hus : u ∈ s.exposed := hm.2.2.symm ▸ hu
    rw [noticeOne, if_pos (Or.inr hus)]
    right
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
  rcases close_actual_or_overflow π d F H ha (2 * R) r hr hc hm.1
      (((hs.2.1 hm.1).2).trans (Finset.subset_insert _ _)) with hov | hclose
  · exact Or.inl hov
  · right
    refine ⟨hclose.1, ?_, ?_⟩
    · rw [hclose.2.1]
      simp only [r, Screening.addNotice, hu, ↓reduceIte, hm.2.1]
    · rw [hclose.2.2]
      simp only [r, Screening.addNotice, hu, ↓reduceIte, hm.2.2]

theorem noticeList_actual_or_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (R : ℕ) (l : List (Terminal S G I)) (s : SimState S G I C d)
    (b : Screening.Book (Terminal S G I))
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H)) (hm : Corresponds s b)
    (hN : (Screening.addNotices (fillers π F) (stars π d H) b l).noticed.card ≤ R) :
    let r := (noticeList (access π d F) (support π d) R l s).output (bits d H)
    r.stop = some .closure ∨
      Corresponds r (Screening.addNotices (fillers π F) (stars π d H) b l) := by
  induction l generalizing s b with
  | nil => exact Or.inr hm
  | cons u l ih =>
      let b' := Screening.addNotice (fillers π F) (stars π d H) b u
      have hN' : b'.noticed.card ≤ R :=
        (Finset.card_le_card (addNotices_noticed_mono _ _ b' l)).trans hN
      have hm' := noticeOne_actual_or_overflow π d F H ha R u s b hs hc hm hN'
      have hsp := noticeOne_spec (access π d F) (support π d) (access_mono π d F) R u s hs
      have hs' := Spec.output _ _ _ _ hsp (bits d H)
      have hc' := Spec.consistent _ _ _ _ hsp (bits d H) hc
      rw [noticeList, output_bind]
      rcases hm' with hov | hm'
      · rw [noticeList_stopped _ _ _ _ _ (by rw [hov]; simp)]
        exact Or.inl hov
      · exact ih _ b' hs' hc' hm' hN

theorem actualBook_stopped (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h k : List (Query (Terminal S G I) C))
    (hn : (actualBook π d F H D t R h).stop ≠ none) :
    actualBook π d F H D t R (h ++ k) = actualBook π d F H D t R h := by
  induction k using List.reverseRecOn with
  | nil => simp
  | append_singleton k q ih =>
      rw [actualBook, ← List.append_assoc, Screening.analyze_append]
      change Screening.advance π (internalFillers F) (internalStars d H) D t R (h ++ k)
        (actualBook π d F H D t R (h ++ k)) q = _
      rw [ih]
      exact if_pos hn

def NoOtherStop (b : Screening.Book (Terminal S G I)) : Prop :=
  b.stop = none ∨ b.stop = some .closure

theorem actualBook_prefix_noOtherStop (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h k : List (Query (Terminal S G I) C))
    (hn : NoOtherStop (actualBook π d F H D t R (h ++ k))) :
    NoOtherStop (actualBook π d F H D t R h) := by
  by_cases hh : (actualBook π d F H D t R h).stop = none
  · exact Or.inl hh
  · rwa [actualBook_stopped π d F H D t R h k hh] at hn

theorem advance_noOtherStop_data (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (b : Screening.Book (Terminal S G I))
    (q : Query (Terminal S G I) C) (hold : b.stop = none)
    (hn : NoOtherStop (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q)) :
    let b' := Screening.addNotices (fillers π F) (stars π d H) b
      (Screening.noticeOrder (Screening.noticeCandidates π (internalFillers F)
        (internalStars d H) D t h q b.exposed))
    ¬Screening.Lucky π (internalStars d H) b.exposed q ∧
      (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).noticed = b'.noticed ∧
      (Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).exposed = b'.exposed ∧
      b'.noticed.card ≤ R ∧
      ((Screening.advance π (internalFillers F) (internalStars d H) D t R h b q).stop =
        some .closure → 2 * R < b'.exposed.card) := by
  classical
  rw [fillers_eq_relabel, stars_eq_relabel]
  unfold NoOtherStop at hn
  unfold Screening.advance at hn ⊢
  simp only [hold, ne_eq, not_true_eq_false, ↓reduceIte] at hn ⊢
  split_ifs at hn ⊢ <;> simp_all [internalFillers, internalStars]

theorem run_actual_or_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (D t R : ℕ) (algorithm : DecisionTree (Query (Terminal S G I) C) Reply Z)
    (h : List (Query (Terminal S G I) C)) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H))
    (hm : Corresponds s (actualBook π d F H D t R h))
    (hold : (actualBook π d F H D t R h).stop = none)
    (hfinal : NoOtherStop (actualBook π d F H D t R
      (h ++ Screening.questions (onlineRun (actualAnswer π d F H) algorithm h).2))) :
    let r := (run π d F D t R algorithm h s).output (bits d H)
    r.state.stop = some .closure ∨
      (r.result = (onlineRun (actualAnswer π d F H) algorithm h).1 ∧
        r.transcript = (onlineRun (actualAnswer π d F H) algorithm h).2) := by
  classical
  induction algorithm generalizing h s with
  | leaf z => exact Or.inr ⟨rfl, rfl⟩
  | query q next ih =>
      let a := actualAnswer π d F H h q
      let tail := onlineRun (actualAnswer π d F H) (next a) (h ++ [q])
      have hfull : NoOtherStop (actualBook π d F H D t R
          ((h ++ [q]) ++ Screening.questions tail.2)) := by
        simpa only [onlineRun, Screening.questions, List.map_cons,
          List.singleton_append, List.append_assoc, a, tail] using hfinal
      have hnext := actualBook_prefix_noOtherStop π d F H D t R (h ++ [q])
        (Screening.questions tail.2) hfull
      have hadv : NoOtherStop (Screening.advance π (internalFillers F) (internalStars d H)
          D t R h (actualBook π d F H D t R h) q) := by
        simpa only [actualBook, Screening.analyze_append] using hnext
      have hdata := advance_noOtherStop_data π d F H D t R h
        (actualBook π d F H D t R h) q hold hadv
      have hcontacts : Screening.ContactsExposed π (internalFillers F) (internalStars d H)
          h s.exposed := by
        rw [hm.2.2]
        exact Screening.analyze_contacts π (internalFillers F) (internalStars d H)
          D t R (internalSupport_supported _) (internalSupport_supported _) h hold
      have he : answer π d F s.cache h q = a :=
        answer_actual π d F H ha R s hs hc hm.1 h q hcontacts (hm.2.2.symm ▸ hdata.1)
      let l := Screening.noticeOrder (Screening.noticeCandidates π (internalFillers F)
        (internalStars d H) D t h q (actualBook π d F H D t R h).exposed)
      let b' := Screening.addNotices (fillers π F) (stars π d H)
        (actualBook π d F H D t R h) l
      have hN : b'.noticed.card ≤ R := hdata.2.2.2.1
      let s' := (noticeList (access π d F) (support π d) R l s).output (bits d H)
      have hm' := noticeList_actual_or_overflow π d F H ha R l s
        (actualBook π d F H D t R h) hs hc hm hN
      have hsp := noticeList_spec (access π d F) (support π d) (access_mono π d F) R l s hs
      have hs' := Spec.output _ _ _ _ hsp (bits d H)
      have hc' := Spec.consistent _ _ _ _ hsp (bits d H) hc
      have hnots : notices π F D t h q a s.exposed =
          Screening.noticeCandidates π (internalFillers F) (internalStars d H)
            D t h q (actualBook π d F H D t R h).exposed := by
        rw [hm.2.2]
        exact notices_actual π F (internalStars d H) D t h q _
      rw [run, if_neg (by simp [hm.1])]
      dsimp only
      rw [he, hnots, output_bind, output_bind]
      rcases hm' with hov | hm'
      · left
        change ((run π d F D t R (next a) (h ++ [q]) s').output (bits d H)).state.stop = _
        rw [run_stopped π d F D t R (next a) (h ++ [q]) s' (by rw [hov]; simp)]
        exact hov
      · have hmatch : Corresponds s' (actualBook π d F H D t R (h ++ [q])) := by
          refine ⟨hm'.1, ?_, ?_⟩
          · rw [actualBook, Screening.analyze_append]
            exact hm'.2.1.trans hdata.2.1.symm
          · rw [actualBook, Screening.analyze_append]
            exact hm'.2.2.trans hdata.2.2.1.symm
        have hnnext : (actualBook π d F H D t R (h ++ [q])).stop = none := by
          rcases hnext with hn | hov
          · exact hn
          · have hcap := (hs'.2.2.1 hm'.1).2
            rw [hm'.2.2] at hcap
            have hlarge := hdata.2.2.2.2 (by
              simpa only [actualBook, Screening.analyze_append] using hov)
            exact False.elim (Nat.not_lt.mpr hcap hlarge)
        rcases ih a (h ++ [q]) s' hs' hc' hmatch hnnext hfull with hov | hagree
        · exact Or.inl hov
        · exact Or.inr ⟨hagree.1, congrArg (List.cons (q, a)) hagree.2⟩

theorem tree_actual_or_overflow (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (hn : NoOtherStop (actualBook π d F H D t R
      (Screening.questions (onlineRun (actualAnswer π d F H)
        (mapQuestions orient algorithm) []).2))) :
    let r := (tree π d F D t R algorithm).output (bits d H)
    r.state.stop = some .closure ∨
      (r.result = (gatedRun π (fun c => fillerNeighbors (F c))
        (fun c => (H c).elim ∅ Subtype.val) algorithm []).1 ∧
        r.transcript.map (fun qa => (encode qa.1, qa.2)) =
          (gatedRun π (fun c => fillerNeighbors (F c))
            (fun c => (H c).elim ∅ Subtype.val) algorithm []).2) := by
  have hr := run_actual_or_overflow π d F H ha D t R (mapQuestions orient algorithm) [] .initial
    (initial_stable _ _ R (access_empty π d F)) (Cache.empty_consistent (bits d H))
    (by simp [Corresponds, actualBook, Screening.analyze_nil, State.initial, Screening.Book.initial])
    (by simp [actualBook, Screening.analyze_nil, Screening.Book.initial])
    (by simpa only [List.nil_append] using hn)
  rcases hr with hov | hr
  · exact Or.inl hov
  right
  have ho := onlineRun_mapQuestions orient (actualAnswer π d F H) algorithm []
  simp only [List.map_nil] at ho
  have hanswer : (fun h q => actualAnswer π d F H (h.map orient) (orient q)) =
      gatedAnswer π (fun c => fillerNeighbors (F c)) (fun c => (H c).elim ∅ Subtype.val) := rfl
  rw [hanswer] at ho
  refine ⟨hr.1.trans (congrArg Prod.fst ho), ?_⟩
  rw [tree, hr.2]
  have he := congrArg (fun p => p.2.map (fun qa => (encode qa.1, qa.2))) ho
  simpa only [List.map_map, Function.comp_def, encode_orient, Prod.mk.eta,
    List.map_id', gatedRun] using he

end Public

end SteinerLowerBound.Simulation

module

public import SteinerLowerBound.Screening.Charges

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

theorem mask_card_bound {Ω T : Type*} [Fintype Ω] [Fintype T]
    (μ : Law Ω) (P : Ω → Prop) (s : Ω → Finset T) (e : Finset T) (F B : ℝ)
    (hs : ∀ ω, s ω ⊆ e)
    (h : ∀ u ∈ e, F * μ.prob {ω | P ω ∧ u ∈ s ω} ≤ B * μ.prob {ω | P ω}) :
    F * μ.expect (fun ω => if P ω then ((s ω).card : ℝ) else 0) ≤
      e.card * (B * μ.prob {ω | P ω}) := by
  classical
  rw [expect_mask_card, Finset.mul_sum]
  calc
    _ ≤ ∑ u, if u ∈ e then B * μ.prob {ω | P ω} else 0 := by
      apply Finset.sum_le_sum
      intro u _
      by_cases hu : u ∈ e
      · simpa only [hu, ↓reduceIte] using h u hu
      · have he : {ω | P ω ∧ u ∈ s ω} = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hu (hs ω hω.2)
        simp only [he, prob_empty, mul_zero, hu, ↓reduceIte, le_refl]
    _ = _ := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun u => u ∈ e) = e := by ext u; simp
      rw [he, Finset.sum_const, nsmul_eq_mul]

end Law

namespace Screening

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def directUnitNotices (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    Finset (Terminal S G I) :=
  let s := analyze π F H D t R h
  if s.stop = none ∧ ¬Lucky π H s.exposed q then
    (noticeCandidates π F H D t h q s.exposed).filter (UnitAt π F H h q) else ∅

noncomputable def directDegreeNotices (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    Finset (Terminal S G I) :=
  let s := analyze π F H D t R h
  if s.stop = none ∧ ¬Lucky π H s.exposed q then
    (noticeCandidates π F H D t h q s.exposed).filter
      (fun u => D ≤ degree (h ++ [q]) u) else ∅

noncomputable def fillerHigh (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) : Finset (Terminal S G I) :=
  Finset.univ.filter fun u => t ≤ (counterLabels π F h u).card

theorem fillerHigh_mono_append (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    fillerHigh π F t h ⊆ fillerHigh π F t (h ++ [q]) := by
  intro u hu
  simp only [fillerHigh, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rw [counterLabels_append]
  exact hu.trans (Finset.card_le_card Finset.subset_union_left)

theorem fillerHigh_budget (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (hcard : ∀ c, (F c).card ≤ 2)
    (t : ℕ) (h : List (Query (Terminal S G I) C)) :
    t * (fillerHigh π F t h).card ≤ 2 * h.length := by
  calc
    _ = ∑ _u ∈ fillerHigh π F t h, t := by simp [Nat.mul_comm]
    _ ≤ ∑ u ∈ fillerHigh π F t h, (counterLabels π F h u).card := by
      apply Finset.sum_le_sum
      intro u hu
      exact (Finset.mem_filter.mp hu).2
    _ ≤ ∑ u, (counterLabels π F h u).card :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ _ := sum_counterLabels_le π F hcard h

theorem notice_step_charging (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    (analyze π F H D t R (h ++ [q])).noticed \ fillerHigh π F t (h ++ [q]) ⊆
      ((analyze π F H D t R h).noticed \ fillerHigh π F t h) ∪
        directUnitNotices π F H D t R h q ∪ directDegreeNotices π F H D t R h q := by
  classical
  let s := analyze π F H D t R h
  intro u hu
  obtain ⟨huN, huF⟩ := Finset.mem_sdiff.mp hu
  have old (huo : u ∈ s.noticed) :
      u ∈ (s.noticed \ fillerHigh π F t h) ∪ directUnitNotices π F H D t R h q ∪
        directDegreeNotices π F H D t R h q :=
    Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨huo, fun hh => huF (fillerHigh_mono_append π F t h q hh)⟩))
  rw [analyze_append] at huN
  change u ∈ (advance π F H D t R h s q).noticed at huN
  by_cases hn : s.stop = none
  · by_cases hl : Lucky π H s.exposed q
    · exact old (by simpa only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte] using huN)
    · have hnew : (advance π F H D t R h s q).noticed =
          (addNotices (relabel π F) (relabel π H) s
            (noticeOrder (noticeCandidates π F H D t h q s.exposed))).noticed := by
        simp only [advance, hn, ne_eq, not_true_eq_false, hl, ↓reduceIte]
      rw [hnew] at huN
      have hsub := addNotices_new_subset (relabel π F) (relabel π H) s
        (noticeOrder (noticeCandidates π F H D t h q s.exposed)) huN
      rcases Finset.mem_union.mp hsub with huold | huc
      · exact old huold
      · have huc' : u ∈ noticeCandidates π F H D t h q s.exposed := by simpa using huc
        have hreason := (Finset.mem_filter.mp huc').2.2.2
        have hnotF : ¬t ≤ (counterLabels π F (h ++ [q]) u).card := by
          intro hh
          exact huF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        rcases hreason with hunit | hdegree | hcounter
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          change u ∈ (if s.stop = none ∧ ¬Lucky π H s.exposed q then
            (noticeCandidates π F H D t h q s.exposed).filter (UnitAt π F H h q) else ∅)
          rw [if_pos ⟨hn, hl⟩]
          exact Finset.mem_filter.mpr ⟨huc', hunit⟩
        · apply Finset.mem_union_right
          change u ∈ (if s.stop = none ∧ ¬Lucky π H s.exposed q then
            (noticeCandidates π F H D t h q s.exposed).filter
              (fun u => D ≤ degree (h ++ [q]) u) else ∅)
          rw [if_pos ⟨hn, hl⟩]
          exact Finset.mem_filter.mpr ⟨huc', hdegree⟩
        · exact False.elim (hnotF hcounter)
  · exact old (by simpa only [advance, hn, ne_eq, not_false_eq_true, ↓reduceIte] using huN)

theorem noticed_charging (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ)
    (h : List (Query (Terminal S G I) C)) :
    (((analyze π F H D t R h).noticed \ fillerHigh π F t h).card : ℝ) ≤
      historyCharge (fun h q => ((directUnitNotices π F H D t R h q).card : ℝ) +
        (directDegreeNotices π F H D t R h q).card) h := by
  induction h using List.reverseRecOn with
  | nil => simp [Book.initial]
  | append_singleton h q ih =>
      have hh := Finset.card_le_card (notice_step_charging π F H D t R h q)
      have hu := Finset.card_union_le
        ((analyze π F H D t R h).noticed \ fillerHigh π F t h ∪
          directUnitNotices π F H D t R h q) (directDegreeNotices π F H D t R h q)
      have hu' := Finset.card_union_le
        ((analyze π F H D t R h).noticed \ fillerHigh π F t h)
        (directUnitNotices π F H D t R h q)
      have hb : (((analyze π F H D t R (h ++ [q])).noticed \
          fillerHigh π F t (h ++ [q])).card : ℝ) ≤
        ((analyze π F H D t R h).noticed \ fillerHigh π F t h).card +
          (directUnitNotices π F H D t R h q).card +
            (directDegreeNotices π F H D t R h q).card := by
        exact_mod_cast (show _ ≤ _ by omega)
      rw [historyCharge_append]
      linarith

theorem directDegree_subset_crossings (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (D t R : ℕ) (hD : 0 < D) (ht : 0 < t)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C) :
    directDegreeNotices π F H D t R h q ⊆ degreeCrossings D h q := by
  classical
  intro u hu
  dsimp only [directDegreeNotices] at hu
  split_ifs at hu with hg
  · obtain ⟨hc, hd⟩ := Finset.mem_filter.mp hu
    have hcs := (Finset.mem_filter.mp hc).2
    have hb := thresholds_before_stop π F H D t R hD ht h hg.1 u hcs.1 hcs.2.1
    exact (mem_degreeCrossings D h q u).mpr ⟨hb.2.1, hd⟩
  · simp at hu

end Screening

end SteinerLowerBound

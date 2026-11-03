module

public import SteinerLowerBound.Simulation.Agreement

@[expose] public section

namespace SteinerLowerBound.Simulation.Public

open scoped Classical
open HardDistribution
open MetricComparison.Public

variable {S G I C Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem run_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (D t R : ℕ) (algorithm : DecisionTree (Query (Terminal S G I) C) Reply Z)
    (h : List (Query (Terminal S G I) C)) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s)
    (hc : s.cache.Consistent (bits d H))
    (hm : Corresponds s (actualBook π d F H D t R h))
    (hfinal : (actualBook π d F H D t R
      (h ++ Screening.questions (onlineRun (actualAnswer π d F H) algorithm h).2)).stop = none) :
    let r := (run π d F D t R algorithm h s).output (bits d H)
    r.result = (onlineRun (actualAnswer π d F H) algorithm h).1 ∧
      r.transcript = (onlineRun (actualAnswer π d F H) algorithm h).2 ∧
      Corresponds r.state (actualBook π d F H D t R
        (h ++ Screening.questions (onlineRun (actualAnswer π d F H) algorithm h).2)) := by
  classical
  induction algorithm generalizing h s with
  | leaf z =>
      refine ⟨rfl, rfl, ?_⟩
      simpa only [run, DecisionTree.output, onlineRun, Screening.questions,
        List.map_nil, List.append_nil] using hm
  | query q next ih =>
      let a := actualAnswer π d F H h q
      let tail := onlineRun (actualAnswer π d F H) (next a) (h ++ [q])
      have hfull : (actualBook π d F H D t R
          ((h ++ [q]) ++ Screening.questions tail.2)).stop = none := by
        simpa only [onlineRun, Screening.questions, List.map_cons,
          List.singleton_append, List.append_assoc, a, tail] using hfinal
      have hnnext := actualBook_prefix_none π d F H D t R (h ++ [q])
        (Screening.questions tail.2) hfull
      have hadv : (Screening.advance π (internalFillers F) (internalStars d H) D t R h
          (actualBook π d F H D t R h) q).stop = none := by
        simpa only [actualBook, Screening.analyze_append] using hnnext
      obtain ⟨hnold, hlucky, _, _⟩ :=
        Screening.advance_none π (internalFillers F) (internalStars d H)
          D t R h (actualBook π d F H D t R h) q hadv
      have hcontacts : Screening.ContactsExposed π (internalFillers F) (internalStars d H)
          h s.exposed := by
        rw [hm.2.2]
        exact Screening.analyze_contacts π (internalFillers F) (internalStars d H)
          D t R (internalSupport_supported _) (internalSupport_supported _) h hnold
      have he : answer π d F s.cache h q = a :=
        answer_actual π d F H ha R s hs hc hm.1 h q hcontacts (hm.2.2.symm ▸ hlucky)
      let l := Screening.noticeOrder (Screening.noticeCandidates π (internalFillers F)
        (internalStars d H) D t h q (actualBook π d F H D t R h).exposed)
      let b' := Screening.addNotices (fillers π F) (stars π d H)
        (actualBook π d F H D t R h) l
      have hdata := advance_none_data π d F H D t R h
        (actualBook π d F H D t R h) q hadv
      have hN : b'.noticed.card ≤ R := hdata.2.2.1
      have hQ : b'.exposed.card ≤ 2 * R := hdata.2.2.2
      let s' := (noticeList (access π d F) (support π d) R l s).output (bits d H)
      have hm' := noticeList_actual π d F H ha R l s
        (actualBook π d F H D t R h) hs hc hm hN hQ
      have hsp := noticeList_spec (access π d F) (support π d) (access_mono π d F) R l s hs
      have hs' := Spec.output _ _ _ _ hsp (bits d H)
      have hc' := Spec.consistent _ _ _ _ hsp (bits d H) hc
      have hmatch : Corresponds s' (actualBook π d F H D t R (h ++ [q])) := by
        refine ⟨hm'.1, ?_, ?_⟩
        · rw [actualBook, Screening.analyze_append]
          exact hm'.2.1.trans hdata.1.symm
        · rw [actualBook, Screening.analyze_append]
          exact hm'.2.2.trans hdata.2.1.symm
      have hitail := ih a (h ++ [q]) s' hs' hc' hmatch hfull
      have hnots : notices π F D t h q a s.exposed =
          Screening.noticeCandidates π (internalFillers F) (internalStars d H)
            D t h q (actualBook π d F H D t R h).exposed := by
        rw [hm.2.2]
        exact notices_actual π F (internalStars d H) D t h q _
      rw [run, if_neg (by simp [hm.1])]
      dsimp only
      rw [he, hnots, output_bind, output_bind]
      refine ⟨hitail.1, congrArg (List.cons (q, a)) hitail.2.1, ?_⟩
      simpa only [DecisionTree.output, onlineRun, Screening.questions, List.map_cons,
        List.singleton_append, List.append_assoc, a, tail, s', l] using hitail.2.2

theorem tree_actual (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (hn : (actualBook π d F H D t R
      (Screening.questions (onlineRun (actualAnswer π d F H)
        (mapQuestions orient algorithm) []).2)).stop = none) :
    let r := (tree π d F D t R algorithm).output (bits d H)
    r.result = (gatedRun π (fun c => fillerNeighbors (F c))
      (fun c => (H c).elim ∅ Subtype.val) algorithm []).1 ∧
      r.transcript.map (fun qa => (encode qa.1, qa.2)) =
        (gatedRun π (fun c => fillerNeighbors (F c))
          (fun c => (H c).elim ∅ Subtype.val) algorithm []).2 := by
  have hr := run_actual π d F H ha D t R (mapQuestions orient algorithm) [] .initial
    (initial_stable _ _ R (access_empty π d F)) (Cache.empty_consistent (bits d H))
    (by simp [Corresponds, actualBook, Screening.analyze_nil, State.initial, Screening.Book.initial])
    (by simpa only [List.nil_append] using hn)
  have ho := onlineRun_mapQuestions orient (actualAnswer π d F H) algorithm []
  simp only [List.map_nil] at ho
  have hanswer : (fun h q => actualAnswer π d F H (h.map orient) (orient q)) =
      gatedAnswer π (fun c => fillerNeighbors (F c)) (fun c => (H c).elim ∅ Subtype.val) := rfl
  rw [hanswer] at ho
  refine ⟨hr.1.trans (congrArg Prod.fst ho), ?_⟩
  rw [tree, hr.2.1]
  have he := congrArg (fun p => p.2.map (fun qa => (encode qa.1, qa.2))) ho
  simpa only [List.map_map, Function.comp_def, encode_orient, Prod.mk.eta,
    List.map_id', gatedRun] using he

end SteinerLowerBound.Simulation.Public

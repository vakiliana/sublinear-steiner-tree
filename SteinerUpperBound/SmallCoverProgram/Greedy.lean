module

public import SteinerUpperBound.SmallCoverProgram.BoolArrays
public import SteinerUpperBound.SetSystem.Greedy

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {M Q : Type*} {n g : ℕ}

structure GreedyState (g : ℕ) where
  claimed : Vector Bool g
  u : ℕ
  f : ℕ

def rowSets (rows : Vector (Vector Bool g) n) (v : Fin n) : Finset (Fin g) :=
  bits (rows.get v)

def eligible (rows : Vector (Vector Bool g) n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 3 ≤ (rowSets rows v).card)

theorem mem_eligible (rows : Vector (Vector Bool g) n) (v : Fin n) :
    v ∈ eligible rows ↔ 3 ≤ (rowSets rows v).card := by simp [eligible]

def commit (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) :
    Code M Q (GreedyState g) :=
  if 3 ≤ c.1 ∧ 2 ≤ c.2 then
    (claim row s.claimed).bind (fun mask => .tick 2 (.pure ⟨mask, s.u + c.2, s.f + 1⟩))
  else .pure s

def commitRun (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) : Outcome (GreedyState g) :=
  if 3 ≤ c.1 ∧ 2 ≤ c.2 then
    (claimRun row s.claimed).combine
      ((Outcome.pure ⟨(claimRun row s.claimed).value, s.u + c.2, s.f + 1⟩).add 3 0 0 0)
  else .pure s

def greedyStep (rows : Vector (Vector Bool g) n) (s : GreedyState g) (v : Fin n) :
    Code M Q (GreedyState g) :=
  .tick 0 ((counts (rows.get v) s.claimed).bind
    (fun c => .tick 3 (commit (rows.get v) s c)))

def greedyStepRun (rows : Vector (Vector Bool g) n) (s : GreedyState g) (v : Fin n) :
    Outcome (GreedyState g) :=
  ((countsRun (rows.get v) s.claimed).combine
    ((commitRun (rows.get v) s (countsRun (rows.get v) s.claimed).value).add 4 0 0 0)).add 1 0 0 0

def greedy (rows : Vector (Vector Bool g) n) : Code M Q (GreedyState g) :=
  (allocate g false).bind (fun mask =>
    .tick 0 (Code.foldList (greedyStep rows) (List.finRange n) ⟨mask, 0, 0⟩))

def greedyRun (rows : Vector (Vector Bool g) n) : Outcome (GreedyState g) :=
  (allocated g false).combine
    ((Code.folded (greedyStepRun rows) (List.finRange n) ⟨Vector.replicate g false, 0, 0⟩).add 1 0 0 0)

def stateScore (s : GreedyState g) : ℝ := (s.u : ℝ) - s.f

def greedyScore (rows : Vector (Vector Bool g) n) : Code M Q ℝ :=
  (greedy rows).bind (fun s => .tick 2 (.pure (stateScore s)))

def greedyScoreRun (rows : Vector (Vector Bool g) n) : Outcome ℝ :=
  (greedyRun rows).combine ((Outcome.pure (stateScore (greedyRun rows).value)).add 3 0 0 0)

theorem commit_evaluates (m : M → ℝ) (b : Q → Bool)
    (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) :
    Code.Evaluates m b (commit row s c) (commitRun row s c) := by
  unfold commit commitRun
  split_ifs
  · exact Code.Evaluates.bind m b _ _ _ _ (claim_evaluates m b row s.claimed)
      (Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 2)
  · exact Code.evaluates_pure m b s

theorem greedyStep_evaluates (m : M → ℝ) (b : Q → Bool)
    (rows : Vector (Vector Bool g) n) (s : GreedyState g) (v : Fin n) :
    Code.Evaluates m b (greedyStep rows s v) (greedyStepRun rows s v) :=
  Code.Evaluates.tick m b _ _
    (Code.Evaluates.bind m b _ _ _ _ (counts_evaluates m b _ _)
      (Code.Evaluates.tick m b _ _ (commit_evaluates m b _ _ _) 3)) 0

theorem greedy_evaluates (m : M → ℝ) (b : Q → Bool) (rows : Vector (Vector Bool g) n) :
    Code.Evaluates m b (greedy rows) (greedyRun rows) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (Code.Evaluates.tick m b _ _
      (Code.foldList_evaluates m b _ _ (greedyStep_evaluates m b rows) _ _) 0)

theorem greedyScore_evaluates (m : M → ℝ) (b : Q → Bool) (rows : Vector (Vector Bool g) n) :
    Code.Evaluates m b (greedyScore rows) (greedyScoreRun rows) :=
  Code.Evaluates.bind m b _ _ _ _ (greedy_evaluates m b rows)
    (Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 2)

def Matches (rows : Vector (Vector Bool g) n) (s : GreedyState g) (S : Finset (Fin n)) : Prop :=
  bits s.claimed = SetSystem.claimed (rowSets rows) Finset.univ S ∧
    s.u = (SetSystem.claimed (rowSets rows) Finset.univ S).card ∧ s.f = S.card

noncomputable def nextFamily (rows : Vector (Vector Bool g) n)
    (S : Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  letI : DecidableEq (Fin g) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  exact if v ∈ eligible rows ∧
      2 ≤ (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card
    then insert v S else S

noncomputable def eligibleOrder (rows : Vector (Vector Bool g) n) (l : List (Fin n)) :
    List (Fin n) := by
  letI : DecidableEq (Fin n) := Classical.decEq _
  exact l.filter (fun v => v ∈ eligible rows)

theorem card_union_fresh {U : Type*} (C B : Finset U) :
    (C ∪ B).card = C.card + (B \ C).card := by
  classical
  have he : C ∪ B = C ∪ (B \ C) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [he, Finset.card_union_of_disjoint
    (Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp hy).2 hx))]

theorem greedyStep_matches (rows : Vector (Vector Bool g) n) (s : GreedyState g)
    (S : Finset (Fin n)) (hs : Matches rows s S) (v : Fin n) :
    Matches rows (greedyStepRun rows s v).value (nextFamily rows S v) := by
  classical
  let : DecidableEq (Fin g) := Classical.decEq _
  let : DecidableEq (Fin n) := Classical.decEq _
  have hc : (countsRun (rows.get v) s.claimed).value =
      ((rowSets rows v).card,
        (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card) := by
    rw [countsRun_value, hs.1]
    congr 1
    apply congrArg Finset.card
    ext j
    simp only [Finset.mem_sdiff, rowSets]
  change Matches rows (commitRun (rows.get v) s (countsRun (rows.get v) s.claimed).value).value _
  rw [hc]
  have he : (v ∈ eligible rows ∧
      2 ≤ (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card) ↔
      (3 ≤ (rowSets rows v).card ∧
        2 ≤ (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card) := by
    rw [mem_eligible]
  unfold nextFamily
  simp only [he]
  unfold commitRun
  split_ifs with h
  · have hv : v ∉ S := by
      intro hv
      have hrow : rowSets rows v ⊆ SetSystem.claimed (rowSets rows) Finset.univ S := by
        simpa only [Finset.univ_inter] using SetSystem.claimed_contains_row (rowSets rows) Finset.univ hv
      have hz := Finset.sdiff_eq_empty_iff_subset.mpr hrow
      rw [hz, Finset.card_empty] at h
      omega
    have hclaim : SetSystem.claimed (rowSets rows) Finset.univ (insert v S) =
        SetSystem.claimed (rowSets rows) Finset.univ S ∪ rowSets rows v := by
      ext j
      simp only [SetSystem.claimed, Finset.univ_inter, Finset.biUnion_insert,
        Finset.mem_union]
      tauto
    refine ⟨?_, ?_, ?_⟩
    · change bits (claimRun (rows.get v) s.claimed).value = _
      rw [claimRun_bits, hs.1, hclaim]
      ext j
      simp only [Finset.mem_union, rowSets]
    · change s.u + (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card = _
      rw [hs.2.1, hclaim, card_union_fresh]
    · change s.f + 1 = (insert v S).card
      rw [hs.2.2, Finset.card_insert_of_notMem hv]
  · exact hs

theorem greedyFold_matches (rows : Vector (Vector Bool g) n)
    (l : List (Fin n)) (s : GreedyState g) (S : Finset (Fin n)) (hs : Matches rows s S) :
    Matches rows (Code.folded (greedyStepRun rows) l s).value
      (SetSystem.smallCoverAux (rowSets rows) Finset.univ (eligibleOrder rows l) S) := by
  classical
  let : DecidableEq (Fin g) := Classical.decEq _
  let : DecidableEq (Fin n) := Classical.decEq _
  induction l generalizing s S with
  | nil => exact hs
  | cons v l ih =>
      have hh := greedyStep_matches rows s S hs v
      have ht := ih _ _ hh
      have he :
          SetSystem.smallCoverAux (rowSets rows) Finset.univ
            (eligibleOrder rows (v :: l)) S =
          SetSystem.smallCoverAux (rowSets rows) Finset.univ
            (eligibleOrder rows l) (nextFamily rows S v) := by
        by_cases hv : v ∈ eligible rows <;>
          by_cases hf : 2 ≤ (rowSets rows v \ SetSystem.claimed (rowSets rows) Finset.univ S).card <;>
          simp [eligibleOrder, SetSystem.smallCoverAux, nextFamily, hv, hf, Finset.univ_inter]
      rw [he]
      exact ht

theorem greedyRun_matches (rows : Vector (Vector Bool g) n) :
    Matches rows (greedyRun rows).value
      (SetSystem.smallCover (eligible rows) (rowSets rows) Finset.univ (List.finRange n)) := by
  change Matches rows
    (Code.folded (greedyStepRun rows) (List.finRange n) ⟨Vector.replicate g false, 0, 0⟩).value
    (SetSystem.smallCoverAux (rowSets rows) Finset.univ (eligibleOrder rows (List.finRange n)) ∅)
  apply greedyFold_matches
  simp [Matches, bits, SetSystem.claimed]

theorem greedyScoreRun_value (rows : Vector (Vector Bool g) n) :
    (greedyScoreRun rows).value =
      SetSystem.smallCoverEstimate (eligible rows) (rowSets rows) Finset.univ (List.finRange n) := by
  have hh := greedyRun_matches rows
  change stateScore (greedyRun rows).value = _
  unfold stateScore SetSystem.smallCoverEstimate
  rw [hh.2.1, hh.2.2]

theorem greedyScoreRun_guarantee (rows : Vector (Vector Bool g) n) :
    0 ≤ (greedyScoreRun rows).value ∧
      (greedyScoreRun rows).value ≤ SetSystem.saving (eligible rows) (rowSets rows) Finset.univ ∧
      SetSystem.saving (eligible rows) (rowSets rows) Finset.univ / 2 ≤ (greedyScoreRun rows).value := by
  rw [greedyScoreRun_value]
  exact SetSystem.smallCover_guarantee _ _ _ _
    (by intro v _; simp)

theorem commitRun_work (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) :
    (commitRun row s c).work ≤ 6 * g + 3 := by
  unfold commitRun
  split_ifs
  · have hh := claimRun_work row s.claimed
    dsimp only [Outcome.combine, Outcome.add, Outcome.pure]
    omega
  · simp [Outcome.pure]

theorem greedyStepRun_work (rows : Vector (Vector Bool g) n) (s : GreedyState g) (v : Fin n) :
    (greedyStepRun rows s v).work ≤ 15 * g + 8 := by
  have hc := countsRun_work (rows.get v) s.claimed
  have hk := commitRun_work (rows.get v) s (countsRun (rows.get v) s.claimed).value
  dsimp only [greedyStepRun, Outcome.add, Outcome.combine]
  omega

theorem greedyScoreRun_work (rows : Vector (Vector Bool g) n) :
    (greedyScoreRun rows).work ≤ (15 * g + 9) * n + g + 5 := by
  have hh := Code.folded_work (greedyStepRun rows) (15 * g + 8)
    (greedyStepRun_work rows) (List.finRange n) ⟨Vector.replicate g false, 0, 0⟩
  simp only [List.length_finRange] at hh
  dsimp only [greedyScoreRun, greedyRun, Outcome.combine, Outcome.add, Outcome.pure, allocated]
  nlinarith

theorem commitRun_resources (row : Vector Bool g) (s : GreedyState g) (c : ℕ × ℕ) :
    (commitRun row s c).metricQueries = 0 ∧ (commitRun row s c).retentionQueries = 0 ∧
      (commitRun row s c).positiveReplies = 0 := by
  unfold commitRun
  split_ifs
  · have hh := claimRun_resources row s.claimed
    simpa only [Outcome.combine, Outcome.add, Outcome.pure, Nat.add_zero, Nat.zero_add] using hh
  · exact ⟨rfl, rfl, rfl⟩

theorem greedyStepRun_resources (rows : Vector (Vector Bool g) n) (s : GreedyState g) (v : Fin n) :
    (greedyStepRun rows s v).metricQueries = 0 ∧
      (greedyStepRun rows s v).retentionQueries = 0 ∧
      (greedyStepRun rows s v).positiveReplies = 0 := by
  have hc := countsRun_resources (rows.get v) s.claimed
  have hk := commitRun_resources (rows.get v) s (countsRun (rows.get v) s.claimed).value
  simp only [greedyStepRun, Outcome.add, Outcome.combine, hc, hk, Nat.zero_add, and_self]

theorem greedyScoreRun_resources (rows : Vector (Vector Bool g) n) :
    (greedyScoreRun rows).metricQueries = 0 ∧ (greedyScoreRun rows).retentionQueries = 0 ∧
      (greedyScoreRun rows).positiveReplies = 0 := by
  let init : GreedyState g := ⟨Vector.replicate g false, 0, 0⟩
  have hm := Code.folded_metric_queries (greedyStepRun rows) 0
    (fun s v => (greedyStepRun_resources rows s v).1.le) (List.finRange n) init
  have hr := folded_retention_zero (greedyStepRun rows)
    (fun s v => (greedyStepRun_resources rows s v).2.1) (List.finRange n) init
  have hp := folded_positive_zero (greedyStepRun rows)
    (fun s v => (greedyStepRun_resources rows s v).2.2) (List.finRange n) init
  dsimp only [greedyScoreRun, greedyRun, Outcome.combine, Outcome.add, Outcome.pure, allocated]
  simp only [Nat.zero_add, Nat.add_zero]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.SmallCoverProgram

module

public import SteinerUpperBound.SmallCoverProgram.Geometry

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram Covers.Geometry
open scoped Classical

variable {Q : Type*} {n g : ℕ}

/-- The only private observations are the `g*n` metric replies. -/
noncomputable def programVector (N : Vector (Fin n) g) (a : ℝ) :
    Code (Sym2 (Fin n)) Q ℝ :=
  if g = 0 then .pure 0 else
    (metricTable N).bind (fun d =>
      (adjacencyTable N d a).bind (fun adj =>
        (Closure.closure adj).bind (fun connected =>
          (Closure.roots connected).bind (fun roots =>
            (rowTable d roots (5 * a / 8)).bind greedyScore))))

noncomputable def runVector (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) : Outcome ℝ :=
  if g = 0 then .pure 0 else
    let d := metricTableRun m N
    let adj := adjacencyTableRun N d.value a
    let connected := Closure.computed adj.value
    let roots := Closure.rootsRun connected.value
    let rows := rowTableRun d.value roots.value (5 * a / 8)
    d.combine (adj.combine (connected.combine (roots.combine
      (rows.combine (greedyScoreRun rows.value)))))

theorem programVector_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : Vector (Fin n) g) (a : ℝ) :
    Code.Evaluates m b (programVector N a) (runVector m N a) := by
  unfold programVector runVector
  split_ifs
  · exact Code.evaluates_pure m b _
  · exact Code.Evaluates.bind m b _ _ _ _ (metricTable_evaluates m b N)
      (Code.Evaluates.bind m b _ _ _ _ (adjacencyTable_evaluates m b N _ a)
        (Code.Evaluates.bind m b _ _ _ _ (Closure.closure_evaluates m b _)
          (Code.Evaluates.bind m b _ _ _ _ (Closure.roots_evaluates m b _)
            (Code.Evaluates.bind m b _ _ _ _ (rowTable_evaluates m b _ _ _)
              (greedyScore_evaluates m b _)))))

theorem runVector_value (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) (hg : g ≠ 0) :
    (runVector m N a).value = (greedyScoreRun (observedRowTable m N a)).value := by
  simp only [runVector, hg, ↓reduceIte, Outcome.combine]
  rfl

theorem retained_empty (N : Vector (Fin n) 0) : retained N = ∅ := by
  ext x
  rw [mem_retained]
  simp

theorem empty_actual_estimate (I : Instance (Fin n)) (N : Vector (Fin n) 0) (a : ℝ) :
    SetSystem.smallCoverEstimate (eligibleOn I (retained N) a (5 * a / 8))
      (rowOn I (retained N) a (5 * a / 8)) (componentsOn I (retained N) a) (List.finRange n) = 0 := by
  have hcomponents : componentsOn I (retained N) a = ∅ := by simp [retained_empty, componentsOn]
  have hrows : rowOn I (retained N) a (5 * a / 8) = fun _ => ∅ := by
    funext v
    simp [rowOn, hcomponents]
  have heligible : eligibleOn I (retained N) a (5 * a / 8) = ∅ := by
    ext v
    simp [eligibleOn, hrows]
  have hs : SetSystem.smallCover (eligibleOn I (retained N) a (5 * a / 8))
      (rowOn I (retained N) a (5 * a / 8)) (componentsOn I (retained N) a) (List.finRange n) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := SetSystem.smallCover_subset (eligibleOn I (retained N) a (5 * a / 8))
      (rowOn I (retained N) a (5 * a / 8)) (componentsOn I (retained N) a) (List.finRange n) hv
    simp only [heligible, Finset.notMem_empty] at hh
  simp only [SetSystem.smallCoverEstimate, hs, SetSystem.claimed, Finset.biUnion_empty,
    Finset.inter_empty, Finset.card_empty, Nat.cast_zero, sub_zero]

theorem programVector_agrees (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    (runVector I.weight N a).value =
      SetSystem.smallCoverEstimate (eligibleOn I (retained N) a (5 * a / 8))
        (rowOn I (retained N) a (5 * a / 8)) (componentsOn I (retained N) a) (List.finRange n) := by
  by_cases hg : g = 0
  · subst g
    rw [empty_actual_estimate]
    rfl
  · rw [runVector_value I.weight N a hg]
    exact greedy_actual_estimate I N hN a

theorem programVector_guarantee (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    0 ≤ (runVector I.weight N a).value ∧
      (runVector I.weight N a).value ≤ savingOn I (retained N) a (5 * a / 8) ∧
      savingOn I (retained N) a (5 * a / 8) / 2 ≤ (runVector I.weight N a).value := by
  rw [programVector_agrees I N hN a]
  exact SetSystem.smallCover_guarantee _ _ _ _ (by intro v _; simp)

theorem runVector_queries (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) :
    (runVector m N a).metricQueries ≤ n * g := by
  by_cases hg : g = 0
  · simp [runVector, hg, Outcome.pure]
  · have hd := metricTable_queries m N
    have ha := adjacencyTable_resources N (metricTableRun m N).value a
    have hc := Closure.computed_resources (observedAdj m N a)
    have hr := Closure.rootsRun_resources (connectedTable m N a)
    have hw := rowTable_resources (metricTableRun m N).value
      (Closure.rootsRun (connectedTable m N a)).value (5 * a / 8)
    have hz := greedyScoreRun_resources (observedRowTable m N a)
    dsimp only [observedAdj, connectedTable, observedRowTable] at hc hr hw hz
    simpa only [runVector, hg, ↓reduceIte, Outcome.combine,
      ha.1, hc.1, hr.1, hw.1, hz.1, Nat.add_zero, Nat.zero_add, Nat.mul_comm] using hd

theorem runVector_resources (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) :
    (runVector m N a).retentionQueries = 0 ∧ (runVector m N a).positiveReplies = 0 := by
  by_cases hg : g = 0
  · simp [runVector, hg, Outcome.pure]
  · have hd := metricTable_resources m N
    have ha := adjacencyTable_resources N (metricTableRun m N).value a
    have hc := Closure.computed_resources (observedAdj m N a)
    have hr := Closure.rootsRun_resources (connectedTable m N a)
    have hw := rowTable_resources (metricTableRun m N).value
      (Closure.rootsRun (connectedTable m N a)).value (5 * a / 8)
    have hz := greedyScoreRun_resources (observedRowTable m N a)
    dsimp only [observedAdj, connectedTable, observedRowTable] at hc hr hw hz
    simp only [runVector, hg, ↓reduceIte, Outcome.combine,
      hd, ha, hc, hr, hw, hz, Nat.zero_add, and_self]

theorem runVector_work (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    (runVector m N a).work ≤ 64 * (n * g + g ^ 3 * (1 + Nat.log2 (g + 1))) := by
  by_cases hg : g = 0
  · simp [runVector, hg, Outcome.pure]
  · have hg₁ : 1 ≤ g := by omega
    have hgn : g ≤ n := by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective N.get hN
    have hn₁ : 1 ≤ n := by omega
    have hd := metricTable_work m N
    have ha := adjacencyTable_work N (metricTableRun m N).value a
    have hc := Closure.computed_work (observedAdj m N a) hg₁
    have hr := Closure.rootsRun_work (connectedTable m N a)
    have hw := rowTable_work (metricTableRun m N).value
      (Closure.rootsRun (connectedTable m N a)).value (5 * a / 8)
    have hz := greedyScoreRun_work (observedRowTable m N a)
    have hgg : g * g ≤ g ^ 3 := by nlinarith [Nat.mul_le_mul_left (g * g) hg₁]
    have hgp : 1 ≤ g ^ 3 := by nlinarith
    have hni : n ≤ n * g := by nlinarith
    have hgi : g ≤ n * g := by nlinarith
    have hlog : 1 ≤ 1 + Nat.log2 (g + 1) := by omega
    have hcub := Nat.mul_le_mul_left (g ^ 3) hlog
    simp only [runVector, hg, ↓reduceIte, Outcome.combine]
    dsimp only [observedAdj, connectedTable, observedRowTable] at hc hr hw hz
    nlinarith

end SteinerUpperBound.SmallCoverProgram

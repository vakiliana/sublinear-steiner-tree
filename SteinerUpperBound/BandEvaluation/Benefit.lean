module

public import SteinerUpperBound.BandEvaluation.LocalCost
public import SteinerUpperBound.BandStatistic

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n m : ℕ}

noncomputable def clippedEntry (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (i j : Fin m) : ℝ :=
  if C.get i ≠ C.get j ∧ C.get i ∈ Y ∧ C.get j ∈ Y then 0
  else min (max (distanceAt d i (C.get j) - lo) 0) (hi - lo)

noncomputable def clippedCell (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (p : Fin (m * m)) : Code M Q ℝ :=
  let ij := finProdFinEquiv.symm p
  .tick (16 * Y.length + 63) (.pure (clippedEntry C d lo hi Y ij.1 ij.2))

noncomputable def clippedCellRun (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (p : Fin (m * m)) : Outcome ℝ :=
  let ij := finProdFinEquiv.symm p
  ⟨clippedEntry C d lo hi Y ij.1 ij.2, 16 * Y.length + 64, 0, 0, 0⟩

noncomputable def clippedMatrix (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Code M Q (FiniteMST.Matrix m) :=
  (allocate (m * m) (0 : ℝ)).bind (fun init => tabulate (clippedCell C d lo hi Y) init)

noncomputable def clippedMatrixRun (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Outcome (FiniteMST.Matrix m) :=
  (allocated (m * m) (0 : ℝ)).combine
    (tabulated (clippedCellRun C d lo hi Y) (Vector.replicate (m * m) 0))

noncomputable def clippedMST (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Code M Q ℝ :=
  (clippedMatrix C d lo hi Y).bind FiniteMST.program

noncomputable def clippedMSTRun (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Outcome ℝ :=
  (clippedMatrixRun C d lo hi Y).combine (FiniteMST.run (clippedMatrixRun C d lo hi Y).value)

noncomputable def finiteBenefit (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Code M Q ℝ :=
  (clippedMST C d lo hi []).bind (fun base =>
    (clippedMST C d lo hi Y).bind (fun zeroed => .tick 1 (.pure (base - zeroed))))

noncomputable def finiteBenefitRun (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) : Outcome ℝ :=
  let base := clippedMSTRun C d lo hi []
  let zeroed := clippedMSTRun C d lo hi Y
  base.combine (zeroed.combine ((Outcome.pure (base.value - zeroed.value)).add 2 0 0 0))

theorem clippedCell_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (lo hi : ℝ) (Y : List (Fin n)) (p) :
    Code.Evaluates oracle bits (clippedCell C d lo hi Y p) (clippedCellRun C d lo hi Y p) :=
  Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) _

theorem clippedMatrix_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (lo hi : ℝ) (Y : List (Fin n)) :
    Code.Evaluates oracle bits (clippedMatrix C d lo hi Y) (clippedMatrixRun C d lo hi Y) :=
  Code.Evaluates.bind _ _ _ _ _ _ (allocate_evaluates _ _ _ _)
    (tabulate_evaluates _ _ _ _ (clippedCell_evaluates oracle bits C d lo hi Y) _)

theorem clippedMST_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (lo hi : ℝ) (Y : List (Fin n)) :
    Code.Evaluates oracle bits (clippedMST C d lo hi Y) (clippedMSTRun C d lo hi Y) :=
  Code.Evaluates.bind _ _ _ _ _ _ (clippedMatrix_evaluates _ _ _ _ _ _ _)
    (FiniteMST.program_evaluates _ _ _)

theorem finiteBenefit_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (C : Vector (Fin n) m) (d : MetricTable n m) (lo hi : ℝ) (Y : List (Fin n)) :
    Code.Evaluates oracle bits (finiteBenefit C d lo hi Y) (finiteBenefitRun C d lo hi Y) :=
  Code.Evaluates.bind _ _ _ _ _ _ (clippedMST_evaluates _ _ _ _ _ _ _)
    (Code.Evaluates.bind _ _ _ _ _ _ (clippedMST_evaluates _ _ _ _ _ _ _)
      (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 1))

theorem clippedMatrixRun_get (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (i j : Fin m) :
    Closure.entry (clippedMatrixRun C d lo hi Y).value i j = clippedEntry C d lo hi Y i j := by
  change (tabulated (clippedCellRun C d lo hi Y) _).value.get (finProdFinEquiv (i, j)) = _
  rw [tabulated_get]
  simp only [clippedCellRun, Equiv.symm_apply_apply]

theorem clippedMatrixRun_nonneg (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (Y : List (Fin n)) :
    ∀ i j, 0 ≤ Closure.entry (clippedMatrixRun C d lo hi Y).value i j := by
  intro i j
  rw [clippedMatrixRun_get]
  unfold clippedEntry
  split_ifs
  · rfl
  · exact le_min (le_max_right _ _) (sub_nonneg.mpr hlohi)

theorem labels_get_retained (C : Vector (Fin n) m) : FiniteMST.labels C.get = retained C := by
  ext x
  rw [FiniteMST.mem_labels, mem_retained]

theorem clippedMSTRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (Y : List (Fin n)) :
    (clippedMSTRun C d lo hi Y).value =
      TerminalMST.value
        (TerminalMST.zeroed (TerminalMST.clipped I.weight lo hi) (Network.completeOn Y.toFinset))
        (retained C) := by
  have hw := TerminalMST.zeroed_nonneg (TerminalMST.clipped I.weight lo hi)
    (Network.completeOn Y.toFinset) (TerminalMST.clipped_nonneg I.weight lo hi hlohi)
  have he (i j : Fin m) :
      Closure.entry (clippedMatrixRun C d lo hi Y).value i j =
        TerminalMST.zeroed (TerminalMST.clipped I.weight lo hi) (Network.completeOn Y.toFinset)
          (Sym2.mk (C.get i) (C.get j)) := by
    rw [clippedMatrixRun_get]
    simp only [clippedEntry, TerminalMST.zeroed, SimpleGraph.mem_edgeSet,
      Network.completeOn_adj, List.mem_toFinset, TerminalMST.clipped, Instance.weight_mk, hd]
  have hh := FiniteMST.on_labels_correct (clippedMatrixRun C d lo hi Y).value
    (clippedMatrixRun_nonneg C d lo hi hlohi Y) _ hw C.get hC (fun i j _ => he i j)
  simpa only [clippedMSTRun, Outcome.combine, labels_get_retained] using hh

theorem finiteBenefitRun_correct (I : Instance (Fin n)) (C : Vector (Fin n) m)
    (hC : Function.Injective C.get) (d : MetricTable n m)
    (hd : ∀ i v, distanceAt d i v = I.distance (C.get i) v)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (Y : List (Fin n)) (hY : Y.toFinset ⊆ retained C) :
    (finiteBenefitRun C d lo hi Y).value = Band.benefit I (retained C) Y.toFinset lo hi := by
  have hb := clippedMSTRun_correct I C hC d hd lo hi hlohi []
  have hz := clippedMSTRun_correct I C hC d hd lo hi hlohi Y
  have hempty : Network.completeOn (∅ : Finset (Fin n)) = ⊥ := by
    ext x y
    simp [Network.completeOn_adj]
  simp only [List.toFinset_nil, hempty, TerminalMST.zeroed_bot] at hb
  change (clippedMSTRun C d lo hi []).value - (clippedMSTRun C d lo hi Y).value = _
  rw [hb, hz, Band.benefit_eq_finiteMST I (retained C) Y.toFinset hY lo hi hlohi]

theorem clippedMatrixRun_work (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    (clippedMatrixRun C d lo hi Y).work ≤ (16 * Y.length + 67) * (m * m) + 1 := by
  have hh := tabulated_work (clippedCellRun C d lo hi Y) (Vector.replicate (m * m) 0)
    (16 * Y.length + 64) (fun _ => le_rfl)
  dsimp only [clippedMatrixRun, allocated, Outcome.combine]
  nlinarith

theorem clippedMSTRun_work (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (hY : Y.length ≤ 4) :
    (clippedMSTRun C d lo hi Y).work ≤ 2000 * (m + 1) ^ 7 := by
  have hm := clippedMatrixRun_work C d lo hi Y
  have hk := finite_work_poly (clippedMatrixRun C d lo hi Y).value
  have hcoef : 16 * Y.length + 67 ≤ 131 := by omega
  have hmul := Nat.mul_le_mul_right (m * m) hcoef
  have hp : m * m ≤ (m + 1) ^ 7 := by
    have hbase : m * m ≤ (m + 1) ^ 2 := by nlinarith
    exact hbase.trans (pow_le_pow_right₀ (by omega : 1 ≤ m + 1) (by omega : 2 ≤ 7))
  have h1 : 1 ≤ (m + 1) ^ 7 := by
    have hp : 0 < (m + 1) ^ 7 := by positivity
    omega
  dsimp only [clippedMSTRun, Outcome.combine]
  nlinarith

theorem finiteBenefitRun_work (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) (hY : Y.length ≤ 4) :
    (finiteBenefitRun C d lo hi Y).work ≤ 5000 * (m + 1) ^ 7 := by
  have hb := clippedMSTRun_work C d lo hi [] (by simp)
  have hz := clippedMSTRun_work C d lo hi Y hY
  have h1 : 1 ≤ (m + 1) ^ 7 := by
    have hp : 0 < (m + 1) ^ 7 := by positivity
    omega
  dsimp only [finiteBenefitRun, Outcome.combine, Outcome.add, Outcome.pure]
  omega

theorem clippedMatrixRun_resources (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    (clippedMatrixRun C d lo hi Y).metricQueries = 0 ∧
      (clippedMatrixRun C d lo hi Y).retentionQueries = 0 ∧
      (clippedMatrixRun C d lo hi Y).positiveReplies = 0 := by
  have hm := tabulated_metricQueries (clippedCellRun C d lo hi Y) (Vector.replicate (m * m) 0) 0
    (fun _ => le_rfl)
  have hr := tabulated_retention_zero (clippedCellRun C d lo hi Y) (Vector.replicate (m * m) 0) (fun _ => rfl)
  have hp := tabulated_positive_zero (clippedCellRun C d lo hi Y) (Vector.replicate (m * m) 0) (fun _ => rfl)
  dsimp only [clippedMatrixRun, allocated, Outcome.combine]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

theorem clippedMSTRun_resources (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    (clippedMSTRun C d lo hi Y).metricQueries = 0 ∧
      (clippedMSTRun C d lo hi Y).retentionQueries = 0 ∧
      (clippedMSTRun C d lo hi Y).positiveReplies = 0 := by
  have hm := clippedMatrixRun_resources C d lo hi Y
  have hk := FiniteMST.run_resources (clippedMatrixRun C d lo hi Y).value
  simp only [clippedMSTRun, Outcome.combine, hm, hk, Nat.zero_add, and_self]

theorem finiteBenefitRun_resources (C : Vector (Fin n) m) (d : MetricTable n m)
    (lo hi : ℝ) (Y : List (Fin n)) :
    (finiteBenefitRun C d lo hi Y).metricQueries = 0 ∧
      (finiteBenefitRun C d lo hi Y).retentionQueries = 0 ∧
      (finiteBenefitRun C d lo hi Y).positiveReplies = 0 := by
  have hb := clippedMSTRun_resources C d lo hi []
  have hz := clippedMSTRun_resources C d lo hi Y
  simp only [finiteBenefitRun, Outcome.combine, Outcome.add, Outcome.pure, hb, hz, Nat.zero_add, and_self]

end SteinerUpperBound.BandEvaluation

module

public import SteinerUpperBound.SmallCoverProgram.Closure

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {Q : Type*} {n g : ℕ}

abbrev MetricTable (n g : ℕ) := Vector ℝ (g * n)

def distanceAt (d : MetricTable n g) (i : Fin g) (v : Fin n) : ℝ :=
  d.get (finProdFinEquiv (i, v))

def metricCell (N : Vector (Fin n) g) (p : Fin (g * n)) :
    Code (Sym2 (Fin n)) Q ℝ :=
  let iv := finProdFinEquiv.symm p
  .tick 3 (.metric (Sym2.mk (N.get iv.1) iv.2) .pure)

def metricCellRun (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (p : Fin (g * n)) :
    Outcome ℝ :=
  let iv := finProdFinEquiv.symm p
  ⟨m (Sym2.mk (N.get iv.1) iv.2), 5, 1, 0, 0⟩

def metricTable (N : Vector (Fin n) g) : Code (Sym2 (Fin n)) Q (MetricTable n g) :=
  (allocate (g * n) (0 : ℝ)).bind (fun init => tabulate (metricCell N) init)

def metricTableRun (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) : Outcome (MetricTable n g) :=
  (allocated (g * n) (0 : ℝ)).combine
    (tabulated (metricCellRun m N) (Vector.replicate (g * n) 0))

noncomputable def adjacencyCell (N : Vector (Fin n) g) (d : MetricTable n g)
    (a : ℝ) (p : Fin (g * g)) : Code (Sym2 (Fin n)) Q Bool :=
  let xy := finProdFinEquiv.symm p
  .tick 11 (.pure (decide (xy.1 ≠ xy.2) && decide (distanceAt d xy.1 (N.get xy.2) < a)))

noncomputable def adjacencyCellRun (N : Vector (Fin n) g) (d : MetricTable n g)
    (a : ℝ) (p : Fin (g * g)) : Outcome Bool :=
  let xy := finProdFinEquiv.symm p
  ⟨decide (xy.1 ≠ xy.2) && decide (distanceAt d xy.1 (N.get xy.2) < a), 12, 0, 0, 0⟩

noncomputable def adjacencyTable (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    Code (Sym2 (Fin n)) Q (Closure.Dense Bool g) :=
  (allocate (g * g) false).bind (fun init => tabulate (adjacencyCell N d a) init)

noncomputable def adjacencyTableRun (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    Outcome (Closure.Dense Bool g) :=
  (allocated (g * g) false).combine
    (tabulated (adjacencyCellRun N d a) (Vector.replicate (g * g) false))

theorem metricCell_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : Vector (Fin n) g) (p) :
    Code.Evaluates m b (metricCell N p) (metricCellRun m N p) :=
  Code.Evaluates.tick m b _ _ (Code.evaluates_metric m b _) 3

theorem metricTable_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool) (N : Vector (Fin n) g) :
    Code.Evaluates m b (metricTable N) (metricTableRun m N) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (tabulate_evaluates m b _ _ (metricCell_evaluates m b N) _)

theorem adjacencyCell_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) (p) :
    Code.Evaluates m b (adjacencyCell N d a p) (adjacencyCellRun N d a p) :=
  Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 11

theorem adjacencyTable_evaluates (m : Sym2 (Fin n) → ℝ) (b : Q → Bool)
    (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    Code.Evaluates m b (adjacencyTable N d a) (adjacencyTableRun N d a) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (tabulate_evaluates m b _ _ (adjacencyCell_evaluates m b N d a) _)

theorem metricTable_get (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (i : Fin g) (v : Fin n) :
    distanceAt (metricTableRun m N).value i v = m (Sym2.mk (N.get i) v) := by
  change (tabulated (metricCellRun m N) _).value.get (finProdFinEquiv (i, v)) = _
  rw [tabulated_get]
  simp only [metricCellRun, Equiv.symm_apply_apply]

theorem adjacencyTable_get (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ)
    (x y : Fin g) :
    Closure.entry (adjacencyTableRun N d a).value x y = true ↔
      x ≠ y ∧ distanceAt d x (N.get y) < a := by
  change (tabulated (adjacencyCellRun N d a) _).value.get (finProdFinEquiv (x, y)) = true ↔ _
  rw [tabulated_get]
  simp [adjacencyCellRun]

theorem metricTable_work (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) :
    (metricTableRun m N).work ≤ 8 * (g * n) + 1 := by
  have hh := tabulated_work (metricCellRun m N) (Vector.replicate (g * n) 0) 5 (fun _ => le_rfl)
  dsimp only [metricTableRun, Outcome.combine, allocated]
  omega

theorem metricTable_queries (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) :
    (metricTableRun m N).metricQueries ≤ g * n := by
  have hh := tabulated_metricQueries (metricCellRun m N) (Vector.replicate (g * n) 0) 1
    (fun _ => le_rfl)
  simpa only [metricTableRun, Outcome.combine, allocated, Nat.zero_add, Nat.one_mul] using hh

theorem metricTable_resources (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) :
    (metricTableRun m N).retentionQueries = 0 ∧ (metricTableRun m N).positiveReplies = 0 := by
  have hr := tabulated_retention_zero (metricCellRun m N) (Vector.replicate (g * n) 0) (fun _ => rfl)
  have hp := tabulated_positive_zero (metricCellRun m N) (Vector.replicate (g * n) 0) (fun _ => rfl)
  simpa only [metricTableRun, Outcome.combine, allocated, Nat.zero_add] using And.intro hr hp

theorem adjacencyTable_work (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    (adjacencyTableRun N d a).work ≤ 15 * (g * g) + 1 := by
  have hh := tabulated_work (adjacencyCellRun N d a) (Vector.replicate (g * g) false) 12
    (fun _ => le_rfl)
  dsimp only [adjacencyTableRun, Outcome.combine, allocated]
  omega

theorem adjacencyTable_resources (N : Vector (Fin n) g) (d : MetricTable n g) (a : ℝ) :
    (adjacencyTableRun N d a).metricQueries = 0 ∧
      (adjacencyTableRun N d a).retentionQueries = 0 ∧
      (adjacencyTableRun N d a).positiveReplies = 0 := by
  have hm := tabulated_metricQueries (adjacencyCellRun N d a) (Vector.replicate (g * g) false) 0
    (fun _ => le_rfl)
  have hr := tabulated_retention_zero (adjacencyCellRun N d a) (Vector.replicate (g * g) false)
    (fun _ => rfl)
  have hp := tabulated_positive_zero (adjacencyCellRun N d a) (Vector.replicate (g * g) false)
    (fun _ => rfl)
  dsimp only [adjacencyTableRun, Outcome.combine, allocated]
  simp only [Nat.zero_add]
  exact ⟨by simpa only [Nat.zero_mul, Nat.le_zero] using hm, hr, hp⟩

end SteinerUpperBound.SmallCoverProgram

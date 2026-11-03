module

public import SteinerUpperBound.SmallCoverProgram.Closure.Basic

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SmallCoverProgram.Closure

open QueryProgram
open scoped Classical

variable {M Q : Type*} {g : ℕ}

def startCell (a : Dense Bool g) (p : Fin (g * g)) : Code M Q Bool :=
  .tick 7 (.pure (let xy := finProdFinEquiv.symm p
    decide (xy.1 = xy.2) || entry a xy.1 xy.2))

def startCellRun (a : Dense Bool g) (p : Fin (g * g)) : Outcome Bool :=
  ⟨(let xy := finProdFinEquiv.symm p
    decide (xy.1 = xy.2) || entry a xy.1 xy.2), 8, 0, 0, 0⟩

def initial (a : Dense Bool g) : Code M Q (Dense Bool g) :=
  (allocate (g * g) false).bind (fun init => tabulate (startCell a) init)

def initialRun (a : Dense Bool g) : Outcome (Dense Bool g) :=
  (allocated (g * g) false).combine
    (tabulated (startCellRun a) (Vector.replicate (g * g) false))

def scanCell (a : Dense Bool g) (x y : Fin g) (found : Bool) (z : Fin g) : Code M Q Bool :=
  .tick 7 (.pure (found || (entry a x z && entry a z y)))

def scanCellRun (a : Dense Bool g) (x y : Fin g) (found : Bool) (z : Fin g) : Outcome Bool :=
  ⟨found || (entry a x z && entry a z y), 8, 0, 0, 0⟩

def squareCell (a : Dense Bool g) (p : Fin (g * g)) : Code M Q Bool :=
  let xy := finProdFinEquiv.symm p
  .tick 5 (Code.foldList (scanCell a xy.1 xy.2) (List.finRange g) (entry a xy.1 xy.2))

def squareCellRun (a : Dense Bool g) (p : Fin (g * g)) : Outcome Bool :=
  let xy := finProdFinEquiv.symm p
  (Code.folded (scanCellRun a xy.1 xy.2) (List.finRange g) (entry a xy.1 xy.2)).add 6 0 0 0

def square (a : Dense Bool g) : Code M Q (Dense Bool g) :=
  (allocate (g * g) false).bind (fun init => tabulate (squareCell a) init)

def squareRun (a : Dense Bool g) : Outcome (Dense Bool g) :=
  (allocated (g * g) false).combine
    (tabulated (squareCellRun a) (Vector.replicate (g * g) false))

def iterate : ℕ → Dense Bool g → Code M Q (Dense Bool g)
  | 0, a => .pure a
  | r + 1, a => .tick 0 ((square a).bind (iterate r))

def iterated : ℕ → Dense Bool g → Outcome (Dense Bool g)
  | 0, a => .pure a
  | r + 1, a => ((squareRun a).combine (iterated r (squareRun a).value)).add 1 0 0 0

def closure (a : Dense Bool g) : Code M Q (Dense Bool g) :=
  (initial a).bind (iterate (rounds g))

def computed (a : Dense Bool g) : Outcome (Dense Bool g) :=
  (initialRun a).combine (iterated (rounds g) (initialRun a).value)

theorem startCell_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) (p) :
    Code.Evaluates m b (startCell a p) (startCellRun a p) :=
  Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 7

theorem initial_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) :
    Code.Evaluates m b (initial a) (initialRun a) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (tabulate_evaluates m b _ _ (startCell_evaluates m b a) _)

theorem scanCell_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g)
    (x y : Fin g) (found : Bool) (z : Fin g) :
    Code.Evaluates m b (scanCell a x y found z) (scanCellRun a x y found z) :=
  Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 7

theorem squareCell_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) (p) :
    Code.Evaluates m b (squareCell a p) (squareCellRun a p) :=
  Code.Evaluates.tick m b _ _
    (Code.foldList_evaluates m b _ _ (scanCell_evaluates m b a _ _) _ _) 5

theorem square_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) :
    Code.Evaluates m b (square a) (squareRun a) :=
  Code.Evaluates.bind m b _ _ _ _ (allocate_evaluates m b _ _)
    (tabulate_evaluates m b _ _ (squareCell_evaluates m b a) _)

theorem iterate_evaluates (m : M → ℝ) (b : Q → Bool) (r : ℕ) (a : Dense Bool g) :
    Code.Evaluates m b (iterate r a) (iterated r a) := by
  induction r generalizing a with
  | zero => exact Code.evaluates_pure _ _ _
  | succ r ih =>
      exact Code.Evaluates.tick m b _ _
        (Code.Evaluates.bind m b _ _ _ _ (square_evaluates m b a) (ih _)) 0

theorem closure_evaluates (m : M → ℝ) (b : Q → Bool) (a : Dense Bool g) :
    Code.Evaluates m b (closure a) (computed a) :=
  Code.Evaluates.bind m b _ _ _ _ (initial_evaluates m b a) (iterate_evaluates m b _ _)

theorem initial_get (a : Dense Bool g) (x y : Fin g) :
    entry (initialRun a).value x y = true ↔ Bounded a 0 x y := by
  change (tabulated (startCellRun a) _).value.get (finProdFinEquiv (x, y)) = true ↔ _
  rw [tabulated_get]
  simp [startCellRun, Bounded]

theorem squareCell_value (a : Dense Bool g) (x y : Fin g) :
    (squareCellRun a (finProdFinEquiv (x, y))).value = true ↔
      entry a x y = true ∨ ∃ z, entry a x z = true ∧ entry a z y = true := by
  simp only [squareCellRun, Equiv.symm_apply_apply, Outcome.add]
  rw [folded_value]
  change (List.finRange g).foldl (fun found z => found || (entry a x z && entry a z y))
    (entry a x y) = true ↔ _
  rw [fold_or_true]
  simp only [List.mem_finRange, true_and, Bool.and_eq_true]

theorem square_get (a : Dense Bool g) (x y : Fin g) :
    entry (squareRun a).value x y = true ↔
      entry a x y = true ∨ ∃ z, entry a x z = true ∧ entry a z y = true := by
  change (tabulated (squareCellRun a) _).value.get (finProdFinEquiv (x, y)) = true ↔ _
  rw [tabulated_get]
  exact squareCell_value a x y

theorem iterate_get (a t : Dense Bool g) (k : ℕ)
    (ht : ∀ x y, entry t x y = true ↔ Bounded a k x y) :
    ∀ r x y, entry (iterated r t).value x y = true ↔ Bounded a (k + r) x y := by
  intro r
  induction r generalizing t k with
  | zero => simpa only [iterated, Outcome.pure, Nat.add_zero] using ht
  | succ r ih =>
      intro x y
      have hs : ∀ u v, entry (squareRun t).value u v = true ↔ Bounded a (k + 1) u v := by
        intro u v
        rw [square_get]
        simp only [ht, Bounded]
      have hh := ih (squareRun t).value (k + 1) hs x y
      simpa only [iterated, Outcome.add, Outcome.combine, Nat.add_assoc,
        Nat.add_comm 1 r] using hh

theorem computed_correct {G : SimpleGraph (Fin g)} (a : Dense Bool g)
    (hAdj : ∀ x y, entry a x y = true ↔ G.Adj x y) (x y : Fin g) :
    entry (computed a).value x y = true ↔ G.Reachable x y := by
  have hh := iterate_get a (initialRun a).value 0 (initial_get a) (rounds g) x y
  simpa only [computed, Outcome.combine, Nat.zero_add,
    bounded_iff_reachable a G hAdj x y] using hh

theorem initial_work (a : Dense Bool g) : (initialRun a).work ≤ 11 * (g * g) + 1 := by
  have hh := tabulated_work (startCellRun a) (Vector.replicate (g * g) false) 8 (fun _ => le_rfl)
  dsimp only [initialRun, Outcome.combine, allocated]
  omega

theorem squareCell_work (a : Dense Bool g) (p) : (squareCellRun a p).work ≤ 9 * g + 6 := by
  have hh := Code.folded_work
    (scanCellRun a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) 8 (fun _ _ => le_rfl)
    (List.finRange g) (entry a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
  simp only [List.length_finRange] at hh
  dsimp only [squareCellRun, Outcome.add]
  omega

theorem square_work (a : Dense Bool g) : (squareRun a).work ≤ (9 * g + 9) * (g * g) + 1 := by
  have hh := tabulated_work (squareCellRun a) (Vector.replicate (g * g) false)
    (9 * g + 6) (squareCell_work a)
  dsimp only [squareRun, Outcome.combine, allocated]
  nlinarith

theorem iterate_work (r : ℕ) (a : Dense Bool g) :
    (iterated r a).work ≤ r * ((9 * g + 9) * (g * g) + 2) := by
  induction r generalizing a with
  | zero => simp [iterated, Outcome.pure]
  | succ r ih =>
      have hs := square_work a
      have ht := ih (squareRun a).value
      dsimp only [iterated, Outcome.add, Outcome.combine]
      nlinarith

theorem computed_work (a : Dense Bool g) (hg : 1 ≤ g) :
    (computed a).work ≤ 32 * g ^ 3 * (1 + Nat.log2 (g + 1)) := by
  have hi := initial_work a
  have ht := iterate_work (rounds g) (initialRun a).value
  have hg2 : g * g ≤ g ^ 3 := by
    nlinarith [Nat.mul_le_mul_left (g * g) hg]
  have hg3 : 1 ≤ g ^ 3 := by nlinarith
  have hstep : (9 * g + 9) * (g * g) + 2 ≤ 20 * g ^ 3 := by nlinarith
  have hh := Nat.mul_le_mul_left (rounds g) hstep
  have hr : 1 ≤ rounds g := by simp [rounds]
  have hbase := Nat.mul_le_mul_right (12 * g ^ 3) hr
  dsimp only [computed, Outcome.combine, rounds]
  dsimp only [rounds] at ht hh hr hbase
  nlinarith

theorem initial_resources (a : Dense Bool g) :
    (initialRun a).metricQueries = 0 ∧ (initialRun a).retentionQueries = 0 ∧
      (initialRun a).positiveReplies = 0 := by
  have hm := tabulated_metricQueries (startCellRun a) (Vector.replicate (g * g) false) 0
    (fun _ => le_rfl)
  have hr := tabulated_retention_zero (startCellRun a) (Vector.replicate (g * g) false) (fun _ => rfl)
  have hp := tabulated_positive_zero (startCellRun a) (Vector.replicate (g * g) false) (fun _ => rfl)
  simp only [Nat.zero_mul] at hm
  dsimp only [initialRun, Outcome.combine, allocated]
  simp only [Nat.zero_add]
  exact ⟨by omega, hr, hp⟩

theorem squareCell_resources (a : Dense Bool g) (p) :
    (squareCellRun a p).metricQueries = 0 ∧ (squareCellRun a p).retentionQueries = 0 ∧
      (squareCellRun a p).positiveReplies = 0 := by
  have hm := Code.folded_metric_queries
    (scanCellRun a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) 0 (fun _ _ => le_rfl)
    (List.finRange g) (entry a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
  have hr := folded_retention_zero
    (scanCellRun a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) (fun _ _ => rfl)
    (List.finRange g) (entry a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
  have hp := folded_positive_zero
    (scanCellRun a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) (fun _ _ => rfl)
    (List.finRange g) (entry a (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
  simp only [Nat.zero_mul] at hm
  dsimp only [squareCellRun, Outcome.add]
  simp only [Nat.zero_add]
  exact ⟨by omega, hr, hp⟩

theorem square_resources (a : Dense Bool g) :
    (squareRun a).metricQueries = 0 ∧ (squareRun a).retentionQueries = 0 ∧
      (squareRun a).positiveReplies = 0 := by
  have hm := tabulated_metricQueries (squareCellRun a) (Vector.replicate (g * g) false) 0
    (fun p => (squareCell_resources a p).1.le)
  have hr := tabulated_retention_zero (squareCellRun a) (Vector.replicate (g * g) false)
    (fun p => (squareCell_resources a p).2.1)
  have hp := tabulated_positive_zero (squareCellRun a) (Vector.replicate (g * g) false)
    (fun p => (squareCell_resources a p).2.2)
  simp only [Nat.zero_mul] at hm
  dsimp only [squareRun, Outcome.combine, allocated]
  simp only [Nat.zero_add]
  exact ⟨by omega, hr, hp⟩

theorem iterate_resources (r : ℕ) (a : Dense Bool g) :
    (iterated r a).metricQueries = 0 ∧ (iterated r a).retentionQueries = 0 ∧
      (iterated r a).positiveReplies = 0 := by
  induction r generalizing a with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ r ih =>
      have hs := square_resources a
      have ht := ih (squareRun a).value
      simp only [iterated, Outcome.add, Outcome.combine, hs, ht, Nat.zero_add, and_self]

theorem computed_resources (a : Dense Bool g) :
    (computed a).metricQueries = 0 ∧ (computed a).retentionQueries = 0 ∧
      (computed a).positiveReplies = 0 := by
  have hi := initial_resources a
  have ht := iterate_resources (rounds g) (initialRun a).value
  simp only [computed, Outcome.combine, hi, ht, Nat.zero_add, and_self]

end SteinerUpperBound.SmallCoverProgram.Closure

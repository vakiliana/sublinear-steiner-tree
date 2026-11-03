module

public import SteinerUpperBound.RuntimeWorld
public import SteinerUpperBound.EstimatorMST
public import SteinerUpperBound.BandEstimator
public import SteinerUpperBound.EstimatorLoop.Records

@[expose] public section

noncomputable section

namespace SteinerUpperBound.EstimatorFrontend

open QueryProgram MSTApproximation RuntimeGrids
open scoped Classical

variable {n k : ℕ}

abbrev Index (t : Tables) := Fin (t.coarse.intervals + 1)

abbrev Saving (n k : ℕ) (t : Tables) :=
  Index t → Cache (RuntimeWorld.Coordinate t k) →
    Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k)
      (Option (ℝ × Cache (RuntimeWorld.Coordinate t k)))

def savingRound (t : Tables) (saving : Saving n k t) :
    EstimatorLoop.Step (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Index t) :=
  fun i c => (saving i c).map (fun r => r.map (fun zc => (zc.1, 0, zc.2)))

variable {M Q : Type*}

def totalStep (g : Grid) (total : ℝ) (r : EstimatorLoop.ScaleRecord (Fin (g.intervals + 1))) :
    Code M Q ℝ :=
  (BandEstimator.scaleProgram g r.index.val).bind (fun a =>
    .tick 2 (.pure (total + a * r.saving)))

def totalStepResult (g : Grid) (total : ℝ) (r : EstimatorLoop.ScaleRecord (Fin (g.intervals + 1))) :
    Outcome ℝ :=
  ⟨total + g.scale r.index.val * r.saving, 2 * r.index.val + 6, 0, 0, 0⟩

theorem totalStep_evaluates (m : M → ℝ) (bits : Q → Bool) (g : Grid) (total : ℝ)
    (r : EstimatorLoop.ScaleRecord (Fin (g.intervals + 1))) :
    Code.Evaluates m bits (totalStep g total r) (totalStepResult g total r) := by
  intro F
  rw [totalStep, Code.evaluate_bind, BandEstimator.scale_evaluates]
  simp only [Code.evaluate, BandEstimator.scaleResult, Outcome.combine, Outcome.add,
    Outcome.pure, totalStepResult, Nat.add_zero]

def totals (g : Grid) (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) :
    Code M Q ℝ :=
  Code.foldList (totalStep g) records 0

def summed (g : Grid) (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) :
    Outcome ℝ :=
  Code.folded (totalStepResult g) records 0

theorem totals_evaluates (m : M → ℝ) (bits : Q → Bool) (g : Grid)
    (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) :
    Code.Evaluates m bits (totals g records) (summed g records) :=
  Code.foldList_evaluates m bits _ _ (fun s r => totalStep_evaluates m bits g s r) _ _

theorem folded_value (g : Grid) (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1))))
    (start : ℝ) :
    (Code.folded (totalStepResult g) records start).value =
      start + (records.map (fun r => g.scale r.index.val * r.saving)).sum := by
  induction records generalizing start with
  | nil => simp [Code.folded, Outcome.pure]
  | cons r l ih =>
      simpa only [Code.folded, Outcome.add, Outcome.combine, totalStepResult,
        List.map_cons, List.sum_cons, add_assoc] using ih (start + g.scale r.index.val * r.saving)

theorem totals_value (g : Grid) (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) :
    (summed g records).value = (records.map (fun r => g.scale r.index.val * r.saving)).sum := by
  simpa only [summed, zero_add] using folded_value g records 0

theorem totals_work (g : Grid) (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) :
    (summed g records).work ≤ (2 * g.intervals + 7) * records.length := by
  have h := Code.folded_work (totalStepResult g) (2 * g.intervals + 6)
    (fun s r => by dsimp only [totalStepResult]; have hi := r.index.isLt; omega) records 0
  exact h

def finish (t : Tables) (upper That : ℝ)
    (saved : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k)) :
    Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ) :=
  (totals t.coarse saved.records).bind (fun S =>
    .tick 5 (.pure (some (Estimation.output upper S That EstimatorParameters.QS EstimatorParameters.QQ))))

def afterSaving (p : EstimatorParameters.PublicParameters)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (upper : ℝ) :
    Option (EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k)) →
      Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ)
  | none => .tick 0 (.pure none)
  | some saved =>
      (BandEstimator.fromParameters t.coarse label.get
        (fun i => RuntimeWorld.coarseKey t inverse i.val) root label.toList p saved.cache).bind (fun band =>
          .tick 1 (match band.1 with
            | none => .pure none
            | some That => finish t upper That saved))

def afterMST (p : EstimatorParameters.PublicParameters)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t)
    (mst : MSTApproximation.IntervalAnswer (RuntimeWorld.Coordinate t k)) :
    Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ) :=
  .tick (4 * (t.coarse.intervals + 1) + 3)
    ((EstimatorLoop.rounds (savingRound t saving) (List.finRange (t.coarse.intervals + 1))
      ⟨mst.cache, []⟩).bind (afterSaving p label root t inverse mst.upper))

def program (p : EstimatorParameters.PublicParameters)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t)
    (cache : Cache (RuntimeWorld.Coordinate t k)) :
    Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ) :=
  (EstimatorMST.withParameters p label.get (RuntimeWorld.fineKey t inverse)
    t.fine label.toList root cache).bind (afterMST p label root t inverse saving)

end SteinerUpperBound.EstimatorFrontend

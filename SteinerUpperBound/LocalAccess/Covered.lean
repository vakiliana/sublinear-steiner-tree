module

public import SteinerUpperBound.LocalAccess.Reveal

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {Q : Type*} {n : ℕ}

noncomputable def coveredProgram (r : ℝ) (centers : List (Fin n)) :
    Code (Sym2 (Fin n)) Q (Vector Bool n) :=
  (SmallCoverProgram.allocate n false).bind (fun init =>
    SmallCoverProgram.tabulate (fun v => nearProgram r v centers) init)

noncomputable def coveredResult (w : Sym2 (Fin n) → ℝ) (r : ℝ)
    (centers : List (Fin n)) : Outcome (Vector Bool n) :=
  (SmallCoverProgram.allocated n false).combine
    (SmallCoverProgram.tabulated (fun v => nearResult w r v centers) (Vector.replicate n false))

theorem covered_evaluates (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (r : ℝ)
    (centers : List (Fin n)) :
    Code.Evaluates w b (coveredProgram r centers) (coveredResult w r centers) :=
  Code.Evaluates.bind w b _ _ _ _ (SmallCoverProgram.allocate_evaluates w b _ _)
    (SmallCoverProgram.tabulate_evaluates w b _ _ (fun v => near_evaluates w b r v centers) _)

theorem covered_get (w : Sym2 (Fin n) → ℝ) (r : ℝ) (centers : List (Fin n)) (x : Fin n) :
    (coveredResult w r centers).value.get x = true ↔
      ∃ v ∈ centers, w (Sym2.mk v x) ≤ r := by
  change (SmallCoverProgram.tabulated _ _).value.get x = true ↔ _
  rw [SmallCoverProgram.tabulated_get, near_value]
  simp only [Sym2.eq_swap]

theorem covered_queries (w : Sym2 (Fin n) → ℝ) (r : ℝ) (centers : List (Fin n)) :
    (coveredResult w r centers).metricQueries ≤ n * centers.length := by
  have h := SmallCoverProgram.tabulated_metricQueries (fun v : Fin n => nearResult w r v centers)
    (Vector.replicate n false) centers.length (fun v => near_queries w r v centers)
  simpa only [coveredResult, SmallCoverProgram.allocated, Outcome.combine, Nat.zero_add,
    Nat.mul_comm] using h

theorem covered_work (w : Sym2 (Fin n) → ℝ) (r : ℝ) (centers : List (Fin n)) :
    (coveredResult w r centers).work ≤ (2 * centers.length + 4) * n + 1 := by
  have h := SmallCoverProgram.tabulated_work (fun v : Fin n => nearResult w r v centers)
    (Vector.replicate n false) (2 * centers.length + 1) (fun v => near_work w r v centers)
  dsimp only [coveredResult, SmallCoverProgram.allocated, Outcome.combine]
  nlinarith

theorem covered_counters (w : Sym2 (Fin n) → ℝ) (r : ℝ) (centers : List (Fin n)) :
    (coveredResult w r centers).retentionQueries = 0 ∧
      (coveredResult w r centers).positiveReplies = 0 := by
  have hr := SmallCoverProgram.tabulated_retention_zero
    (fun v : Fin n => nearResult w r v centers) (Vector.replicate n false)
    (fun v => (near_counters w r v centers).1)
  have hp := SmallCoverProgram.tabulated_positive_zero
    (fun v : Fin n => nearResult w r v centers) (Vector.replicate n false)
    (fun v => (near_counters w r v centers).2)
  simpa only [coveredResult, SmallCoverProgram.allocated, Outcome.combine, Nat.zero_add] using
    And.intro hr hp

end SteinerUpperBound.LocalAccess

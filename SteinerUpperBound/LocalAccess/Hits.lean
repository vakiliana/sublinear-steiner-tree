module

public import SteinerUpperBound.LocalAccess.Index

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {Q : Type*} {n : ℕ}

def hitsProgram (D : Vector Bool n) : List (Fin n) → Code (Sym2 (Fin n)) Q Bool
  | [] => .tick 0 (.pure false)
  | x :: l => .tick 1 (if D.get x then .pure true else hitsProgram D l)

def hitsResult (D : Vector Bool n) : List (Fin n) → Outcome Bool
  | [] => (Outcome.pure false).add 1 0 0 0
  | x :: l => (if D.get x then Outcome.pure true else hitsResult D l).add 2 0 0 0

theorem hits_evaluates (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (l : List (Fin n)) :
    Code.Evaluates w bits (hitsProgram D l) (hitsResult D l) := by
  induction l with
  | nil => intro F; rfl
  | cons x l ih =>
      intro F
      cases hd : D.get x with
      | false =>
          simpa only [hitsProgram, hitsResult, hd, Bool.false_eq_true, ite_false, Code.evaluate] using
            ih (fun o => F (o.add 2 0 0 0))
      | true => simp only [hitsProgram, hitsResult, hd, ite_true, Code.evaluate]

theorem hits_value (D : Vector Bool n) (l : List (Fin n)) :
    (hitsResult D l).value = true ↔ ∃ x ∈ l, D.get x = true := by
  induction l with
  | nil => simp [hitsResult, Outcome.add, Outcome.pure]
  | cons x l ih =>
      cases hd : D.get x <;> simp [hitsResult, hd, Outcome.add, Outcome.pure, ih]

theorem hits_work (D : Vector Bool n) (l : List (Fin n)) :
    (hitsResult D l).work ≤ 2 * l.length + 1 := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih =>
      cases hd : D.get x <;>
        simp only [hitsResult, hd, Bool.false_eq_true, ite_false, ite_true, Outcome.add,
          Outcome.pure, List.length_cons] <;> omega

theorem hits_counters (D : Vector Bool n) (l : List (Fin n)) :
    (hitsResult D l).metricQueries = 0 ∧ (hitsResult D l).retentionQueries = 0 ∧
      (hitsResult D l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
      cases hd : D.get x <;> simp [hitsResult, hd, Outcome.add, Outcome.pure, ih]

end SteinerUpperBound.LocalAccess

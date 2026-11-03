module

public import SteinerUpperBound.QueryProgram

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V Q : Type*}

noncomputable def nearProgram (r : ℝ) (v : V) : List V → Code (Sym2 V) Q Bool
  | [] => .tick 0 (.pure false)
  | x :: l => .metric (Sym2.mk v x) (fun d =>
      .tick 0 (if d ≤ r then .pure true else nearProgram r v l))

noncomputable def nearResult (w : Sym2 V → ℝ) (r : ℝ) (v : V) : List V → Outcome Bool
  | [] => (Outcome.pure false).add 1 0 0 0
  | x :: l =>
      ((if w (Sym2.mk v x) ≤ r then Outcome.pure true else nearResult w r v l).add 1 0 0 0).add
        1 1 0 0

theorem near_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (r : ℝ) (v : V) (l : List V) :
    Code.Evaluates w b (nearProgram r v l) (nearResult w r v l) := by
  induction l with
  | nil => intro F; rfl
  | cons x l ih =>
      intro F
      by_cases h : w (Sym2.mk v x) ≤ r
      · simp only [nearProgram, nearResult, Code.evaluate, h, ite_true]
      · simpa only [nearProgram, nearResult, Code.evaluate, h, ite_false] using
          ih (fun o => F ((o.add 1 0 0 0).add 1 1 0 0))

theorem near_value (w : Sym2 V → ℝ) (r : ℝ) (v : V) (l : List V) :
    (nearResult w r v l).value = true ↔ ∃ x ∈ l, w (Sym2.mk v x) ≤ r := by
  induction l with
  | nil => simp [nearResult, Outcome.add, Outcome.pure]
  | cons x l ih =>
      by_cases h : w (Sym2.mk v x) ≤ r
      · simp [nearResult, h, Outcome.add, Outcome.pure]
      · simp [nearResult, h, Outcome.add, ih]

theorem near_work (w : Sym2 V → ℝ) (r : ℝ) (v : V) (l : List V) :
    (nearResult w r v l).work ≤ 2 * l.length + 1 := by
  induction l with
  | nil => simp [nearResult, Outcome.add, Outcome.pure]
  | cons x l ih =>
      by_cases h : w (Sym2.mk v x) ≤ r <;>
        simp only [nearResult, h, ite_true, ite_false, Outcome.add, Outcome.pure,
          List.length_cons] <;> omega

theorem near_queries (w : Sym2 V → ℝ) (r : ℝ) (v : V) (l : List V) :
    (nearResult w r v l).metricQueries ≤ l.length := by
  induction l with
  | nil => simp [nearResult, Outcome.add, Outcome.pure]
  | cons x l ih =>
      by_cases h : w (Sym2.mk v x) ≤ r <;>
        simp only [nearResult, h, ite_true, ite_false, Outcome.add, Outcome.pure,
          List.length_cons] <;> omega

theorem near_counters (w : Sym2 V → ℝ) (r : ℝ) (v : V) (l : List V) :
    (nearResult w r v l).retentionQueries = 0 ∧
      (nearResult w r v l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x l ih =>
      by_cases h : w (Sym2.mk v x) ≤ r <;>
        simp only [nearResult, h, ite_true, ite_false, Outcome.add, Outcome.pure,
          Nat.zero_add] <;> simp_all

end SteinerUpperBound.LocalAccess

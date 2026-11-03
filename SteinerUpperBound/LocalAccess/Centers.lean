module

public import SteinerUpperBound.LocalAccess.Near

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V Q : Type*}

noncomputable def centersProgram (r : ℝ) (points : List V) :
    ℕ → List V → Code (Sym2 V) Q (List V)
  | 0, _ => .tick 0 (.pure [])
  | _ + 1, [] => .tick 0 (.pure [])
  | cap + 1, v :: l =>
      .tick 0 ((nearProgram r v points).bind (fun h =>
        .tick 0 (if h then
          (centersProgram r points cap l).bind (fun vs => .tick 0 (.pure (v :: vs)))
        else centersProgram r points (cap + 1) l)))

noncomputable def centersResult (w : Sym2 V → ℝ) (r : ℝ) (points : List V) :
    ℕ → List V → Outcome (List V)
  | 0, _ => (Outcome.pure []).add 1 0 0 0
  | _ + 1, [] => (Outcome.pure []).add 1 0 0 0
  | cap + 1, v :: l =>
      let n := nearResult w r v points
      let tail := if n.value then
          ((centersResult w r points cap l).map (List.cons v)).add 1 0 0 0
        else centersResult w r points (cap + 1) l
      (n.combine (tail.add 1 0 0 0)).add 1 0 0 0

theorem centers_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (r : ℝ)
    (points : List V) (cap : ℕ) (vertices : List V) :
    Code.Evaluates w b (centersProgram r points cap vertices)
      (centersResult w r points cap vertices) := by
  induction vertices generalizing cap with
  | nil => cases cap <;> intro F <;> rfl
  | cons v l ih =>
      cases cap with
      | zero => intro F; rfl
      | succ cap =>
          intro F
          simp only [centersProgram, centersResult, Code.evaluate, Code.evaluate_bind]
          rw [near_evaluates w b r v points]
          cases hn : (nearResult w r v points).value <;>
            simp only [hn, Bool.false_eq_true, ite_false, ite_true, Code.evaluate]
          · rw [ih]
          · rw [Code.evaluate_bind, ih]
            simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, Outcome.map,
              Nat.zero_add, Nat.add_zero, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem centers_value (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (cap : ℕ) (vertices : List V) :
    (centersResult w r points cap vertices).value =
      (vertices.filter (fun v => (nearResult w r v points).value)).take cap := by
  induction vertices generalizing cap with
  | nil => cases cap <;> rfl
  | cons v l ih =>
      cases cap with
      | zero => rfl
      | succ cap =>
          cases hn : (nearResult w r v points).value <;>
            simp [centersResult, hn, Outcome.add, Outcome.combine, Outcome.map, ih]

theorem centers_length (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (cap : ℕ) (vertices : List V) :
    (centersResult w r points cap vertices).value.length ≤ cap := by
  rw [centers_value]
  exact List.length_take_le _ _

theorem centers_work (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (cap : ℕ) (vertices : List V) :
    (centersResult w r points cap vertices).work ≤
      (2 * points.length + 5) * (vertices.length + 1) := by
  induction vertices generalizing cap with
  | nil => cases cap <;> simp [centersResult, Outcome.add, Outcome.pure]
  | cons v l ih =>
      cases cap with
      | zero =>
          simp only [centersResult, Outcome.add, Outcome.pure, List.length_cons]
          nlinarith [Nat.zero_le (points.length * l.length)]
      | succ cap =>
          have hn := near_work w r v points
          have h₀ := ih cap
          have h₁ := ih (cap + 1)
          cases hb : (nearResult w r v points).value <;>
            simp only [centersResult, hb, Bool.false_eq_true, ite_false, ite_true,
              Outcome.add, Outcome.combine, Outcome.map, List.length_cons] <;> nlinarith

theorem centers_queries (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (cap : ℕ) (vertices : List V) :
    (centersResult w r points cap vertices).metricQueries ≤ vertices.length * points.length := by
  induction vertices generalizing cap with
  | nil => cases cap <;> simp [centersResult, Outcome.add, Outcome.pure]
  | cons v l ih =>
      cases cap with
      | zero => simp [centersResult, Outcome.add, Outcome.pure]
      | succ cap =>
          have hn := near_queries w r v points
          have h₀ := ih cap
          have h₁ := ih (cap + 1)
          cases hb : (nearResult w r v points).value <;>
            simp only [centersResult, hb, Bool.false_eq_true, ite_false, ite_true,
              Outcome.add, Outcome.combine, Outcome.map, List.length_cons] <;> nlinarith

theorem centers_counters (w : Sym2 V → ℝ) (r : ℝ) (points : List V)
    (cap : ℕ) (vertices : List V) :
    (centersResult w r points cap vertices).retentionQueries = 0 ∧
      (centersResult w r points cap vertices).positiveReplies = 0 := by
  induction vertices generalizing cap with
  | nil => cases cap <;> exact ⟨rfl, rfl⟩
  | cons v l ih =>
      cases cap with
      | zero => exact ⟨rfl, rfl⟩
      | succ cap =>
          have hn := near_counters w r v points
          have h₀ := ih cap
          have h₁ := ih (cap + 1)
          cases hb : (nearResult w r v points).value <;>
            simp only [centersResult, hb, Bool.false_eq_true, ite_false, ite_true,
              Outcome.add, Outcome.combine, Outcome.map, hn.1, hn.2, h₀.1, h₀.2, h₁.1, h₁.2,
              Nat.zero_add] <;> simp

end SteinerUpperBound.LocalAccess

module

public import SteinerUpperBound.LocalAccess.Canonical

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V M Q : Type*}

structure Revealed (V Q : Type*) where
  points : List V
  cache : Cache Q

noncomputable def revealProgram (key : V → Q) : List V → Cache Q → Code M Q (Revealed V Q)
  | [], c => .tick 0 (.pure ⟨[], c⟩)
  | x :: l, c =>
      .tick 0 ((Cache.resolve (key x) c).bind (fun r =>
        .tick 0 ((revealProgram key l r.2).bind (fun rest =>
          .tick 0 (.pure ⟨if r.1 then x :: rest.points else rest.points, rest.cache⟩)))))

noncomputable def revealResult (b : Q → Bool) (key : V → Q) :
    List V → Cache Q → Outcome (Revealed V Q)
  | [], c => (Outcome.pure ⟨[], c⟩).add 1 0 0 0
  | x :: l, c =>
      let r := Cache.resolved b (key x) c
      let tail := revealResult b key l r.value.2
      let output : Outcome (Revealed V Q) :=
        (tail.map (fun out => ⟨if r.value.1 then x :: out.points else out.points, out.cache⟩)).add
          1 0 0 0
      (r.combine (output.add 1 0 0 0)).add 1 0 0 0

theorem reveal_evaluates (m : M → ℝ) (b : Q → Bool) (key : V → Q) (l : List V) (c : Cache Q) :
    Code.Evaluates m b (revealProgram key l c) (revealResult b key l c) := by
  induction l generalizing c with
  | nil => intro F; rfl
  | cons x l ih =>
      intro F
      simp only [revealProgram, revealResult, Code.evaluate, Code.evaluate_bind]
      rw [Cache.resolve_evaluates m b (key x) c, ih]
      simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, Outcome.map,
        Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem reveal_correct (b : Q → Bool) (key : V → Q) (l : List V) (c : Cache Q)
    (hc : Cache.Correct b c) :
    (revealResult b key l c).value.points = l.filter (fun x => b (key x)) ∧
      Cache.Correct b (revealResult b key l c).value.cache := by
  induction l generalizing c with
  | nil => exact ⟨rfl, hc⟩
  | cons x l ih =>
      have hr := Cache.resolved_correct b (key x) c hc
      have ht := ih _ hr.2
      simp only [revealResult, Outcome.add, Outcome.combine, Outcome.map, hr.1, ht.1]
      cases hb : b (key x) <;> simpa [hb] using ht.2

theorem reveal_work (b : Q → Bool) (key : V → Q) (l : List V) (c : Cache Q) :
    (revealResult b key l c).work ≤ 7 * l.length + 1 := by
  induction l generalizing c with
  | nil => exact le_rfl
  | cons x l ih =>
      have hr := Cache.resolved_work_le b (key x) c
      have ht := ih (Cache.resolved b (key x) c).value.2
      simp only [revealResult, Outcome.add, Outcome.combine, Outcome.map, List.length_cons]
      omega

theorem reveal_metric_queries (b : Q → Bool) (key : V → Q) (l : List V) (c : Cache Q) :
    (revealResult b key l c).metricQueries = 0 := by
  induction l generalizing c with
  | nil => rfl
  | cons x l ih =>
      have hr : (Cache.resolved b (key x) c).metricQueries = 0 := by
        cases h : c (key x) <;> simp only [Cache.resolved, h]
      simp only [revealResult, Outcome.add, Outcome.combine, Outcome.map, ih, hr,
        Nat.zero_add]

theorem reveal_positive (b : Q → Bool) (key : V → Q) (l : List V) (c : Cache Q) :
    (revealResult b key l c).positiveReplies ≤ (revealResult b key l c).value.points.length := by
  induction l generalizing c with
  | nil => exact le_rfl
  | cons x l ih =>
      have hr := ComponentExplore.resolved_positive_bit b (key x) c
      have ht := ih (Cache.resolved b (key x) c).value.2
      cases hb : (Cache.resolved b (key x) c).value.1 <;>
        simp only [hb, Bool.false_eq_true, ite_false, ite_true] at hr <;>
        simp only [revealResult, hb, Bool.false_eq_true, ite_false, ite_true, Outcome.add,
          Outcome.combine, Outcome.map, List.length_cons] <;> omega

end SteinerUpperBound.LocalAccess

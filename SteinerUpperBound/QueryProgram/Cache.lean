module

public import SteinerUpperBound.QueryProgram.Resources

@[expose] public section

namespace SteinerUpperBound.QueryProgram

open SteinerLowerBound
open scoped Classical

abbrev Cache (Q : Type*) := Q → Option Bool

namespace Cache

variable {M Q : Type*}

def Correct (b : Q → Bool) (c : Cache Q) : Prop :=
  ∀ q v, c q = some v → b q = v

noncomputable def resolve (q : Q) (c : Cache Q) : Code M Q (Bool × Cache Q) :=
  .tick 0 (match c q with
    | some v => .pure (v, c)
    | none => .retained q (fun v => .tick 0 (.pure (v, Function.update c q (some v)))))

noncomputable def resolved (b : Q → Bool) (q : Q) (c : Cache Q) : Outcome (Bool × Cache Q) :=
  match c q with
  | some v => ⟨(v, c), 1, 0, 0, 0⟩
  | none => ⟨(b q, Function.update c q (some (b q))), 3, 0, 1, if b q then 1 else 0⟩

theorem resolve_evaluates (m : M → ℝ) (b : Q → Bool) (q : Q) (c : Cache Q) :
    Code.Evaluates m b (resolve q c) (resolved b q c) := by
  intro F
  cases h : c q <;>
    simp only [resolve, resolved, h, Code.evaluate, Outcome.add, Outcome.pure,
      Nat.add_zero, Nat.zero_add]

theorem resolved_correct (b : Q → Bool) (q : Q) (c : Cache Q) (hc : Correct b c) :
    (resolved b q c).value.1 = b q ∧ Correct b (resolved b q c).value.2 := by
  cases h : c q with
  | some v =>
      simp only [resolved, h]
      exact ⟨(hc q v h).symm, hc⟩
  | none =>
      simp only [resolved, h, true_and]
      intro q' v hv
      by_cases hq : q' = q
      · subst q'
        simpa using hv
      · exact hc q' v (by simpa only [Function.update_of_ne hq] using hv)

theorem resolved_work_le (b : Q → Bool) (q : Q) (c : Cache Q) :
    (resolved b q c).work ≤ 3 := by
  cases h : c q <;> simp only [resolved, h] <;> omega

theorem resolved_positive_le (b : Q → Bool) (q : Q) (c : Cache Q) :
    (resolved b q c).positiveReplies ≤ 1 := by
  cases h : c q <;> simp only [resolved, h]
  · cases b q <;> decide
  · omega

end Cache

end SteinerUpperBound.QueryProgram

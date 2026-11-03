module

public import SteinerUpperBound.MSTApproximation.Grid
public import SteinerUpperBound.QueryProgram

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open QueryProgram
open scoped Classical

variable {M Q : Type*}

noncomputable def indexProgram (q x : ℝ) : ℕ → Code M Q ℕ
  | 0 => .tick 1 (.pure 0)
  | fuel + 1 => .tick 2 (if 4 < x then .pure 0 else
      (indexProgram q (x * q) fuel).bind (fun i => .tick 1 (.pure (1 + i))))

noncomputable def indexResult (q x : ℝ) : ℕ → Outcome ℕ
  | 0 => ⟨0, 2, 0, 0, 0⟩
  | fuel + 1 => if 4 < x then ⟨0, 3, 0, 0, 0⟩ else
      ((indexResult q (x * q) fuel).map (fun i => 1 + i)).add 5 0 0 0

theorem indexProgram_evaluates (m : M → ℝ) (b : Q → Bool) (q x : ℝ) (fuel : ℕ) :
    Code.Evaluates m b (indexProgram q x fuel) (indexResult q x fuel) := by
  induction fuel generalizing x with
  | zero => intro F; rfl
  | succ fuel ih =>
    intro F
    by_cases hx : 4 < x
    · simp [indexProgram, indexResult, hx, Code.evaluate, Outcome.add, Outcome.pure]
    · simp only [indexProgram, indexResult, hx, ite_false, Code.evaluate, Code.evaluate_bind]
      rw [ih]
      simp only [Outcome.combine, Outcome.add, Outcome.map, Outcome.pure, Nat.add_zero, Nat.zero_add]
      congr 2 <;> omega

theorem indexResult_value (q x : ℝ) (fuel : ℕ) :
    (indexResult q x fuel).value = firstAbove q x fuel := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    by_cases hx : 4 < x <;> simp [indexResult, firstAbove, hx, Outcome.map, Outcome.add, ih]

theorem indexResult_resources (q x : ℝ) (fuel : ℕ) :
    (indexResult q x fuel).work ≤ 5 * fuel + 3 ∧
      (indexResult q x fuel).metricQueries = 0 ∧
      (indexResult q x fuel).retentionQueries = 0 ∧
      (indexResult q x fuel).positiveReplies = 0 := by
  induction fuel generalizing x with
  | zero => simp [indexResult]
  | succ fuel ih =>
    by_cases hx : 4 < x
    · simp [indexResult, hx]
    · have h := ih (x * q)
      simp only [indexResult, hx, ite_false, Outcome.map, Outcome.add] at *
      omega

noncomputable def gridProgram (k : ℕ) (q zeta theta R : ℝ) (fuel : ℕ)
    (hk : 0 < k) (hq : 1 < q) (hz : 0 < zeta) (ht : 0 < theta) (hR : 0 < R) :
    Code M Q Grid :=
  .tick (k + 10) ((indexProgram q (relativeStart k zeta theta) fuel).map
    (fun i => Grid.mk i q (relativeStart k zeta theta * R) hq
      (by unfold relativeStart; positivity)))

theorem gridProgram_evaluates (m : M → ℝ) (b : Q → Bool)
    (k : ℕ) (q zeta theta R : ℝ) (fuel : ℕ)
    (hk : 0 < k) (hq : 1 < q) (hz : 0 < zeta) (ht : 0 < theta) (hR : 0 < R) :
    Code.Evaluates m b (gridProgram k q zeta theta R fuel hk hq hz ht hR)
      ⟨generate k q zeta theta R fuel hk hq hz ht hR,
        k + 11 + (indexResult q (relativeStart k zeta theta) fuel).work, 0, 0, 0⟩ := by
  intro F
  simp only [gridProgram, Code.evaluate, Code.evaluate_map]
  rw [indexProgram_evaluates]
  have hv := indexResult_value q (relativeStart k zeta theta) fuel
  obtain ⟨_, hm, hr, hp⟩ := indexResult_resources q (relativeStart k zeta theta) fuel
  simp only [Outcome.map, Outcome.add, hv, hm, hr, hp, Nat.zero_add]

end SteinerUpperBound.MSTApproximation

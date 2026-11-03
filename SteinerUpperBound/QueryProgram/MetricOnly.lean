module

public import SteinerUpperBound.QueryProgram.DisclosureCap

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R : Type*}

def emptyBits : Empty → Bool := fun q => nomatch q

/-- Fix the unused logical oracle after its queries have been implemented by
the metric-query factory. The result cannot issue a retention query. -/
def metricOnly : Code M Q R → Code M Empty R
  | .pure r => .pure r
  | .metric q next => .metric q (fun a => (next a).metricOnly)
  | .retained _ next => (next false).metricOnly
  | .uniform n next => .uniform n (fun a => (next a).metricOnly)
  | .coin rate next => .coin rate (fun a => (next a).metricOnly)
  | .tick n next => .tick n next.metricOnly

theorem metricOnly_value (m : M → ℝ) (p : Code M Q R) (F : R → ℝ) :
    p.metricOnly.evaluate m emptyBits (fun o => F o.value) =
      p.evaluate m (fun _ => false) (fun o => F o.value) := by
  induction p with
  | pure r => rfl
  | metric q next ih =>
      simpa only [metricOnly, evaluate, Outcome.add] using ih (m q)
  | retained q next ih =>
      simpa only [metricOnly, evaluate, Outcome.add] using ih false
  | uniform n next ih =>
      simp only [metricOnly, evaluate, Outcome.add]
      apply congrArg (Law.uniform (Fin (n + 1))).expect
      funext a
      exact ih a
  | coin rate next ih =>
      simp only [metricOnly, evaluate, Outcome.add]
      apply congrArg (CategoricalCoupling.bernoulli rate).expect
      funext a
      exact ih a
  | tick n next ih =>
      simpa only [metricOnly, evaluate, Outcome.add] using ih

theorem metricOnly_work_mono (m : M → ℝ) (p : Code M Q R) (F : ℕ → ℝ) (hF : Monotone F) :
    p.metricOnly.evaluate m emptyBits (fun o => F o.work) ≤
      p.evaluate m (fun _ => false) (fun o => F o.work) := by
  induction p generalizing F with
  | pure r => exact le_rfl
  | metric q next ih =>
      simpa only [metricOnly, evaluate, Outcome.add] using
        ih (m q) (fun n => F (1 + n)) (fun _ _ h => hF (Nat.add_le_add_left h 1))
  | retained q next ih =>
      change (next false).metricOnly.evaluate m emptyBits (fun o => F o.work) ≤
        (next false).evaluate m (fun _ => false) (fun o => F (1 + o.work))
      exact (ih false F hF).trans
        (evaluate_mono _ _ _ (fun o => hF (by omega)))
  | uniform n next ih =>
      simp only [metricOnly, evaluate, Outcome.add]
      apply Law.expect_mono
      intro a
      exact ih a (fun n => F (1 + n)) (fun _ _ h => hF (Nat.add_le_add_left h 1))
  | coin rate next ih =>
      simp only [metricOnly, evaluate, Outcome.add]
      apply Law.expect_mono
      intro a
      exact ih a (fun n => F (2 + n)) (fun _ _ h => hF (Nat.add_le_add_left h 2))
  | tick n next ih =>
      simpa only [metricOnly, evaluate, Outcome.add] using
        ih (fun k => F (n + 1 + k)) (fun _ _ h => hF (Nat.add_le_add_left h (n + 1)))

theorem metricOnly_expected_work (m : M → ℝ) (p : Code M Q R) :
    p.metricOnly.evaluate m emptyBits (fun o => (o.work : ℝ)) ≤
      p.evaluate m (fun _ => false) (fun o => (o.work : ℝ)) :=
  metricOnly_work_mono m p (fun n => (n : ℝ)) (fun _ _ h => Nat.cast_le.mpr h)

theorem empty_retention (m : M → ℝ) (p : Code M Empty R) :
    ∀ s : (p.compile m).Seed,
      (((p.compile m).tree s).output emptyBits).retentionQueries = 0 := by
  induction p with
  | pure r => intro s; rfl
  | metric q next ih =>
      intro s
      simpa only [compile, Compiled.map, DecisionTree.output_map, Outcome.add,
        Nat.zero_add] using ih (m q) s
  | retained q _ _ => exact Empty.elim q
  | uniform n next ih =>
      intro s
      simpa only [compile, Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add,
        Nat.zero_add] using ih s.1 s.2
  | coin rate next ih =>
      intro s
      simpa only [compile, Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add,
        Nat.zero_add] using ih s.1 s.2
  | tick n next ih =>
      intro s
      simpa only [compile, Compiled.map, DecisionTree.output_map, Outcome.add,
        Nat.zero_add] using ih s

end SteinerUpperBound.QueryProgram.Code

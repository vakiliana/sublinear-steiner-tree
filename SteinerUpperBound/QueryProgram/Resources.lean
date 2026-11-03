module

public import SteinerUpperBound.QueryProgram.Composition

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R S : Type*}

theorem accounted (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) :
    ∀ s : (p.compile m).Seed,
      let o := ((p.compile m).tree s).output b
      o.metricQueries + o.retentionQueries ≤ o.work ∧ o.positiveReplies ≤ o.retentionQueries := by
  induction p with
  | pure r =>
      intro s
      simp only [compile, Compiled.leaf, DecisionTree.output, Outcome.pure, Nat.add_zero,
        le_refl, and_self]
  | metric q next ih =>
      intro s
      have hs := ih (m q) s
      simp only [compile, Compiled.map, DecisionTree.output_map, Outcome.add]
      dsimp only at hs
      omega
  | retained q next ih =>
      intro s
      cases hb : b q with
      | false =>
          have hs := ih false s.1
          simp only [compile, Compiled.query, DecisionTree.output, hb, Bool.false_eq_true,
            ite_false, Compiled.map, DecisionTree.output_map, Outcome.add]
          dsimp only at hs
          omega
      | true =>
          have hs := ih true s.2
          simp only [compile, Compiled.query, DecisionTree.output, hb,
            ite_true, Compiled.map, DecisionTree.output_map, Outcome.add]
          dsimp only at hs
          omega
  | uniform n next ih =>
      intro s
      have hs := ih s.1 s.2
      simp only [compile, Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add]
      dsimp only at hs
      omega
  | coin rate next ih =>
      intro s
      have hs := ih s.1 s.2
      simp only [compile, Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add]
      dsimp only at hs
      omega
  | tick n next ih =>
      intro s
      have hs := ih s
      simp only [compile, Compiled.map, DecisionTree.output_map, Outcome.add]
      dsimp only at hs
      omega

theorem cap_metric_queries (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (s : ((p.cap budget).compile m).Seed) :
    ((((p.cap budget).compile m).tree s).output b).metricQueries ≤ budget := by
  have ha := (accounted m b (p.cap budget) s).1
  have hw := cap_work m b p budget s
  omega

theorem evaluate_work_bind (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) :
    (p.bind k).evaluate m b (fun o => (o.work : ℝ)) =
      p.evaluate m b (fun a =>
        (a.work : ℝ) + (k a.value).evaluate m b (fun o => (o.work : ℝ))) := by
  rw [evaluate_bind]
  apply congrArg (p.evaluate m b)
  funext a
  simp only [Outcome.combine, Nat.cast_add, evaluate_add, evaluate_const]

theorem evaluate_positive_bind (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (k : R → Code M Q S) :
    (p.bind k).evaluate m b (fun o => (o.positiveReplies : ℝ)) =
      p.evaluate m b (fun a =>
        (a.positiveReplies : ℝ) +
          (k a.value).evaluate m b (fun o => (o.positiveReplies : ℝ))) := by
  rw [evaluate_bind]
  apply congrArg (p.evaluate m b)
  funext a
  simp only [Outcome.combine, Nat.cast_add, evaluate_add, evaluate_const]

end SteinerUpperBound.QueryProgram.Code

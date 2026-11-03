module

public import SteinerUpperBound.QueryProgram.MetricOnly

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R S : Type*}

theorem map_compiled_output (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R) (f : R → S) :
    ∀ s : ((p.map f).compile m).Seed, ∃ t : (p.compile m).Seed,
      ((((p.map f).compile m).tree s).output bits) = ((((p.compile m).tree t).output bits).map f) := by
  induction p with
  | pure r => intro s; exact ⟨s, rfl⟩
  | metric q next ih =>
      intro s
      obtain ⟨t, ht⟩ := ih (m q) s
      refine ⟨t, ?_⟩
      simp only [map, bind, compile, Compiled.map, DecisionTree.output_map]
      change (((((next (m q)).map f).compile m).tree s).output bits).add 1 1 0 0 =
        (((((next (m q)).compile m).tree t).output bits).add 1 1 0 0).map f
      rw [ht]
      rfl
  | retained q next ih =>
      intro s
      obtain ⟨t0, h0⟩ := ih false s.1
      obtain ⟨t1, h1⟩ := ih true s.2
      refine ⟨(t0, t1), ?_⟩
      cases hb : bits q with
      | false =>
          simp only [map, bind, compile, Compiled.query, DecisionTree.output, hb,
            Bool.false_eq_true, ite_false, Compiled.map, DecisionTree.output_map]
          change (((((next false).map f).compile m).tree s.1).output bits).add 1 0 1 0 =
            (((((next false).compile m).tree t0).output bits).add 1 0 1 0).map f
          rw [h0]
          rfl
      | true =>
          simp only [map, bind, compile, Compiled.query, DecisionTree.output, hb,
            ite_true, Compiled.map, DecisionTree.output_map]
          change (((((next true).map f).compile m).tree s.2).output bits).add 1 0 1 1 =
            (((((next true).compile m).tree t1).output bits).add 1 0 1 1).map f
          rw [h1]
          rfl
  | uniform n next ih =>
      intro s
      obtain ⟨t, ht⟩ := ih s.1 s.2
      refine ⟨⟨s.1, t⟩, ?_⟩
      simp only [map, bind, compile, Compiled.map, Compiled.choose, DecisionTree.output_map]
      change (((((next s.1).map f).compile m).tree s.2).output bits).add 1 0 0 0 =
        (((((next s.1).compile m).tree t).output bits).add 1 0 0 0).map f
      rw [ht]
      rfl
  | coin rate next ih =>
      intro s
      obtain ⟨t, ht⟩ := ih s.1 s.2
      refine ⟨⟨s.1, t⟩, ?_⟩
      simp only [map, bind, compile, Compiled.map, Compiled.choose, DecisionTree.output_map]
      change (((((next s.1).map f).compile m).tree s.2).output bits).add 2 0 0 0 =
        (((((next s.1).compile m).tree t).output bits).add 2 0 0 0).map f
      rw [ht]
      rfl
  | tick n next ih =>
      intro s
      obtain ⟨t, ht⟩ := ih s
      refine ⟨t, ?_⟩
      simp only [map, bind, compile, Compiled.map, DecisionTree.output_map]
      change ((((next.map f).compile m).tree s).output bits).add (n + 1) 0 0 0 =
        ((((next.compile m).tree t).output bits).add (n + 1) 0 0 0).map f
      rw [ht]
      rfl

def capDefault (budget : ℕ) (fallback : R) (p : Code M Q R) : Code M Q R :=
  .tick 0 ((p.cap budget).map (fun r => r.getD fallback))

theorem capDefault_resources (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (fallback : R) (s : ((p.capDefault budget fallback).compile m).Seed) :
    let o := (((p.capDefault budget fallback).compile m).tree s).output bits
    o.work ≤ budget + 1 ∧ o.metricQueries ≤ budget := by
  change (((p.cap budget).map (fun r => r.getD fallback)).compile m).Seed at s
  obtain ⟨t, ht⟩ := map_compiled_output m bits (p.cap budget) (fun r => r.getD fallback) s
  have hw := cap_work m bits p budget t
  have hm := cap_metric_queries m bits p budget t
  simp only [capDefault, compile, Compiled.map, DecisionTree.output_map, Outcome.add, Nat.zero_add]
  change 1 + (((((p.cap budget).map (fun r => r.getD fallback)).compile m).tree s).output bits).work ≤
      budget + 1 ∧
    (((((p.cap budget).map (fun r => r.getD fallback)).compile m).tree s).output bits).metricQueries ≤ budget
  rw [ht]
  exact ⟨by dsimp only [Outcome.map]; omega, hm⟩

theorem capDefault_success (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (fallback : R) (P : R → Prop) :
    valueProbability m bits p P - p.evaluate m bits (fun o => (o.work : ℝ)) / (budget + 1 : ℕ) ≤
      valueProbability m bits (p.capDefault budget fallback) P := by
  have hc := cap_success m bits p budget P
  have hm : valueProbability m bits (p.cap budget) (SomeGood P) ≤
      valueProbability m bits (p.capDefault budget fallback) P := by
    change (p.cap budget).evaluate m bits (fun o => if SomeGood P o.value then (1 : ℝ) else 0) ≤ _
    change _ ≤ (((p.cap budget).map (fun r => r.getD fallback))).evaluate m bits
      (fun o => if P o.value then (1 : ℝ) else 0)
    rw [evaluate_map]
    apply evaluate_mono
    intro o
    cases h : o.value <;> simp [SomeGood, Outcome.map, h]
    split_ifs <;> norm_num
  exact hc.trans hm

end SteinerUpperBound.QueryProgram.Code

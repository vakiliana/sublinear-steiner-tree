module

public import SteinerUpperBound.QueryProgram.Seed

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R : Type*}

def cap (budget : ℕ) : Code M Q R → Code M Q (Option R)
  | .pure r => .pure (some r)
  | .metric q next =>
      if 1 ≤ budget then .metric q (fun a => (next a).cap (budget - 1)) else .pure none
  | .retained q next =>
      if 1 ≤ budget then .retained q (fun a => (next a).cap (budget - 1)) else .pure none
  | .uniform n next =>
      if 1 ≤ budget then .uniform n (fun a => (next a).cap (budget - 1)) else .pure none
  | .coin rate next =>
      if 2 ≤ budget then .coin rate (fun a => (next a).cap (budget - 2)) else .pure none
  | .tick n next =>
      if n + 1 ≤ budget then .tick n (next.cap (budget - (n + 1))) else .pure none

theorem cap_work (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (budget : ℕ) :
    ∀ s : ((p.cap budget).compile m).Seed,
      ((((p.cap budget).compile m).tree s).output b).work ≤ budget := by
  induction p generalizing budget with
  | pure r =>
      intro s
      simp only [cap, compile, Compiled.leaf, DecisionTree.output, Outcome.pure]
      exact Nat.zero_le _
  | metric q next ih =>
      by_cases h : 1 ≤ budget
      · rw [cap, if_pos h, compile]
        intro s
        have hs := ih (m q) (budget - 1) s
        simp only [Compiled.map, DecisionTree.output_map, Outcome.add]
        omega
      · rw [cap, if_neg h, compile]
        intro s
        change 0 ≤ budget
        exact Nat.zero_le _
  | retained q next ih =>
      by_cases h : 1 ≤ budget
      · rw [cap, if_pos h, compile]
        intro s
        cases hb : b q with
        | false =>
            have hs := ih false (budget - 1) s.1
            simp only [Compiled.query, DecisionTree.output, hb, Bool.false_eq_true, ite_false,
              Compiled.map, DecisionTree.output_map, Outcome.add]
            omega
        | true =>
            have hs := ih true (budget - 1) s.2
            simp only [Compiled.query, DecisionTree.output, hb, ite_true,
              Compiled.map, DecisionTree.output_map, Outcome.add]
            omega
      · rw [cap, if_neg h, compile]
        intro s
        change 0 ≤ budget
        exact Nat.zero_le _
  | uniform n next ih =>
      by_cases h : 1 ≤ budget
      · rw [cap, if_pos h, compile]
        intro s
        have hs := ih s.1 (budget - 1) s.2
        simp only [Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add]
        omega
      · rw [cap, if_neg h, compile]
        intro s
        change 0 ≤ budget
        exact Nat.zero_le _
  | coin rate next ih =>
      by_cases h : 2 ≤ budget
      · rw [cap, if_pos h, compile]
        intro s
        have hs := ih s.1 (budget - 2) s.2
        simp only [Compiled.map, Compiled.choose, DecisionTree.output_map, Outcome.add]
        omega
      · rw [cap, if_neg h, compile]
        intro s
        change 0 ≤ budget
        exact Nat.zero_le _
  | tick n next ih =>
      by_cases h : n + 1 ≤ budget
      · rw [cap, if_pos h, compile]
        intro s
        have hs := ih (budget - (n + 1)) s
        simp only [Compiled.map, DecisionTree.output_map, Outcome.add]
        omega
      · rw [cap, if_neg h, compile]
        intro s
        change 0 ≤ budget
        exact Nat.zero_le _

theorem cap_expect (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (F : R → ℝ) :
    (p.cap budget).evaluate m b (fun o => o.value.elim 0 F) =
      p.evaluate m b (fun o => if o.work ≤ budget then F o.value else 0) := by
  induction p generalizing budget with
  | pure r => simp [cap, evaluate, Outcome.pure]
  | metric q next ih =>
      by_cases h : 1 ≤ budget
      · have ht (v : ℕ) : 1 + v ≤ budget ↔ v ≤ budget - 1 := by omega
        simpa only [cap, h, ite_true, evaluate, Outcome.add, ht] using
          ih (m q) (budget - 1)
      · have ht (v : ℕ) : ¬1 + v ≤ budget := by omega
        simp only [cap, h, ite_false, evaluate, Outcome.pure, Option.elim_none, Outcome.add,
          ht, evaluate_const]
  | retained q next ih =>
      by_cases h : 1 ≤ budget
      · have ht (v : ℕ) : 1 + v ≤ budget ↔ v ≤ budget - 1 := by omega
        simpa only [cap, h, ite_true, evaluate, Outcome.add, ht] using
          ih (b q) (budget - 1)
      · have ht (v : ℕ) : ¬1 + v ≤ budget := by omega
        simp only [cap, h, ite_false, evaluate, Outcome.pure, Option.elim_none, Outcome.add,
          ht, evaluate_const]
  | uniform n next ih =>
      by_cases h : 1 ≤ budget
      · have ht (v : ℕ) : 1 + v ≤ budget ↔ v ≤ budget - 1 := by omega
        simp only [cap, h, ite_true, evaluate]
        apply congrArg (Law.uniform (Fin (n + 1))).expect
        funext a
        simpa only [Outcome.add, ht] using ih a (budget - 1)
      · have ht (v : ℕ) : ¬1 + v ≤ budget := by omega
        simp only [cap, h, ite_false, evaluate, Outcome.pure, Option.elim_none, Outcome.add,
          ht, evaluate_const, Law.expect_const]
  | coin rate next ih =>
      by_cases h : 2 ≤ budget
      · have ht (v : ℕ) : 2 + v ≤ budget ↔ v ≤ budget - 2 := by omega
        simp only [cap, h, ite_true, evaluate]
        apply congrArg (CategoricalCoupling.bernoulli rate).expect
        funext a
        simpa only [Outcome.add, ht] using ih a (budget - 2)
      · have ht (v : ℕ) : ¬2 + v ≤ budget := by omega
        simp only [cap, h, ite_false, evaluate, Outcome.pure, Option.elim_none, Outcome.add,
          ht, evaluate_const, Law.expect_const]
  | tick n next ih =>
      by_cases h : n + 1 ≤ budget
      · have ht (v : ℕ) : n + 1 + v ≤ budget ↔ v ≤ budget - (n + 1) := by omega
        simpa only [cap, h, ite_true, evaluate, Outcome.add, ht] using
          ih (budget - (n + 1))
      · have ht (v : ℕ) : ¬n + 1 + v ≤ budget := by omega
        simp only [cap, h, ite_false, evaluate, Outcome.pure, Option.elim_none, Outcome.add,
          ht, evaluate_const]

theorem positive_floor (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (F : ℕ → ℝ) (hF : Monotone F) :
    F 0 ≤ p.evaluate m b (fun o => F o.positiveReplies) := by
  calc
    _ = p.evaluate m b (fun _ => F 0) := (evaluate_const m b p _).symm
    _ ≤ _ := evaluate_mono m b p (fun o => hF (Nat.zero_le _))

theorem cap_positive_mono (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (F : ℕ → ℝ) (hF : Monotone F) :
    (p.cap budget).evaluate m b (fun o => F o.positiveReplies) ≤
      p.evaluate m b (fun o => F o.positiveReplies) := by
  induction p generalizing budget F with
  | pure r => simp only [cap, evaluate, Outcome.pure, le_refl]
  | metric q next ih =>
      by_cases h : 1 ≤ budget
      · simpa only [cap, h, ite_true, evaluate, Outcome.add, Nat.zero_add] using
          ih (m q) (budget - 1) F hF
      · simpa only [cap, h, ite_false, evaluate, Outcome.pure] using
          positive_floor m b (.metric q next) F hF
  | retained q next ih =>
      by_cases h : 1 ≤ budget
      · simpa only [cap, h, ite_true, evaluate, Outcome.add] using
          ih (b q) (budget - 1) (fun v => F ((if b q then 1 else 0) + v))
            (fun _ _ hle => hF (Nat.add_le_add_left hle _))
      · simpa only [cap, h, ite_false, evaluate, Outcome.pure] using
          positive_floor m b (.retained q next) F hF
  | uniform n next ih =>
      by_cases h : 1 ≤ budget
      · simp only [cap, h, ite_true, evaluate, Outcome.add, Nat.zero_add]
        exact (Law.uniform (Fin (n + 1))).expect_mono
          (fun a => ih a (budget - 1) F hF)
      · simpa only [cap, h, ite_false, evaluate, Outcome.pure] using
          positive_floor m b (.uniform n next) F hF
  | coin rate next ih =>
      by_cases h : 2 ≤ budget
      · simp only [cap, h, ite_true, evaluate, Outcome.add, Nat.zero_add]
        exact (CategoricalCoupling.bernoulli rate).expect_mono
          (fun a => ih a (budget - 2) F hF)
      · simpa only [cap, h, ite_false, evaluate, Outcome.pure] using
          positive_floor m b (.coin rate next) F hF
  | tick n next ih =>
      by_cases h : n + 1 ≤ budget
      · simpa only [cap, h, ite_true, evaluate, Outcome.add, Nat.zero_add] using
          ih (budget - (n + 1)) F hF
      · simpa only [cap, h, ite_false, evaluate, Outcome.pure] using
          positive_floor m b (.tick n next) F hF

end SteinerUpperBound.QueryProgram.Code

module

public import SteinerUpperBound.Matching.Padded.RuntimeCost
public import SteinerUpperBound.Matching.Padded.CounterTruncation
public import SteinerUpperBound.Matching.Padded.TruncationBudget

@[expose] public section

set_option maxHeartbeats 2400000

namespace SteinerUpperBound.Matching.Padded.Presentation

open SteinerLowerBound
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

theorem answer_truncated_counter (v : V) (hC : 0 < A.Cstar) :
    (Runtime.answer C I (J.vertex v)).evaluate m bits (fun o =>
      if counter.value o ≤ Account.truncationLimit S J.parameters A then counter.value o else 0) ≤
      A.Cstar + 2 * (1 / (C.Nstar : ℝ) ^ 30) * A.Cstar *
          Parameters.truncationScale S J.parameters +
        2 * (Parameters.truncationExponent S J.parameters : ℝ) *
          Execution.goodCost S J.parameters A v := by
  have ht := Causal.code_truncated_of_tail m bits (Runtime.answer C I (J.vertex v))
    counter A.Cstar (1 / (C.Nstar : ℝ) ^ 30) (Execution.goodCost S J.parameters A v)
    hC (by positivity)
    (fun t ht => answer_counter_tail J I m bits K D A counter resources v t ht)
    (Parameters.truncationExponent S J.parameters)
  exact ht

omit D resources

variable (family : V → Runtime.Primitives C.length Label M T)
    (contracts : ∀ v, J.Contract (family v) m bits)
    (deterministic : ∀ v, J.Deterministic (family v) m bits (contracts v))
    (accounts : ∀ v, J.Resources (family v) m bits (contracts v) A counter)

include deterministic accounts

theorem family_answer_truncated_counter [Nonempty V] (hC : 0 < A.Cstar) :
    (Law.uniform V).expect (fun v =>
      (Runtime.answer C (family v) (J.vertex v)).evaluate m bits (fun o =>
        if counter.value o ≤ Account.truncationLimit S J.parameters A then counter.value o else 0)) ≤
      Parameters.truncatedFactor S J.parameters * Account.publicPrice S A := by
  have hp := (Law.uniform V).expect_mono (fun v =>
    answer_truncated_counter J (family v) m bits (contracts v) (deterministic v)
      A counter (accounts v) v hC)
  simp only [Law.expect_add, Law.expect_const, Law.expect_const_mul] at hp
  have hc := mul_le_mul_of_nonneg_left (Execution.expected_goodCost_le S J.parameters A)
    (show (0 : ℝ) ≤ 2 * (Parameters.truncationExponent S J.parameters : ℝ) by positivity)
  exact (hp.trans (add_le_add (le_refl _) hc)).trans
    (Parameters.truncated_budget_le S J.parameters A)

/-- Root-dependent genuine primitive states are averaged only after pointwise refinement. -/
theorem family_answer_original_good_cost [Nonempty V] (hC : 0 < A.Cstar) :
    (Law.uniform V).expect (fun v =>
      ((Runtime.answer C (family v) (J.vertex v)).compile m).law.expect (fun seed =>
        if Causal.counterGood m bits (Runtime.answer C (family v) (J.vertex v)) counter
            (Account.truncationLimit S J.parameters A) seed then
          Causal.counterSeed m bits (Runtime.answer C (family v) (J.vertex v)) counter seed else 0)) ≤
      Parameters.truncatedFactor S J.parameters * Account.publicPrice S A := by
  simp_rw [Causal.counterGood_cost]
  exact family_answer_truncated_counter J m bits A counter family contracts deterministic accounts hC

/-- The exceptional event is on each original `Runtime.answer.compile` seed. -/
theorem family_answer_original_good_failure [Nonempty V] (hC : 0 < A.Cstar) :
    (Law.uniform V).expect (fun v =>
      ((Runtime.answer C (family v) (J.vertex v)).compile m).law.prob {seed |
        ¬ Causal.counterGood m bits (Runtime.answer C (family v) (J.vertex v)) counter
          (Account.truncationLimit S J.parameters A) seed}) ≤ 1 / (C.Nstar : ℝ) ^ 3 := by
  simp_rw [Causal.counterGood_failure]
  have hlimit : 0 < Account.truncationLimit S J.parameters A := by
    unfold Account.truncationLimit Parameters.truncationScale
    positivity
  have hp (v : V) :
      (Runtime.answer C (family v) (J.vertex v)).evaluate m bits
        (fun o => if ¬ counter.value o ≤ Account.truncationLimit S J.parameters A then 1 else 0) ≤
      (Runtime.answer C (family v) (J.vertex v)).evaluate m bits
        (fun o => if Account.truncationLimit S J.parameters A ≤ counter.value o then 1 else 0) := by
    apply QueryProgram.Code.evaluate_mono
    intro o
    split_ifs <;> norm_num at * <;> linarith
  have hh := (Law.uniform V).expect_mono hp
  exact (hh.trans
    (family_answer_counter_tail J m bits A counter family contracts deterministic accounts
      (Account.truncationLimit S J.parameters A) hlimit)).trans
    (Parameters.truncation_error_le S J.parameters A hC)

end SteinerUpperBound.Matching.Padded.Presentation

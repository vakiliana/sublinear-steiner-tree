module

public import SteinerUpperBound.Matching.Padded.ClosedCost
public import SteinerUpperBound.Matching.Padded.CounterTail

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

theorem answer_counter_tail (v : V) (threshold : ℝ) (ht : 0 < threshold) :
    (Runtime.answer C I (J.vertex v)).evaluate m bits
        (fun o => if threshold ≤ counter.value o then 1 else 0) ≤
      1 / (C.Nstar : ℝ) ^ 30 + Execution.goodCost S J.parameters A v / threshold := by
  rw [Runtime.answer, QueryProgram.Code.evaluate_map]
  exact vertex_counter_tail J I m bits K D A counter resources v threshold ht

omit D resources

variable (family : V → Runtime.Primitives C.length Label M T)
    (contracts : ∀ v, J.Contract (family v) m bits)
    (deterministic : ∀ v, J.Deterministic (family v) m bits (contracts v))
    (accounts : ∀ v, J.Resources (family v) m bits (contracts v) A counter)

include deterministic accounts

/-- Every root may supply its own correct incoming primitive cache and frame. -/
theorem family_answer_counter_tail [Nonempty V] (threshold : ℝ) (ht : 0 < threshold) :
    (Law.uniform V).expect (fun v =>
      (Runtime.answer C (family v) (J.vertex v)).evaluate m bits
        (fun o => if threshold ≤ counter.value o then 1 else 0)) ≤
      1 / (C.Nstar : ℝ) ^ 30 +
        Parameters.costFactor S J.parameters * Account.publicPrice S A / threshold := by
  have hp := (Law.uniform V).expect_mono (fun v =>
    answer_counter_tail J (family v) m bits (contracts v) (deterministic v)
      A counter (accounts v) v threshold ht)
  rw [Law.expect_add, Law.expect_const] at hp
  simp only [div_eq_mul_inv, Law.expect_mul_const] at hp
  have hc := mul_le_mul_of_nonneg_right
    (Execution.expected_goodCost_le S J.parameters A) (inv_nonneg.mpr ht.le)
  exact hp.trans (add_le_add (le_refl _) (by simpa only [div_eq_mul_inv] using hc))

end SteinerUpperBound.Matching.Padded.Presentation

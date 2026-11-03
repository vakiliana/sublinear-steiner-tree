module

public import SteinerUpperBound.Matching.Padded.MatchedLaw
public import SteinerUpperBound.Matching.Padded.ModelValueKernel

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open SteinerLowerBound
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

/-- The actual causal callback has the global greedy-matching kernel up to the explicit tie budget. -/
theorem answer_mean_error (v : V) (f : Bool → ℝ)
    (hf0 : ∀ value, 0 ≤ f value) (hf1 : ∀ value, f value ≤ 1) :
    |(Runtime.answer C I (J.vertex v)).evaluate m bits (fun o => f o.value.1) -
        (Rank.uniform (E := E)).expect (fun ρ => f (G.vertexOracle ρ v).value.isSome)| ≤
      1 / (C.Nstar : ℝ) ^ 30 := by
  rw [answer_matched_law J I m bits K D A counter resources v f]
  exact Execution.matched_mean_error_budget S J.parameters v f hf0 hf1

theorem answer_event_error (v : V) (event : Set Bool) :
    |(Runtime.answer C I (J.vertex v)).evaluate m bits (fun o => if o.value.1 ∈ event then 1 else 0) -
        (Rank.uniform (E := E)).prob {ρ | (G.vertexOracle ρ v).value.isSome ∈ event}| ≤
      1 / (C.Nstar : ℝ) ^ 30 := by
  classical
  rw [Law.prob_eq_expect]
  exact answer_mean_error J I m bits K D A counter resources v
    (fun value => if value ∈ event then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)

end SteinerUpperBound.Matching.Padded.Presentation

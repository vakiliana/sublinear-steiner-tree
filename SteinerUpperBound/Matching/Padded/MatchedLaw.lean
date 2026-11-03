module

public import SteinerUpperBound.Matching.Padded.OracleDomination

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

theorem vertex_matched_law (v : V) (f : Bool → ℝ) :
    Causal.expect m bits (Runtime.vertex C I (J.vertex v)) (fun r => f r.value.isSome) =
      (Oracle.vertex S J.parameters v).expect (fun r => f r.value.isSome) := by
  apply Causal.Dominates.value_law m bits counter (Command.charge A) A.rate _ _ _
    (vertex_dominates J I m bits K D A counter resources v)
  intro result raw h
  rw [h.value]
  cases result.value <;> rfl

theorem answer_matched_law (v : V) (f : Bool → ℝ) :
    (Runtime.answer C I (J.vertex v)).evaluate m bits (fun o => f o.value.1) =
      (Oracle.vertex S J.parameters v).expect (fun r => f r.value.isSome) := by
  change Causal.expect m bits (Runtime.answer C I (J.vertex v)) (fun answer => f answer.1) = _
  unfold Runtime.answer SteinerUpperBound.QueryProgram.Code.map
  rw [Causal.expect_bind]
  simp only [Causal.expect_pure]
  exact vertex_matched_law J I m bits K D A counter resources v f

theorem answer_preserves (v : V) :
    Causal.Ensures m bits (Runtime.answer C I (J.vertex v)) (fun answer => K.Inv answer.2) := by
  intro f hf
  unfold Runtime.answer SteinerUpperBound.QueryProgram.Code.map
  rw [Causal.expect_bind]
  simp only [Causal.expect_pure]
  have h := Causal.Dominates.value_law m bits counter (Command.charge A) A.rate _ _ _
    (vertex_dominates J I m bits K D A counter resources v)
    (fun _ => 0) (fun r => f (r.value.isSome, r.cache.memory))
    (fun _ raw hr => (hf _ hr.state.memory.1).symm)
  simpa only [Program.expect_const] using h

end SteinerUpperBound.Matching.Padded.Presentation

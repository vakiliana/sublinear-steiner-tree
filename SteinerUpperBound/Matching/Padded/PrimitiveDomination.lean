module

public import SteinerUpperBound.Matching.Padded.ArithmeticDomination
public import SteinerUpperBound.Matching.Padded.Presentation

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (b : T → Bool)
    (K : J.Contract I m b)

/-- Local metric/retention frontends are deterministic after fixing their oracle and cache. -/
structure Deterministic : Prop where
  prepare : ∀ v memory, K.Inv memory →
    ∃ o, (I.prepare (J.vertex v) memory).Evaluates m b o
  slot : ∀ s memory, K.Inv memory → K.Ready memory s.1 →
    ∃ o, (I.slot (J.slot s) memory).Evaluates m b o

theorem slot_dominates (D : J.Deterministic I m b K) (A : Account S) (counter : Causal.Counter)
    (hcost : J.Resources I m b K A counter) (s : Slot S.length) (memory : I.Memory)
    (hmemory : K.Inv memory) (hready : K.Ready memory s.1) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (Command.testSlot S s) (I.slot (J.slot s) memory)
      (fun hit answer => answer.1 = hit.map (fun edge => (J.label edge.1, J.slot edge.2)) ∧
        K.Inv answer.2 ∧ ∀ v, K.Ready memory v → K.Ready answer.2 v) := by
  obtain ⟨o, ho⟩ := D.slot s memory hmemory hready
  have hv := Causal.ensures_holds_of_evaluates m b _ _
    (K.slot s memory hmemory hready) o ho
  have hc := hcost.slot s memory hmemory hready
  rw [ho] at hc
  apply Causal.Dominates.primitive
  apply Causal.ensuresOutcome_of_evaluates m b _ o ho
  exact ⟨hv, hc⟩

theorem prepare_dominates (D : J.Deterministic I m b K) (A : Account S) (counter : Causal.Counter)
    (hcost : J.Resources I m b K A counter) (v : V) (memory : I.Memory)
    (hmemory : K.Inv memory) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (.tick (.prepare v) (.ret ())) (I.prepare (J.vertex v) memory)
      (fun _ memory' => K.Inv memory' ∧ K.Ready memory' v ∧
        ∀ u, K.Ready memory u → K.Ready memory' u) := by
  obtain ⟨o, ho⟩ := D.prepare v memory hmemory
  have hv := Causal.ensures_holds_of_evaluates m b _ _
    (K.prepare v memory hmemory) o ho
  have hc := hcost.prepare v memory hmemory
  rw [ho] at hc
  apply Causal.Dominates.primitive
  apply Causal.ensuresOutcome_of_evaluates m b _ o ho
  exact ⟨hv, hc⟩

end SteinerUpperBound.Matching.Padded.Presentation

module

public import SteinerUpperBound.Matching.Padded.Runtime
public import SteinerUpperBound.Matching.Padded.CausalContract

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E}

/-- The proof graph may have metric-dependent subtype carriers; runtime names do not. -/
structure Presentation (S : Slots G) [Fintype V] (P : Parameters S) (C : Runtime.Config Vertex) where
  vertex : V ↪ Vertex
  label : E ↪ Label
  length_eq : ∀ v, S.length v = C.length (vertex v)
  size_eq : P.Nstar = C.Nstar

namespace Presentation

variable {S : Slots G} [Fintype V] {P : Parameters S} {C : Runtime.Config Vertex}
    (J : Presentation (Label := Label) S P C)

def slot (s : Slot S.length) : Slot C.length :=
  ⟨J.vertex s.1, Fin.cast (J.length_eq s.1) s.2⟩

@[simp] theorem slot_vertex (s : Slot S.length) : (J.slot s).1 = J.vertex s.1 := rfl

@[simp] theorem slot_index (s : Slot S.length) : (J.slot s).2.val = s.2.val := rfl

theorem slot_injective : Function.Injective J.slot := by
  intro s t h
  obtain ⟨v, i⟩ := s
  obtain ⟨u, j⟩ := t
  have hv : v = u := J.vertex.injective (congrArg Sigma.fst h)
  subst u
  have hi : i.val = j.val := congrArg (fun z : Slot C.length => z.2.val) h
  exact congrArg (Sigma.mk v) (Fin.ext hi)

include J in
theorem rankCard_eq : P.rankCard = C.rankCard := by
  simp only [Parameters.rankCard, Parameters.rankExponent, Parameters.logarithm,
    Runtime.Config.rankCard, Runtime.Config.rankExponent, Runtime.Config.logarithm, J.size_eq]

variable (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (b : T → Bool)

structure Contract where
  Inv : I.Memory → Prop
  Ready : I.Memory → V → Prop
  initial : Inv I.initial
  prepare : ∀ v memory, Inv memory →
    Causal.Ensures m b (I.prepare (J.vertex v) memory) (fun memory' =>
      Inv memory' ∧ Ready memory' v ∧ ∀ u, Ready memory u → Ready memory' u)
  slot : ∀ s memory, Inv memory → Ready memory s.1 →
    Causal.Ensures m b (I.slot (J.slot s) memory) (fun answer =>
      answer.1 = (S.test s).map (fun hit => (J.label hit.1, J.slot hit.2)) ∧
        Inv answer.2 ∧ ∀ u, Ready memory u → Ready answer.2 u)

structure Resources (K : J.Contract I m b) (A : Account S) (c : Causal.Counter) : Prop where
  rate : A.rate = c.work
  prepare : ∀ v memory, K.Inv memory →
    (I.prepare (J.vertex v) memory).evaluate m b c.value ≤ A.preparation v
  slot : ∀ s memory, K.Inv memory → K.Ready memory s.1 →
    (I.slot (J.slot s) memory).evaluate m b c.value ≤ A.slot s

end Presentation

end SteinerUpperBound.Matching.Padded

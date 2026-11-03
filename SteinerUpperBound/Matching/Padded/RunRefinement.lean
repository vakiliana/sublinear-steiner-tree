module

public import SteinerUpperBound.Matching.Padded.RefinementMetadata
public import SteinerUpperBound.Matching.Padded.CacheFacts
public import SteinerUpperBound.Matching.Padded.Invariant

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)

def MemoMatch (μ : Memo E) (ν : Label × Vertex → Option Bool) : Prop :=
  ∀ d, ν (J.liftDirected d) = μ d

theorem empty_memoMatch : J.MemoMatch (fun _ => none) (fun _ => none) := fun _ => rfl

theorem MemoMatch.update {μ : Memo E} {ν : Label × Vertex → Option Bool}
    (h : J.MemoMatch μ ν) (d : Directed E) (value : Bool) :
    J.MemoMatch (Function.update μ d (some value))
      (Function.update ν (J.liftDirected d) (some value)) := by
  classical
  intro e
  by_cases he : e = d
  · subst e; simp
  · have hraw : J.liftDirected e ≠ J.liftDirected d := J.liftDirected_injective.ne he
    simpa only [Function.update_of_ne he, Function.update_of_ne hraw] using h e

variable (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits)

structure RunMatch {A B : Type*} (R : A → B → Prop)
    (run : LocalRun S C.rankCard A) (raw : Runtime.Result C I B) : Prop where
  value : R run.value raw.value
  memo : J.MemoMatch run.memo raw.memo
  state : J.StateMatch I m bits K run.cache raw.cache
  calls : raw.calls = run.calls.map J.liftInvocation
  invariant : Cache.Invariant S C.rankCard run.cache

theorem reverse_vertex (x : Entry S C.rankCard) (v : V)
    (hx : Cache.EntryValid S C.rankCard x) (hsource : x.source.1 = v) :
    x.reverse.1 = G.head (G.away v x.edge) := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete x.source x.edge x.reverse hx
  have htail : G.tail d = v := by rw [← S.place_vertex d, hd, hsource]
  have hi : G.Incident x.edge v := by simpa only [hsource] using (S.test_incident hx).1
  have haway : G.away v x.edge = d :=
    G.directed_eq_of_tail he.symm ((G.tail_away hi).trans htail.symm)
  calc
    x.reverse.1 = (S.place (Padded.reverse d)).1 := congrArg Sigma.fst hr.symm
    _ = G.head d := (S.place_vertex _).trans (Padded.tail_reverse G d)
    _ = G.head (G.away v x.edge) := by rw [haway]

theorem lifted_child (x : Entry S C.rankCard) (v : V)
    (hx : Cache.EntryValid S C.rankCard x) (hsource : x.source.1 = v) :
    ((J.liftEntry x).label, (J.liftEntry x).reverse.1) = J.liftDirected (G.away v x.edge) := by
  simp only [liftEntry, slot_vertex, liftDirected, Graph.away_edge]
  rw [reverse_vertex x v hx hsource]

end SteinerUpperBound.Matching.Padded.Presentation

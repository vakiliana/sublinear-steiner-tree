module

public import SteinerUpperBound.Matching.Padded.ScanDomination

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V] [Fintype E]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (K : J.Contract I m bits) (D : J.Deterministic I m bits K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m bits K A counter)

include D resources

theorem edge_dominates (d : Directed E) (rank : Fin C.rankCard) (ancestors : List (Directed E))
    (s : Cache S C.rankCard) (t : Runtime.State C I) (μ : Memo E) (ν : Label × Vertex → Option Bool)
    (hstate : J.StateMatch I m bits K s t) (hmemo : J.MemoMatch μ ν)
    (hs : Cache.Invariant S C.rankCard s) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Oracle.edge S J.parameters d rank ancestors s μ)
      (Runtime.edge C I (J.label d.1) (J.vertex (G.head d)) rank (ancestors.map J.liftDirected) t ν)
      (J.RunMatch I m bits K Eq) := by
  have heq := Oracle.edge.eq_def S J.parameters d rank ancestors s μ
  rw [heq, Runtime.edge]
  apply Causal.Dominates.spend m bits counter (Command.charge A) A.rate (.oracle 3) 3 _ _ _
    (by simp only [Command.charge, resources.rate, le_refl])
  have hlookup : ν (J.label d.1, J.vertex (G.head d)) = μ d := hmemo d
  rw [hlookup]
  cases hm : μ d with
  | some value =>
    exact Causal.Dominates.ret m bits counter _ _ _ _ _ ⟨rfl, hmemo, hstate, rfl, hs⟩
  | none =>
    let call := fun (x : Entry S C.rankCard) (state : Cache S C.rankCard) (memo : Memo E) =>
      if _h : x.rank.val < rank.val then
        Oracle.edge S J.parameters (G.away (G.head d) x.edge) x.rank (d :: ancestors) state memo
      else .ret ⟨false, memo, state, []⟩
    let rawCall := fun (x : Runtime.Copy C (Label := Label)) (state : Runtime.State C I)
        (memo : Label × Vertex → Option Bool) =>
      if _h : x.rank.val < rank.val then
        Runtime.edge C I x.label x.reverse.1 x.rank
          ((J.label d.1, J.vertex (G.head d)) :: ancestors.map J.liftDirected) state memo
      else .pure ⟨false, memo, state, []⟩
    have hcall (x : Entry S C.rankCard) (s' : Cache S C.rankCard) (t' : Runtime.State C I)
        (μ' : Memo E) (ν' : Label × Vertex → Option Bool)
        (hstate' : J.StateMatch I m bits K s' t') (hmemo' : J.MemoMatch μ' ν')
        (hs' : Cache.Invariant S C.rankCard s') (hsource : x.source.1 = G.head d)
        (hx : Cache.EntryValid S C.rankCard x) (hk : x.rank.val < rank.val) :
        Causal.Dominates m bits counter (Command.charge A) A.rate
          (call x s' μ') (rawCall (J.liftEntry x) t' ν') (J.RunMatch I m bits K Eq) := by
      dsimp only [call, rawCall, liftEntry, slot_vertex]
      simp only [hk, ↓reduceDIte]
      rw [reverse_vertex x (G.head d) hx hsource]
      exact edge_dominates (G.away (G.head d) x.edge) x.rank (d :: ancestors)
        s' t' μ' ν' hstate' hmemo' hs'
    apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _
      (scan_dominates J I m bits K D A counter resources call rawCall (G.head d) rank.val
        hcall 0 (C.Nstar + 1) s t μ ν hstate hmemo hs)
    intro result rawResult hresult
    have hvalue : rawResult.value.isNone = result.value.isNone := by
      rw [hresult.value]
      cases result.value <;> rfl
    apply Causal.Dominates.spend m bits counter (Command.charge A) A.rate (.oracle 3) 3 _ _ _
      (by simp only [Command.charge, resources.rate, le_refl])
    apply Causal.Dominates.ret m bits counter _ _
    refine ⟨hvalue.symm, ?_, hresult.state, ?_, hresult.invariant⟩
    · rw [hvalue]
      exact hresult.memo.update J d result.value.isNone
    · rw [hresult.calls, List.map_cons]
      rfl
termination_by rank.val
decreasing_by exact hk

theorem vertex_dominates (v : V) :
    Causal.Dominates m bits counter (Command.charge A) A.rate
      (Oracle.vertex S J.parameters v) (Runtime.vertex C I (J.vertex v))
      (J.RunMatch I m bits K (fun hit raw => raw = hit.map J.label)) := by
  let rawCall := fun (x : Runtime.Copy C (Label := Label)) (state : Runtime.State C I)
      (memo : Label × Vertex → Option Bool) =>
    Runtime.edge C I x.label x.reverse.1 x.rank [] state memo
  have hcall (x : Entry S C.rankCard) (s : Cache S C.rankCard) (t : Runtime.State C I)
      (μ : Memo E) (ν : Label × Vertex → Option Bool)
      (hstate : J.StateMatch I m bits K s t) (hmemo : J.MemoMatch μ ν)
      (hs : Cache.Invariant S C.rankCard s) (hsource : x.source.1 = v)
      (hx : Cache.EntryValid S C.rankCard x) (_hk : x.rank.val < C.rankCard) :
      Causal.Dominates m bits counter (Command.charge A) A.rate
        (Oracle.rootCall S J.parameters v x s μ) (rawCall (J.liftEntry x) t ν)
        (J.RunMatch I m bits K Eq) := by
    dsimp only [Oracle.rootCall, rawCall, liftEntry, slot_vertex]
    rw [reverse_vertex x v hx hsource]
    exact edge_dominates J I m bits K D A counter resources (G.away v x.edge) x.rank []
      s t μ ν hstate hmemo hs
  rw [Oracle.vertex, Runtime.vertex]
  apply Causal.Dominates.spend m bits counter (Command.charge A) A.rate
    (.oracle (C.rankExponent + C.sortHeight + 12)) (C.rankExponent + C.sortHeight + 12) _ _ _
    (by simp only [Command.charge, resources.rate, le_refl])
  apply Causal.Dominates.bind m bits counter (Command.charge A) A.rate _ _ _ _ _ _
    (scan_dominates J I m bits K D A counter resources (Oracle.rootCall S J.parameters v) rawCall
      v C.rankCard hcall 0 (C.Nstar + 1) (Cache.empty S C.rankCard) (Runtime.empty C I)
      (fun _ => none) (fun _ => none) (empty_match J I m bits K) (empty_memoMatch J)
      (Cache.empty_invariant S C.rankCard C.rankCard_pos))
  intro result rawResult hresult
  apply Causal.Dominates.ret m bits counter _ _
  refine ⟨?_, hresult.memo, hresult.state, hresult.calls, hresult.invariant⟩
  rw [hresult.value]
  cases result.value <;> rfl

end SteinerUpperBound.Matching.Padded.Presentation

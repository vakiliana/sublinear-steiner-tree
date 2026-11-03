module

public import SteinerUpperBound.Matching.Padded.ScanRefinement

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Oracle

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem scan_fuel_bound (ranks : E → Fin P.rankCard) (v : V) :
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).length ≤ P.Nstar + 1 := by
  have hl := candidates_length_le (G := G) (UniformOrder.order ranks) v
  have he := S.copies_le_slots
  have hn := P.size_le
  omega

theorem idealEdge_refines (d : Directed E) (rank : Fin P.rankCard) (ancestors : List (Directed E))
    (s : Cache S P.rankCard) (μ : Memo E) (ranks : E → Fin P.rankCard)
    (hn : Function.Injective ranks) (hs : Cache.Invariant S P.rankCard s)
    (hc : Cache.Consistent S P.rankCard s ranks) (hrank : ranks d.1 = rank) :
    (idealEdge S P d rank ancestors s μ ranks).forget =
      G.runEO (UniformOrder.order ranks) d ancestors μ := by
  classical
  let ρ := UniformOrder.order ranks
  let call := fun (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
      (world : E → Fin P.rankCard) =>
    if _h : x.rank.val < rank.val then
      idealEdge S P (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν world
    else ⟨false, ν, t, []⟩
  let reference : E → Memo E → Graph.Run E Bool := fun e ν =>
    if _h : ρ.index e < ρ.index d.1 then
      G.runEO ρ (G.away (G.head d) e) (d :: ancestors) ν
    else ⟨false, ν, []⟩
  have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
      (ht : Cache.Invariant S P.rankCard t) (hct : Cache.Consistent S P.rankCard t ranks)
      (hxr : ranks x.edge = x.rank) (hk : x.rank.val < rank.val) :
      RunSafe S P.rankCard ranks (call x t ν ranks) ∧ (call x t ν ranks).forget = reference x.edge ν := by
    have hnum : ranks x.edge < ranks d.1 := by
      rw [hxr, hrank]
      exact hk
    have hord : ρ.index x.edge < ρ.index d.1 := (UniformOrder.order_lt ranks hn _ _).mpr hnum
    dsimp only [call, reference]
    simp only [hk, hord, ↓reduceDIte]
    exact ⟨idealEdge_safe S P _ _ _ _ _ _ ht hct,
      idealEdge_refines (G.away (G.head d) x.edge) x.rank (d :: ancestors) t ν ranks hn ht hct hxr⟩
  have hscan := idealScan_refines S P call reference ranks hn (G.head d) rank.val
    hcall 0 (P.Nstar + 1) s μ hs hc (by simpa only [zero_add] using scan_fuel_bound S P ranks (G.head d))
  have hprefix :
      ((G.candidates ρ (Fintype.card E) (G.head d)).drop 0).takeWhile
          (fun e => (ranks e).val < rank.val) =
        G.candidates ρ (ρ.index d.1) (G.head d) := by
    simp only [List.drop_zero, ← hrank]
    exact candidates_numeric_prefix P.rankCard ranks hn (G.head d) d.1
  rw [hprefix] at hscan
  rw [idealEdge, Graph.runEO]
  cases hm : μ d with
  | some b => rfl
  | none =>
    have he := congrArg (fun r : Graph.Run E (Option E) =>
      (⟨r.value.isNone, Function.update r.memo d (some r.value.isNone),
        ⟨d, ancestors, false⟩ :: r.calls⟩ : Graph.Run E Bool)) hscan
    simpa only [LocalRun.forget, LocalRun.forgetScan, Option.isNone_map] using he
termination_by rank.val
decreasing_by exact hk

theorem idealVertex_refines (v : V) (ranks : E → Fin P.rankCard) (hn : Function.Injective ranks) :
    (idealVertex S P v ranks).forget = G.vertexOracle (UniformOrder.order ranks) v := by
  let reference := fun e μ => G.runEO (UniformOrder.order ranks) (G.away v e) [] μ
  have hcall (x : Entry S P.rankCard) (t : Cache S P.rankCard) (ν : Memo E)
      (ht : Cache.Invariant S P.rankCard t) (hc : Cache.Consistent S P.rankCard t ranks)
      (hr : ranks x.edge = x.rank) (_hk : x.rank.val < P.rankCard) :
      RunSafe S P.rankCard ranks (idealRootCall S P v x t ν ranks) ∧
        (idealRootCall S P v x t ν ranks).forget = reference x.edge ν :=
    ⟨idealEdge_safe S P _ _ _ _ _ _ ht hc,
      idealEdge_refines S P (G.away v x.edge) x.rank [] t ν ranks hn ht hc hr⟩
  have hscan := idealScan_refines S P (idealRootCall S P v) reference ranks hn v P.rankCard hcall
    0 (P.Nstar + 1) (Cache.empty S P.rankCard) (fun _ => none)
    (Cache.empty_invariant S P.rankCard P.rankCard_pos) (Cache.empty_consistent S P.rankCard ranks)
    (by simpa only [zero_add] using scan_fuel_bound S P ranks v)
  simp only [List.drop_zero, candidates_full_numeric] at hscan
  unfold idealVertex
  rw [LocalRun.forget_mapEntries]
  exact hscan

theorem idealVertex_correct (v : V) (ranks : E → Fin P.rankCard) (hn : Function.Injective ranks) :
    (idealVertex S P v ranks).value = (G.vertexOracle (UniformOrder.order ranks) v).value := by
  have h := congrArg Graph.Run.value (idealVertex_refines S P v ranks hn)
  rw [LocalRun.forget_value] at h
  exact h

end SteinerUpperBound.Matching.Padded.Oracle

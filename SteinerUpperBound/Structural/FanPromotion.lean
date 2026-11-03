module

public import SteinerUpperBound.Structural.Fans

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

theorem promote_primary_adj (C : Cherry S v) :
    C.promote.graph.Adj (retained S C.center v C.trunk.ne)
      (retained S C.center C.primary C.center_ne_primary.symm) := by
  change ((S.graph.deleteEdges {s(C.center, C.secondary)} ⊔ SimpleGraph.edge C.primary C.secondary).deleteEdges
    {s(C.center, v)} ⊔ SimpleGraph.edge C.primary v).Adj v C.primary
  apply Or.inr
  exact (SimpleGraph.edge_adj C.primary v v C.primary).mpr
    ⟨Or.inr ⟨rfl, rfl⟩, C.primary_ne_attachment.symm⟩

theorem promote_neighbor_cases (C : Cherry S v) (z : ↥C.promote.vertices)
    (h : C.promote.graph.Adj (retained S C.center v C.trunk.ne) z) :
    (S.graph.Adj v (eraseEmbedding S C.center z) ∧ eraseEmbedding S C.center z ≠ C.center) ∨
      eraseEmbedding S C.center z = C.primary := by
  have hvp : v ≠ C.primary := C.primary_ne_attachment.symm
  have hvq : v ≠ C.secondary := C.secondary_ne_attachment.symm
  change ((S.graph.deleteEdges {s(C.center, C.secondary)} ⊔ SimpleGraph.edge C.primary C.secondary).deleteEdges
    {s(C.center, v)} ⊔ SimpleGraph.edge C.primary v).Adj v (eraseEmbedding S C.center z) at h
  rcases h with h | h
  · have hh := (SimpleGraph.deleteEdges_adj.mp h).1
    rcases hh with hh | hh
    · refine Or.inl ⟨(SimpleGraph.deleteEdges_adj.mp hh).1, ?_⟩
      intro he
      exact (Finset.mem_erase.mp z.property).1 (congrArg (fun x : ↥S.vertices => (x : V)) he)
    · rcases (SimpleGraph.edge_adj C.primary C.secondary _ _).mp hh with ⟨h | h, _⟩
      · exact False.elim (hvp h.1)
      · exact False.elim (hvq h.1)
  · rcases (SimpleGraph.edge_adj C.primary v _ _).mp h with ⟨h | h, _⟩
    · exact False.elim (hvp h.1)
    · exact Or.inr h.2

noncomputable abbrev transportSibling (C : Cherry S v) (R : Limb S v)
    (hr : R.stem ≠ C.center) :
    Limb C.promote (retained S C.center v C.trunk.ne) := by
  cases R with
  | direct x hv hx h =>
    exact Limb.direct (retained S C.center x (fun he => C.center_nonterminal (he ▸ hx)))
      hv hx (C.promote_adj_survives v x C.trunk.ne _ h)
  | cherry D =>
    exact Limb.cherry (C.transport D C.trunk.ne D.trunk.ne.symm hr)

theorem transportSibling_stem (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center) :
    (C.transportSibling R hr).stem = retained S C.center R.stem hr := by
  cases R <;> rfl

theorem transportSibling_primary_val (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center) :
    ((C.transportSibling R hr).primary : V) = (R.primary : V) := by
  cases R <;> rfl

theorem transportSibling_stem_val (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center) :
    ((C.transportSibling R hr).stem : V) = (R.stem : V) := by
  cases R <;> rfl

theorem primary_ne_sibling_stem (C : Cherry S v) (R : Limb S v)
    (hout : (C.primary : V) ∉ R.region) : C.primary ≠ R.stem := by
  cases R with
  | direct x hv hx h =>
    intro he
    exact hout (he ▸ (Limb.direct x hv hx h).primary_mem_region)
  | cherry D =>
    intro he
    change C.primary = D.center at he
    exact D.center_nonterminal (he ▸ C.primary_terminal)

end Cherry

namespace Fan

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

noncomputable abbrev swap (F : Fan S parent v) : Fan S parent v where
  parent_nonterminal := F.parent_nonterminal
  parent_edge := F.parent_edge
  left := F.right
  right := F.left
  parent_ne_left := F.parent_ne_right
  parent_ne_right := F.parent_ne_left
  stems_ne := F.stems_ne.symm
  neighbors := by
    intro z hz
    have h := F.neighbors z hz
    tauto

noncomputable abbrev promoteLeft (F : Fan S parent v) (C : Cherry S v) (hl : F.left = Limb.cherry C) :
    Fan C.promote
      (retained S C.center parent (by simpa only [hl, Limb.stem] using F.parent_ne_left))
      (retained S C.center v C.trunk.ne) := by
  have hpc : parent ≠ C.center := by simpa only [hl, Limb.stem] using F.parent_ne_left
  have hrc : F.right.stem ≠ C.center := by simpa only [hl, Limb.stem] using F.stems_ne.symm
  let R' := C.transportSibling F.right hrc
  refine
    { parent_nonterminal := F.parent_nonterminal
      parent_edge := C.promote_adj_survives parent v hpc C.trunk.ne F.parent_edge
      left := Limb.direct
        (retained S C.center C.primary C.center_ne_primary.symm)
        C.attachment_nonterminal C.primary_terminal C.promote_primary_adj
      right := R'
      parent_ne_left := ?_
      parent_ne_right := ?_
      stems_ne := ?_
      neighbors := ?_ }
  · intro h
    have hh := congrArg (fun z : ↥C.promote.vertices => (z : V)) h
    exact F.parent_nonterminal (hh ▸ C.primary_terminal)
  · intro h
    have hh := congrArg (fun z : ↥C.promote.vertices => (z : V)) h
    change (parent : V) = (R'.stem : V) at hh
    rw [C.transportSibling_stem_val] at hh
    exact F.parent_ne_right (Subtype.ext hh)
  · intro h
    have hh := congrArg (fun z : ↥C.promote.vertices => (z : V)) h
    change (C.primary : V) = (R'.stem : V) at hh
    rw [C.transportSibling_stem_val] at hh
    have hout : (C.primary : V) ∉ F.right.region := by
      simpa only [hl, Limb.primary] using F.pair.left_outside
    exact C.primary_ne_sibling_stem F.right hout (Subtype.ext hh)
  · intro z hz
    rcases C.promote_neighbor_cases z hz with ⟨hold, hne⟩ | he
    · have hcases := F.neighbors (eraseEmbedding S C.center z) hold
      simp only [hl, Limb.stem] at hcases
      rcases hcases with h | h | h
      · exact Or.inl (Subtype.ext (by
          simpa only [eraseEmbedding_val, retained_val] using
            congrArg (fun x : ↥S.vertices => (x : V)) h))
      · exact False.elim (hne h)
      · apply Or.inr
        apply Or.inr
        apply Subtype.ext
        change (z : V) = (R'.stem : V)
        rw [C.transportSibling_stem_val]
        simpa only [eraseEmbedding_val, Limb.stem] using congrArg (fun x : ↥S.vertices => (x : V)) h
    · apply Or.inr
      apply Or.inl
      apply Subtype.ext
      simpa only [eraseEmbedding_val, retained_val, Limb.stem] using
        congrArg (fun x : ↥S.vertices => (x : V)) he

end Fan

end SteinerUpperBound.Structural.Tree

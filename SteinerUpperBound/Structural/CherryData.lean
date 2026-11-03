module

public import SteinerUpperBound.Structural.FanPromotion

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem ambient_adj_iff (S : TreeGeometry.TreeSolution I) (x y : ↥S.vertices) :
    S.ambient.Adj x y ↔ S.graph.Adj x y := by
  constructor
  · intro h
    change (S.graph.map Subtype.val).Adj (x : V) (y : V) at h
    obtain ⟨_, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' Subtype.val S.graph _ _).mp h
    have hax : a = x := Subtype.ext ha
    have hby : b = y := Subtype.ext hb
    simpa only [hax, hby] using hab
  · intro h
    exact SimpleGraph.map_adj_apply' h (Subtype.val_injective.ne h.ne)

structure CherryData (I : Instance V) where
  attachment : V
  center : V
  primary : V
  secondary : V
  attachment_nonterminal : attachment ∉ I.terminals
  center_nonterminal : center ∉ I.terminals
  primary_terminal : primary ∈ I.terminals
  secondary_terminal : secondary ∈ I.terminals
  ports_ne : primary ≠ secondary
  ordered : I.distance center primary ≤ I.distance center secondary

namespace CherryData

structure OnTree (A : CherryData I) (S : TreeGeometry.TreeSolution I) : Prop where
  attachment_mem : A.attachment ∈ S.vertices
  center_mem : A.center ∈ S.vertices
  trunk : S.ambient.Adj A.attachment A.center
  primary_arm : S.ambient.Adj A.center A.primary
  secondary_arm : S.ambient.Adj A.center A.secondary
  neighbors : ∀ z, S.ambient.Adj A.center z →
    z = A.attachment ∨ z = A.primary ∨ z = A.secondary

noncomputable abbrev selected (A : CherryData I) {S : TreeGeometry.TreeSolution I}
    (h : A.OnTree S) : Cherry S (⟨A.attachment, h.attachment_mem⟩ : ↥S.vertices) where
  center := ⟨A.center, h.center_mem⟩
  primary := ⟨A.primary, S.contains A.primary_terminal⟩
  secondary := ⟨A.secondary, S.contains A.secondary_terminal⟩
  attachment_nonterminal := A.attachment_nonterminal
  center_nonterminal := A.center_nonterminal
  primary_terminal := A.primary_terminal
  secondary_terminal := A.secondary_terminal
  ports_ne := fun he => A.ports_ne (congrArg (fun z : ↥S.vertices => (z : V)) he)
  trunk := (ambient_adj_iff S _ _).mp h.trunk
  primary_arm := (ambient_adj_iff S _ _).mp h.primary_arm
  secondary_arm := (ambient_adj_iff S _ _).mp h.secondary_arm
  neighbors := by
    intro z hz
    have hh := h.neighbors z ((ambient_adj_iff S _ _).mpr hz)
    exact hh.imp Subtype.ext (fun h => h.imp Subtype.ext Subtype.ext)
  ordered := A.ordered

noncomputable def delta (A : CherryData I) (w : Sym2 V → ℝ) : ℝ :=
  w s(A.primary, A.secondary) + w s(A.primary, A.attachment) -
    w s(A.center, A.secondary) - w s(A.center, A.attachment) - w s(A.center, A.primary)

noncomputable def addedGraph (A : CherryData I) : SimpleGraph V :=
  SimpleGraph.edge A.primary A.secondary ⊔ SimpleGraph.edge A.primary A.attachment

end CherryData

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable abbrev data (C : Cherry S v) : CherryData I where
  attachment := v
  center := C.center
  primary := C.primary
  secondary := C.secondary
  attachment_nonterminal := C.attachment_nonterminal
  center_nonterminal := C.center_nonterminal
  primary_terminal := C.primary_terminal
  secondary_terminal := C.secondary_terminal
  ports_ne := fun h => C.ports_ne (Subtype.ext h)
  ordered := C.ordered

theorem data_onTree (C : Cherry S v) : C.data.OnTree S := by
  refine ⟨v.property, C.center.property, (ambient_adj_iff S _ _).mpr C.trunk,
    (ambient_adj_iff S _ _).mpr C.primary_arm, (ambient_adj_iff S _ _).mpr C.secondary_arm, ?_⟩
  intro z hz
  change (S.graph.map Subtype.val).Adj (C.center : V) z at hz
  obtain ⟨_, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' Subtype.val S.graph _ _).mp hz
  have he : a = C.center := Subtype.ext ha
  subst a
  rcases C.neighbors b hab with h | h | h
  · exact Or.inl (hb.symm.trans (congrArg Subtype.val h))
  · exact Or.inr (Or.inl (hb.symm.trans (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (hb.symm.trans (congrArg Subtype.val h)))

theorem data_selected (A : CherryData I) (h : A.OnTree S) : (A.selected h).data = A := by
  cases A
  rfl

theorem transport_data {w : ↥S.vertices} (C : Cherry S v) (D : Cherry S w)
    (hw : w ≠ C.center) (hdv : D.center ≠ v) (hdc : D.center ≠ C.center) :
    (C.transport D hw hdv hdc).data = D.data := rfl

theorem promote_ambient_survives (C : Cherry S v) {x y : V}
    (hx : x ≠ (C.center : V)) (hy : y ≠ (C.center : V)) (hxy : S.ambient.Adj x y) :
    C.promote.ambient.Adj x y := by
  change (S.graph.map Subtype.val).Adj x y at hxy
  obtain ⟨hne, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' Subtype.val S.graph _ _).mp hxy
  have hac : a ≠ C.center := fun h => hx (ha.symm.trans (congrArg Subtype.val h))
  have hbc : b ≠ C.center := fun h => hy (hb.symm.trans (congrArg Subtype.val h))
  have hnew := C.promote_adj_survives a b hac hbc hab
  have hmap := SimpleGraph.map_adj_apply' (f := (Subtype.val : ↥C.promote.vertices → V))
    hnew (by simpa only [retained_val, ha, hb] using hne)
  simpa only [retained_val, ha, hb, TreeGeometry.TreeSolution.ambient] using hmap

theorem promote_primary_ambient (C : Cherry S v) :
    C.promote.ambient.Adj v C.primary := by
  have hne : (v : V) ≠ (C.primary : V) := fun h => C.primary_ne_attachment.symm (Subtype.ext h)
  exact SimpleGraph.map_adj_apply' (f := (Subtype.val : ↥C.promote.vertices → V))
    C.promote_primary_adj hne

end Cherry

theorem CherryData.onTree_promote (A : CherryData I) {S : TreeGeometry.TreeSolution I}
    {v : ↥S.vertices} (C : Cherry S v) (hA : A.OnTree S)
    (hattach : A.attachment ≠ (C.center : V)) (hcenter : A.center ≠ (v : V))
    (hcenters : A.center ≠ (C.center : V)) : A.OnTree C.promote := by
  let D := A.selected hA
  have h1 : (⟨A.attachment, hA.attachment_mem⟩ : ↥S.vertices) ≠ C.center :=
    fun h => hattach (congrArg Subtype.val h)
  have h2 : D.center ≠ v := fun h => hcenter (congrArg Subtype.val h)
  have h3 : D.center ≠ C.center := fun h => hcenters (congrArg Subtype.val h)
  have hd := (C.transport D h1 h2 h3).data_onTree
  rw [Cherry.transport_data, Cherry.data_selected] at hd
  exact hd

end SteinerUpperBound.Structural.Tree

module

public import SteinerUpperBound.Structural.TerminationGeometry
public import SteinerUpperBound.Structural.PromotionBounds

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem nonterminal_of_steinerEdges (S : TreeGeometry.TreeSolution I)
    (hpos : 0 < (steinerEdges S).card) : ∃ v : ↥S.vertices, (v : V) ∉ I.terminals := by
  classical
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have hf := Finset.mem_filter.mp he
  rcases e with ⟨x, y⟩
  have hxy : S.graph.Adj x y := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hf.1
  have hnot : s((x : V), (y : V)) ∉ (Network.completeOn I.terminals).edgeSet := by
    simpa only [Sym2.map_mk] using hf.2
  by_cases hx : (x : V) ∈ I.terminals
  · refine ⟨y, ?_⟩
    intro hy
    exact hnot ((Network.completeOn_adj _ _ _).mpr ⟨Subtype.val_injective.ne hxy.ne, hx, hy⟩)
  · exact ⟨x, hx⟩

theorem terminalOnly_of_steinerEdges_zero (S : TreeGeometry.TreeSolution I)
    (hzero : (steinerEdges S).card = 0) : Network.TerminalOnly I.terminals S.ambient := by
  classical
  intro x y hxy
  change (S.graph.map Subtype.val).Adj x y at hxy
  obtain ⟨hne, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' Subtype.val S.graph x y).mp hxy
  by_cases hT : s((a : V), (b : V)) ∈ (Network.completeOn I.terminals).edgeSet
  · exact ((Network.completeOn_adj _ _ _).mp hT).2
  · have hm : s(a, b) ∈ steinerEdges S := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hab
      · simpa only [Sym2.map_mk] using hT
    have he := Finset.card_eq_zero.mp hzero
    rw [he] at hm
    exact False.elim (by simpa using hm)

theorem mst_le_potential_of_terminal (S : TreeGeometry.TreeSolution I)
    (hzero : (steinerEdges S).card = 0) : I.mst ≤ potential S := by
  have hT := terminalOnly_of_steinerEdges_zero S hzero
  have hcost : potential S = S.cost := by
    unfold potential TreeGeometry.TreeSolution.cost GraphCost.cost
    apply Finset.sum_congr rfl
    intro e he
    rcases e with ⟨x, y⟩
    have hxy : S.graph.Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hmem := hT x y ((ambient_adj_iff S x y).mpr hxy)
    simp only [Sym2.map_mk, potentialWeight_mk, potentialDistance, hmem.1, hmem.2,
      and_self, ↓reduceIte, Instance.weight_mk]
  calc
    I.mst ≤ GraphCost.cost I.weight S.ambient := I.mst_le _ S.ambient_feasible hT
    _ = S.cost := S.cost_ambient
    _ = potential S := hcost.symm

def RootedFringe.Eligible {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}
    (F : RootedFringe S parent v) : Prop :=
  F.fan.Small ∨ delta0 * F.fan.pair.totalLength ≤ I.distance parent v

theorem event_available (S : TreeGeometry.TreeSolution I) (hc : S.IsClean) (hred : Reduced S)
    (hT : I.terminals.Nonempty) (hpos : 0 < (steinerEdges S).card) :
    Nonempty (ShortStar S) ∨ ∃ parent v : ↥S.vertices, ∃ F : RootedFringe S parent v, F.Eligible := by
  classical
  by_cases hstar : Nonempty (ShortStar S)
  · exact Or.inl hstar
  · apply Or.inr
    by_contra hnone
    have hshort : ∀ parent v : ↥S.vertices, ∀ F : RootedFringe S parent v,
        I.distance parent v < delta0 * F.fan.pair.totalLength := by
      intro parent v F
      by_contra h
      exact hnone ⟨parent, v, F, Or.inr (le_of_not_gt h)⟩
    obtain ⟨r, hr⟩ := hT
    let r' : ↥S.vertices := ⟨r, S.contains hr⟩
    have hclean := rooted_clean S hc
    have hno := no_zero_core_star_of_no_star S hstar
    have hNN : ∃ v : ↥S.vertices, v ∉ selectedTerminals S := by
      obtain ⟨v, hv⟩ := nonterminal_of_steinerEdges S hpos
      exact ⟨v, fun h => hv ((mem_selectedTerminals S v).mp h)⟩
    obtain ⟨v, w, z, hv, hw, hz, hwz, hwNT, hw2, hzType⟩ :=
      Rooted.height_three_fork S.graph r' (selectedTerminals S) S.isTree
        ((mem_selectedTerminals S r').mpr hr) hclean hno hNN
    have hvT : (v : V) ∉ I.terminals := fun h => hv ((mem_selectedTerminals S v).mpr h)
    have hwT : (w : V) ∉ I.terminals := fun h => hwNT ((mem_selectedTerminals S w).mpr h)
    have hwData := (Rooted.mem_children S.graph r' v w).mp hw
    obtain ⟨F⟩ := fringe_of_height_two S hc hstar r' hr v w hvT hwT hwData.1 hwData.2.symm hw2
    rcases hzType with hzL | ⟨hzNT, hz2⟩
    · obtain ⟨L, hL⟩ := limb_of_neighbor S v z hvT hzL
      have hst : L.stem ≠ w := by rw [hL]; exact Ne.symm hwz
      exact hstar (star_of_one_short_parent F.fan L hst hred (hshort v w F))
    · have hzT : (z : V) ∉ I.terminals := fun h => hzNT ((mem_selectedTerminals S z).mpr h)
      have hzData := (Rooted.mem_children S.graph r' v z).mp hz
      obtain ⟨H⟩ := fringe_of_height_two S hc hstar r' hr v z hvT hzT hzData.1 hzData.2.symm hz2
      exact hstar (star_of_two_short_parents F.fan H.fan hwz hred (hshort v w F) (hshort v z H))

end SteinerUpperBound.Structural.Tree

module

public import SteinerUpperBound.Structural.FringeEvidence
public import SteinerUpperBound.Structural.RegionOperations

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable def edgeWeight (L : Limb S v) (w : Sym2 V → ℝ) : ℝ :=
  match L with
  | .direct x _ _ _ => w s((v : V), (x : V))
  | .cherry C => w s((v : V), (C.center : V)) +
      w s((C.center : V), (C.primary : V)) + w s((C.center : V), (C.secondary : V))

noncomputable def siblingWeight (L : Limb S v) (w : Sym2 V → ℝ) : ℝ :=
  match L with
  | .direct _ _ _ _ => 0
  | .cherry C => w s((C.primary : V), (C.secondary : V))

noncomputable def siblingGraph (L : Limb S v) : SimpleGraph V :=
  match L with
  | .direct _ _ _ _ => ⊥
  | .cherry C => SimpleGraph.edge C.primary C.secondary

noncomputable def ports (L : Limb S v) : Finset V :=
  match L with
  | .direct x _ _ _ => {(x : V)}
  | .cherry C => {(C.primary : V), (C.secondary : V)}

theorem primary_mem_ports (L : Limb S v) : (L.primary : V) ∈ L.ports := by
  cases L <;> simp [ports, primary]

theorem ports_terminal (L : Limb S v) : L.ports ⊆ I.terminals := by
  cases L with
  | direct x hv hx h => simpa [ports] using hx
  | cherry C =>
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact C.primary_terminal
    · have he := Finset.mem_singleton.mp hx
      simpa only [he] using C.secondary_terminal

theorem edgeWeight_potential (L : Limb S v) :
    L.edgeWeight (potentialWeight I) = chi * L.cost := by
  cases L with
  | direct x hv hx h => simp [edgeWeight, cost, potentialWeight_mk, potentialDistance, hv]
  | cherry C =>
    simp only [edgeWeight, cost, potentialWeight_mk, potentialDistance, C.attachment_nonterminal,
      C.center_nonterminal, false_and, ↓reduceIte]
    ring

theorem edgeWeight_nonneg (L : Limb S v) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ L.edgeWeight w := by
  cases L with
  | direct x hv hx h => exact hw _
  | cherry C => exact add_nonneg (add_nonneg (hw _) (hw _)) (hw _)

theorem siblingWeight_potential (L : Limb S v) :
    L.siblingWeight (potentialWeight I) = L.siblingWeight I.weight := by
  cases L with
  | direct x hv hx h => rfl
  | cherry C =>
    simp [siblingWeight, potentialWeight_mk, potentialDistance, C.primary_terminal, C.secondary_terminal]

theorem siblingWeight_nonterminal (L : Limb S v) :
    L.siblingWeight (nonterminalWeight I) = 0 := by
  cases L with
  | direct x hv hx h => rfl
  | cherry C =>
    simp [siblingWeight, nonterminalWeight_mk, nonterminalDistance, C.primary_terminal]

theorem siblingWeight_count (L : Limb S v) :
    L.siblingWeight (steinerCountWeight I) = 0 := by
  cases L with
  | direct x hv hx h => rfl
  | cherry C =>
    have hne : (C.primary : V) ≠ (C.secondary : V) := fun h => C.ports_ne (Subtype.ext h)
    simp [siblingWeight, steinerCountWeight, SimpleGraph.mem_edgeSet,
      Network.completeOn_adj, hne, C.primary_terminal, C.secondary_terminal]

theorem edgeWeight_count_ge_one (L : Limb S v) :
    1 ≤ L.edgeWeight (steinerCountWeight I) := by
  cases L with
  | direct x hv hx h =>
    simp [edgeWeight, steinerCountWeight_incident I hv]
  | cherry C =>
    simp [edgeWeight, steinerCountWeight_incident I C.attachment_nonterminal,
      steinerCountWeight_incident I C.center_nonterminal]

theorem fan_barrier_contribution (L : Limb S v) :
    b0 * L.length + L.length + L.siblingWeight I.weight ≤ chi * L.cost := by
  cases L with
  | direct x hv hx h =>
    have hn := I.distance_nonneg v x
    change b0 * I.distance v x + I.distance v x + 0 ≤ chi * I.distance v x
    norm_num [b0, p, chi, e0]
    linarith
  | cherry C =>
    have ht := I.distance_triangle (C.primary : V) C.center C.secondary
    rw [I.distance_comm (C.primary : V) C.center] at ht
    have hz := I.distance_nonneg v C.center
    have ho := C.ordered
    change b0 * (I.distance v C.center + I.distance C.center C.primary) +
      (I.distance v C.center + I.distance C.center C.primary) +
      I.distance C.primary C.secondary ≤
      chi * (I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary)
    norm_num [b0, p, chi, e0]
    linarith

theorem potential_reconnection_bound (L : Limb S v) :
    L.siblingWeight (potentialWeight I) + potentialWeight I s((v : V), (L.primary : V)) -
      L.edgeWeight (potentialWeight I) ≤ (2 - chi) * L.longerArm := by
  rw [edgeWeight_potential]
  cases L with
  | direct x hv hx h =>
    simp [siblingWeight, primary, potentialWeight_mk, potentialDistance, hv, cost, longerArm]
  | cherry C =>
    simp only [siblingWeight, primary, potentialWeight_mk, potentialDistance,
      C.primary_terminal, C.secondary_terminal, C.attachment_nonterminal, and_self,
      false_and, and_false, ↓reduceIte, cost, longerArm]
    have h1 := I.distance_triangle (C.primary : V) C.center C.secondary
    rw [I.distance_comm (C.primary : V) C.center] at h1
    have h2 := I.distance_triangle (v : V) C.center C.primary
    have hchi : 0 ≤ chi := by norm_num [chi, e0]
    nlinarith [C.ordered, mul_le_mul_of_nonneg_left h2 hchi]

end Limb

structure Fan (S : TreeGeometry.TreeSolution I) (parent v : ↥S.vertices) where
  parent_nonterminal : (parent : V) ∉ I.terminals
  parent_edge : S.graph.Adj parent v
  left : Limb S v
  right : Limb S v
  parent_ne_left : parent ≠ left.stem
  parent_ne_right : parent ≠ right.stem
  stems_ne : left.stem ≠ right.stem
  neighbors : ∀ z, S.graph.Adj v z → z = parent ∨ z = left.stem ∨ z = right.stem

namespace Fan

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

noncomputable abbrev region (F : Fan S parent v) : Finset V := Tree.region S parent v

noncomputable def localVertices (F : Fan S parent v) : Finset V :=
  insert (v : V) (F.left.ports ∪ F.right.ports)

noncomputable def internalCost (F : Fan S parent v) : ℝ :=
  F.left.siblingWeight I.weight + F.right.siblingWeight I.weight +
    I.distance F.left.primary F.right.primary

theorem center_nonterminal (F : Fan S parent v) : (v : V) ∉ I.terminals :=
  F.left.attachment_nonterminal

theorem limbs_disjoint (F : Fan S parent v) : Disjoint F.left.region F.right.region := by
  apply disjoint_regions_of_outside S v F.left.stem v F.right.stem F.left.stem_adj F.right.stem_adj
  · intro h
    rcases Sym2.eq_iff.mp h with ⟨_, h⟩ | ⟨h, h'⟩
    · exact F.stems_ne h
    · exact F.left.stem_adj.ne (h'.symm)
  · exact region_attachment_outside S v F.right.stem F.right.stem_adj
  · exact region_attachment_outside S v F.left.stem F.left.stem_adj

noncomputable abbrev pair (F : Fan S parent v) : LimbPair S v :=
  ⟨F.left, F.right, F.limbs_disjoint⟩

theorem ports_ne (F : Fan S parent v) : F.left.primary ≠ F.right.primary := by
  intro h
  exact F.pair.right_outside (h ▸ F.left.primary_mem_region)

theorem limb_stem_in_region (F : Fan S parent v) (L : Limb S v) (hp : parent ≠ L.stem) :
    (L.stem : V) ∈ F.region := by
  apply (Tree.mem_region S parent v L.stem).mpr
  apply SimpleGraph.Adj.reachable
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨L.stem_adj, ?_⟩
  rw [Set.mem_singleton_iff]
  intro he
  rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
  · exact F.parent_edge.ne h.symm
  · exact hp h.symm

theorem limb_primary_in_region (F : Fan S parent v) (L : Limb S v) (hp : parent ≠ L.stem) :
    (L.primary : V) ∈ F.region := by
  cases L with
  | direct x hv hx h => exact F.limb_stem_in_region (.direct x hv hx h) hp
  | cherry C =>
    have hstem := F.limb_stem_in_region (.cherry C) hp
    have hvr : (S.graph.deleteEdges {s(parent, v)}).Reachable v C.center :=
      (Tree.mem_region S parent v C.center).mp hstem
    have harm : (S.graph.deleteEdges {s(parent, v)}).Adj C.center C.primary := by
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨C.primary_arm, ?_⟩
      rw [Set.mem_singleton_iff]
      intro he
      rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨_, h⟩
      · exact F.center_nonterminal (h ▸ C.primary_terminal)
      · exact F.parent_nonterminal (h ▸ C.primary_terminal)
    exact (Tree.mem_region S parent v C.primary).mpr (hvr.trans harm.reachable)

theorem cherry_secondary_in_region (F : Fan S parent v) (C : Cherry S v)
    (hp : parent ≠ C.center) : (C.secondary : V) ∈ F.region := by
  have hstem := F.limb_stem_in_region (.cherry C) hp
  have hvr : (S.graph.deleteEdges {s(parent, v)}).Reachable v C.center :=
    (Tree.mem_region S parent v C.center).mp hstem
  have harm : (S.graph.deleteEdges {s(parent, v)}).Adj C.center C.secondary := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨C.secondary_arm, ?_⟩
    rw [Set.mem_singleton_iff]
    intro he
    rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨_, h⟩
    · exact F.center_nonterminal (h ▸ C.secondary_terminal)
    · exact F.parent_nonterminal (h ▸ C.secondary_terminal)
  exact (Tree.mem_region S parent v C.secondary).mpr (hvr.trans harm.reachable)

theorem ports_in_region (F : Fan S parent v) (L : Limb S v) (hp : parent ≠ L.stem) :
    L.ports ⊆ F.region := by
  cases L with
  | direct x hv hx h =>
    intro z hz
    have he := Finset.mem_singleton.mp hz
    subst z
    exact F.limb_primary_in_region (.direct x hv hx h) hp
  | cherry C =>
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hz
    · simpa only [he, Limb.primary] using F.limb_primary_in_region (.cherry C) hp
    · have he := Finset.mem_singleton.mp hz
      simpa only [he] using F.cherry_secondary_in_region C hp

theorem localVertices_in_region (F : Fan S parent v) : F.localVertices ⊆ F.region := by
  intro x hx
  rcases Finset.mem_insert.mp hx with he | hx
  · subst x
    exact (Tree.mem_region S parent v v).mpr (SimpleGraph.Reachable.refl v)
  · rcases Finset.mem_union.mp hx with hx | hx
    · exact F.ports_in_region F.left F.parent_ne_left hx
    · exact F.ports_in_region F.right F.parent_ne_right hx

end Fan

end SteinerUpperBound.Structural.Tree

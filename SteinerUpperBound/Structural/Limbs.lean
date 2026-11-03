module

public import SteinerUpperBound.Structural.CherryElimination

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

inductive Limb (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
  | direct (x : ↥S.vertices) (hv : (v : V) ∉ I.terminals)
      (hx : (x : V) ∈ I.terminals) (h : S.graph.Adj v x)
  | cherry (C : Cherry S v)

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

def primary (L : Limb S v) : ↥S.vertices :=
  match L with
  | .direct x _ _ _ => x
  | .cherry C => C.primary

def stem (L : Limb S v) : ↥S.vertices :=
  match L with
  | .direct x _ _ _ => x
  | .cherry C => C.center

noncomputable def length (L : Limb S v) : ℝ :=
  match L with
  | .direct x _ _ _ => I.distance v x
  | .cherry C => I.distance v C.center + I.distance C.center C.primary

noncomputable def cost (L : Limb S v) : ℝ :=
  match L with
  | .direct x _ _ _ => I.distance v x
  | .cherry C => I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary

noncomputable def longerArm (L : Limb S v) : ℝ :=
  match L with
  | .direct _ _ _ _ => 0
  | .cherry C => I.distance C.center C.secondary

noncomputable def region (L : Limb S v) : Finset V :=
  Tree.region S v L.stem

theorem attachment_nonterminal (L : Limb S v) : (v : V) ∉ I.terminals := by
  cases L with
  | direct x hv _ _ => exact hv
  | cherry C => exact C.attachment_nonterminal

theorem primary_terminal (L : Limb S v) : (L.primary : V) ∈ I.terminals := by
  cases L with
  | direct x _ hx _ => exact hx
  | cherry C => exact C.primary_terminal

theorem stem_adj (L : Limb S v) : S.graph.Adj v L.stem := by
  cases L with
  | direct x _ _ h => exact h
  | cherry C => exact C.trunk

theorem length_pos (L : Limb S v) : 0 < L.length := by
  cases L with
  | direct x _ _ h =>
    exact I.distance_pos v x (Subtype.val_injective.ne h.ne)
  | cherry C =>
    exact add_pos (I.distance_pos v C.center (Subtype.val_injective.ne C.trunk.ne))
      (I.distance_pos C.center C.primary (Subtype.val_injective.ne C.primary_arm.ne))

theorem primary_mem_region (L : Limb S v) : (L.primary : V) ∈ L.region := by
  apply (Tree.mem_region S v L.stem L.primary).mpr
  cases L with
  | direct x _ _ _ => exact SimpleGraph.Reachable.refl _
  | cherry C =>
    exact (SimpleGraph.deleteEdges_adj.mpr
      ⟨C.primary_arm, by simpa only [stem, Set.mem_singleton_iff] using C.primary_edge_ne_trunk⟩).reachable

theorem primary_distance_le (L : Limb S v) : I.distance v L.primary ≤ L.length := by
  cases L with
  | direct x _ _ _ => exact le_rfl
  | cherry C => exact I.distance_triangle v C.center C.primary

theorem length_le_cost (L : Limb S v) : L.length ≤ L.cost := by
  cases L with
  | direct x _ _ _ => exact le_rfl
  | cherry C => exact le_add_of_nonneg_right (I.distance_nonneg C.center C.secondary)

theorem cost_le_length_factor (L : Limb S v) (hred : Reduced S) :
    L.cost ≤ (1 + 1 / (chi - 1)) * L.length := by
  have hchi : 0 < chi - 1 := by norm_num [chi, e0]
  cases L with
  | direct x hv hx h =>
    change I.distance v x ≤ (1 + 1 / (chi - 1)) * I.distance v x
    nlinarith [I.distance_nonneg v x, one_div_pos.mpr hchi]
  | cherry C =>
    have hbound := C.longer_arm_bound hred
    have hz := I.distance_nonneg v C.center
    change I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary ≤
      (1 + 1 / (chi - 1)) * (I.distance v C.center + I.distance C.center C.primary)
    have hb := (lt_div_iff₀ hchi).mp hbound
    norm_num [chi, e0] at hb ⊢
    linarith

theorem longerArm_lt_length (L : Limb S v) (hred : Reduced S) :
    L.longerArm < L.length / (chi - 1) := by
  have hchi : 0 < chi - 1 := by norm_num [chi, e0]
  cases L with
  | direct x hv hx h =>
    exact div_pos (I.distance_pos v x (Subtype.val_injective.ne h.ne)) hchi
  | cherry C =>
    have hs := C.longer_arm_bound hred
    have hz := I.distance_nonneg v C.center
    change I.distance C.center C.secondary <
      (I.distance v C.center + I.distance C.center C.primary) / (chi - 1)
    exact hs.trans_le ((div_le_div_iff_of_pos_right hchi).mpr (by linarith))

theorem crossing_barrier (L : Limb S v) (hred : Reduced S)
    {a b : V} (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ L.region) (hbR : b ∉ L.region) :
    p * L.length < I.distance a b := by
  cases L with
  | direct x hv hx h =>
    have hh := reduced_region_barrier S hred v x h hv ha hb haR hbR
    have hr := I.distance_nonneg v x
    change p * I.distance v x < I.distance a b
    norm_num [p, chi, e0] at hh ⊢
    linarith
  | cherry C =>
    let a' : ↥S.vertices := ⟨a, S.contains ha⟩
    let b' : ↥S.vertices := ⟨b, S.contains hb⟩
    have hca : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center a' :=
      (Tree.mem_region S v C.center a').mp haR
    have hcb : ¬ (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center b' :=
      fun h => hbR ((Tree.mem_region S v C.center b').mpr h)
    have hvb := (delete_edge_two_sides S.graph S.isTree.connected v C.center b').resolve_right hcb
    exact C.crossing_barrier hred a' b' hca hvb ha hb

theorem threshold_region_closed (L : Limb S v) (hred : Reduced S) (a : ℝ)
    (ha : a ≤ p * L.length) :
    ClosedCut (threshold I a ⊔ terminalGraph S) (L.region : Set V) := by
  apply threshold_sup_closedCut I (terminalGraph S) _ _ a ha
  · intro x hx y hy hxR hyR
    exact (L.crossing_barrier hred hx hy hxR hyR).le
  · exact terminalGraph_region_closed S v L.stem L.attachment_nonterminal

end Limb

end SteinerUpperBound.Structural.Tree

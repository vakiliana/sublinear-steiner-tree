module

public import SteinerUpperBound.Structural.FanPromotion

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem edge_le_completeOn (U : Finset V) {a b : V} (ha : a ∈ U) (hb : b ∈ U) :
    SimpleGraph.edge a b ≤ Network.completeOn U := by
  intro x y hxy
  rcases (SimpleGraph.edge_adj a b x y).mp hxy with ⟨h | h, hne⟩
  · rcases h with ⟨rfl, rfl⟩
    exact (Network.completeOn_adj _ _ _).mpr ⟨hne, ha, hb⟩
  · rcases h with ⟨rfl, rfl⟩
    exact (Network.completeOn_adj _ _ _).mpr ⟨hne, hb, ha⟩

theorem completeOn_mono {A B : Finset V} (h : A ⊆ B) :
    Network.completeOn A ≤ Network.completeOn B := by
  intro x y hxy
  obtain ⟨hne, hx, hy⟩ := (Network.completeOn_adj _ _ _).mp hxy
  exact (Network.completeOn_adj _ _ _).mpr ⟨hne, h hx, h hy⟩

namespace Cherry

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

theorem sibling_permanent (C : Cherry S v) :
    (terminalGraph C.promote).Adj C.primary C.secondary := by
  have hp := suppress_preserves_terminals C.promoted C.center v C.primary C.center_nonterminal
    ((C.promoted_center_adj v).mpr (Or.inl rfl))
    ((C.promoted_center_adj C.primary).mpr (Or.inr rfl)) C.primary_ne_attachment.symm
    (fun z hz => (C.promoted_center_adj z).mp hz)
  apply hp
  have hadj : C.promoted.graph.Adj C.primary C.secondary :=
    Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl, rfl⟩, C.ports_ne⟩)
  have hne : (C.primary : V) ≠ (C.secondary : V) :=
    fun h => C.ports_ne (Subtype.ext h)
  exact ⟨SimpleGraph.map_adj_apply' hadj hne,
    (Network.completeOn_adj _ _ _).mpr ⟨hne, C.primary_terminal, C.secondary_terminal⟩⟩

theorem transportSibling_ports (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center) :
    (C.transportSibling R hr).ports = R.ports := by
  cases R <;> rfl

theorem transportSibling_edgeWeight (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center)
    (w : Sym2 V → ℝ) : (C.transportSibling R hr).edgeWeight w = R.edgeWeight w := by
  cases R <;> rfl

theorem transportSibling_siblingWeight (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center)
    (w : Sym2 V → ℝ) : (C.transportSibling R hr).siblingWeight w = R.siblingWeight w := by
  cases R <;> rfl

theorem promote_limbCost_le (C : Cherry S v) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) C.promote.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        (Limb.cherry C).edgeWeight w + (Limb.cherry C).siblingWeight w +
        w s((v : V), (C.primary : V)) := by
  have hh := C.promote_cost_le w hw
  have h1 : w s((C.center : V), (v : V)) = w s((v : V), (C.center : V)) :=
    congrArg w Sym2.eq_swap
  have h2 : w s((C.primary : V), (v : V)) = w s((v : V), (C.primary : V)) :=
    congrArg w Sym2.eq_swap
  rw [h1, h2] at hh
  change GraphCost.cost (fun e => w (e.map Subtype.val)) C.promote.graph ≤ _ at hh
  simp only [Limb.edgeWeight, Limb.siblingWeight]
  linarith

end Cherry

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

def cherryCount : Limb S v → ℕ
  | .direct _ _ _ _ => 0
  | .cherry _ => 1

end Limb

theorem Cherry.transportSibling_cherryCount {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (C : Cherry S v) (R : Limb S v) (hr : R.stem ≠ C.center) :
    (C.transportSibling R hr).cherryCount = R.cherryCount := by
  cases R <;> rfl

namespace Fan

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

noncomputable def cherryCount (F : Fan S parent v) : ℕ :=
  F.left.cherryCount + F.right.cherryCount

theorem promoteLeft_cherryCount (F : Fan S parent v) (C : Cherry S v)
    (hl : F.left = Limb.cherry C) :
    (F.promoteLeft C hl).cherryCount + 1 = F.cherryCount := by
  have hr : F.right.stem ≠ C.center := by simpa only [hl, Limb.stem] using F.stems_ne.symm
  change 0 + (C.transportSibling F.right hr).cherryCount + 1 =
    F.left.cherryCount + F.right.cherryCount
  rw [Cherry.transportSibling_cherryCount, hl]
  simp [Limb.cherryCount]
  omega

theorem promoteLeft_localVertices (F : Fan S parent v) (C : Cherry S v)
    (hl : F.left = Limb.cherry C) :
    (F.promoteLeft C hl).localVertices ⊆ F.localVertices := by
  intro x hx
  change x ∈ insert (v : V)
    ({(C.primary : V)} ∪ (C.transportSibling F.right
      (by simpa only [hl, Limb.stem] using F.stems_ne.symm)).ports) at hx
  rw [Cherry.transportSibling_ports] at hx
  change x ∈ insert (v : V) (F.left.ports ∪ F.right.ports)
  rw [hl]
  simp only [Limb.ports, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
  tauto

theorem promoteLeft_ambient_le (F : Fan S parent v) (C : Cherry S v)
    (hl : F.left = Limb.cherry C) :
    C.promote.ambient ≤ S.ambient ⊔ Network.completeOn F.localVertices := by
  have hp : (C.primary : V) ∈ F.localVertices := by
    simp [localVertices, hl, Limb.ports]
  have hq : (C.secondary : V) ∈ F.localVertices := by
    simp [localVertices, hl, Limb.ports]
  have hv : (v : V) ∈ F.localVertices := by simp [localVertices]
  exact C.promote_ambient_le.trans
    (sup_le (sup_le le_sup_left ((edge_le_completeOn _ hp hq).trans le_sup_right))
      ((edge_le_completeOn _ hp hv).trans le_sup_right))

structure FullyPromoted (F : Fan S parent v) where
  solution : TreeGeometry.TreeSolution I
  parentVertex : ↥solution.vertices
  centerVertex : ↥solution.vertices
  fan : Fan solution parentVertex centerVertex
  parent_val : (parentVertex : V) = (parent : V)
  center_val : (centerVertex : V) = (v : V)
  left_val : (fan.left.primary : V) = (F.left.primary : V)
  right_val : (fan.right.primary : V) = (F.right.primary : V)
  left_direct : fan.left.stem = fan.left.primary
  right_direct : fan.right.stem = fan.right.primary
  vertices_subset : solution.vertices ⊆ S.vertices
  permanent : terminalGraph S ≤ terminalGraph solution
  ambient_le : solution.ambient ≤ S.ambient ⊔ Network.completeOn F.localVertices
  cost_le : ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
    GraphCost.cost (fun e => w (e.map Subtype.val)) solution.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        F.left.edgeWeight w - F.right.edgeWeight w +
        F.left.siblingWeight w + F.right.siblingWeight w +
        w s((v : V), (F.left.primary : V)) + w s((v : V), (F.right.primary : V))
  left_linked : ∀ x ∈ F.left.ports, (terminalGraph solution).Reachable x F.left.primary
  right_linked : ∀ x ∈ F.right.ports, (terminalGraph solution).Reachable x F.right.primary

theorem fullyPromotedBase (F : Fan S parent v)
    (hleft : F.left.stem = F.left.primary) (hright : F.right.stem = F.right.primary) :
    Nonempty (FullyPromoted F) := by
  have hdirect (L : Limb S v) (h : L.stem = L.primary) :
      ∃ x hv hx ha, L = Limb.direct x hv hx ha := by
    cases L with
    | direct x hv hx ha => exact ⟨x, hv, hx, ha, rfl⟩
    | cherry C =>
      change C.center = C.primary at h
      exact False.elim (C.center_ne_primary h)
  obtain ⟨x, hvx, hx, hax, hl⟩ := hdirect F.left hleft
  obtain ⟨y, hvy, hy, hay, hr⟩ := hdirect F.right hright
  refine ⟨{
      solution := S
      parentVertex := parent
      centerVertex := v
      fan := F
      parent_val := rfl
      center_val := rfl
      left_val := rfl
      right_val := rfl
      left_direct := hleft
      right_direct := hright
      vertices_subset := Finset.Subset.refl _
      permanent := le_rfl
      ambient_le := le_sup_left
      cost_le := ?_
      left_linked := ?_
      right_linked := ?_ }⟩
  · intro w hw
    simp only [hl, hr, Limb.edgeWeight, Limb.siblingWeight, Limb.primary]
    linarith
  · intro z hz
    simp only [hl, Limb.ports, Finset.mem_singleton] at hz
    simpa only [hl, Limb.primary, hz] using SimpleGraph.Reachable.refl (G := terminalGraph S) (x : V)
  · intro z hz
    simp only [hr, Limb.ports, Finset.mem_singleton] at hz
    simpa only [hr, Limb.primary, hz] using SimpleGraph.Reachable.refl (G := terminalGraph S) (y : V)

end Fan

end SteinerUpperBound.Structural.Tree

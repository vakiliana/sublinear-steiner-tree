module

public import SteinerUpperBound.Structural.FanPromotionResult

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.Fan

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

noncomputable def FullyPromoted.unswap (F : Fan S parent v) (R : FullyPromoted F.swap) :
    FullyPromoted F := by
  have hloc : F.swap.localVertices = F.localVertices := by
    change insert (v : V) (F.right.ports ∪ F.left.ports) =
      insert (v : V) (F.left.ports ∪ F.right.ports)
    rw [Finset.union_comm]
  refine
    { solution := R.solution
      parentVertex := R.parentVertex
      centerVertex := R.centerVertex
      fan := R.fan.swap
      parent_val := R.parent_val
      center_val := R.center_val
      left_val := R.right_val
      right_val := R.left_val
      left_direct := R.right_direct
      right_direct := R.left_direct
      vertices_subset := R.vertices_subset
      permanent := R.permanent
      ambient_le := by simpa only [hloc] using R.ambient_le
      cost_le := ?_
      left_linked := R.right_linked
      right_linked := R.left_linked }
  intro w hw
  have hh := R.cost_le w hw
  change GraphCost.cost (fun e => w (e.map Subtype.val)) R.solution.graph ≤
    GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
      F.right.edgeWeight w - F.left.edgeWeight w +
      F.right.siblingWeight w + F.left.siblingWeight w +
      w s((v : V), (F.right.primary : V)) + w s((v : V), (F.left.primary : V)) at hh
  linarith

noncomputable def FullyPromoted.prependLeft (F : Fan S parent v)
    (C : Cherry S v) (hl : F.left = Limb.cherry C)
    (R : FullyPromoted (F.promoteLeft C hl)) : FullyPromoted F := by
  have hrc : F.right.stem ≠ C.center := by simpa only [hl, Limb.stem] using F.stems_ne.symm
  refine
    { solution := R.solution
      parentVertex := R.parentVertex
      centerVertex := R.centerVertex
      fan := R.fan
      parent_val := R.parent_val
      center_val := R.center_val
      left_val := R.left_val.trans (by rw [hl]; rfl)
      right_val := R.right_val.trans (C.transportSibling_primary_val F.right hrc)
      left_direct := R.left_direct
      right_direct := R.right_direct
      vertices_subset := R.vertices_subset.trans (Finset.erase_subset _ _)
      permanent := C.promote_preserves_terminals.trans R.permanent
      ambient_le := ?_
      cost_le := ?_
      left_linked := ?_
      right_linked := ?_ }
  · exact R.ambient_le.trans
      (sup_le (F.promoteLeft_ambient_le C hl)
        ((completeOn_mono (F.promoteLeft_localVertices C hl)).trans le_sup_right))
  · intro w hw
    have hrec := R.cost_le w hw
    have hfirst := C.promote_limbCost_le w hw
    change GraphCost.cost (fun e => w (e.map Subtype.val)) R.solution.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) C.promote.graph -
        w s((v : V), (C.primary : V)) - (C.transportSibling F.right hrc).edgeWeight w +
        0 + (C.transportSibling F.right hrc).siblingWeight w +
        w s((v : V), (C.primary : V)) +
        w s((v : V), ((C.transportSibling F.right hrc).primary : V)) at hrec
    rw [Cherry.transportSibling_edgeWeight, Cherry.transportSibling_siblingWeight,
      Cherry.transportSibling_primary_val] at hrec
    rw [hl]
    simp only [Limb.primary] at hrec hfirst ⊢
    linarith
  · intro x hx
    rw [hl] at hx ⊢
    simp only [Limb.ports, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with he | he
    · subst x
      exact SimpleGraph.Reachable.refl _
    · subst x
      exact (C.sibling_permanent.symm.reachable).mono R.permanent
  · intro x hx
    have hx' : x ∈ (F.promoteLeft C hl).right.ports := by
      change x ∈ (C.transportSibling F.right hrc).ports
      rwa [Cherry.transportSibling_ports]
    have hh := R.right_linked x hx'
    change (terminalGraph R.solution).Reachable x
      ((C.transportSibling F.right hrc).primary : V) at hh
    rw [Cherry.transportSibling_primary_val] at hh
    exact hh

theorem fullyPromoted_exists (F : Fan S parent v) : Nonempty (FullyPromoted F) := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (S : TreeGeometry.TreeSolution I)
      (parent v : ↥S.vertices) (F : Fan S parent v), F.cherryCount = n →
      Nonempty (FullyPromoted F) from hh _ S parent v F rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S parent v F hn
    cases hl : F.left with
    | direct x hv hx ha =>
      cases hr : F.right with
      | direct y hvr hyr har =>
        exact fullyPromotedBase F (by rw [hl]; rfl) (by rw [hr]; rfl)
      | cherry C =>
        have hleft : F.swap.left = Limb.cherry C := hr
        let F₁ := F.swap.promoteLeft C hleft
        have hcount : F₁.cherryCount < n := by
          have hh := promoteLeft_cherryCount F.swap C hleft
          have hswap : F.swap.cherryCount = F.cherryCount := by
            change F.right.cherryCount + F.left.cherryCount = F.left.cherryCount + F.right.cherryCount
            omega
          change F₁.cherryCount + 1 = F.swap.cherryCount at hh
          omega
        obtain ⟨R⟩ := ih _ hcount _ _ _ F₁ rfl
        exact ⟨(R.prependLeft F.swap C hleft).unswap F⟩
    | cherry C =>
      let F₁ := F.promoteLeft C hl
      have hcount : F₁.cherryCount < n := by
        have hh := promoteLeft_cherryCount F C hl
        change F₁.cherryCount + 1 = F.cherryCount at hh
        omega
      obtain ⟨R⟩ := ih _ hcount _ _ _ F₁ rfl
      exact ⟨R.prependLeft F C hl⟩

end SteinerUpperBound.Structural.Tree.Fan

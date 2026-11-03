module

public import SteinerUpperBound.Structural.Topology
public import SteinerUpperBound.Structural.Regions

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem terminal_reachable_of_walk (S : TreeGeometry.TreeSolution I)
    {x y : ↥S.vertices} (p : S.graph.Walk x y)
    (hT : ∀ z ∈ p.support, (z : V) ∈ I.terminals) :
    (terminalGraph S).Reachable x y := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hab p ih =>
    have ha := hT a (by simp)
    have hb := hT b (by simpa only [SimpleGraph.Walk.support_cons] using
      List.mem_cons_of_mem a p.start_mem_support)
    have hne : (a : V) ≠ (b : V) := Subtype.val_injective.ne hab.ne
    have hhead : (terminalGraph S).Adj a b :=
      ⟨SimpleGraph.map_adj_apply' hab hne, (Network.completeOn_adj _ _ _).mpr ⟨hne, ha, hb⟩⟩
    exact hhead.reachable.trans (ih (fun z hz => hT z
      (by simpa only [SimpleGraph.Walk.support_cons] using List.mem_cons_of_mem a hz)))

theorem terminal_reachable_of_zero_height (S : TreeGeometry.TreeSolution I) (r : ↥S.vertices)
    {u x q : ↥S.vertices} (hu : Rooted.height S.graph r (selectedTerminals S) u = 0)
    (p : S.graph.Walk u x) (hp : p.IsPath) (hq : S.graph.Adj u q)
    (hdq : S.graph.dist r q + 1 = S.graph.dist r u) (hnot : s(u, q) ∉ p.edges) :
    (terminalGraph S).Reachable u x := by
  apply terminal_reachable_of_walk S p
  intro z hz
  have hprefix := Rooted.path_region_height_le S.graph r (selectedTerminals S) S.isTree
    (p.takeUntil z hz) (hp.takeUntil hz) hq hdq
      (fun he => hnot (p.edges_takeUntil_subset_edges hz he))
  by_contra hzT
  have hzT' : z ∉ selectedTerminals S :=
    fun h => hzT ((mem_selectedTerminals S z).mp h)
  have hpz := Rooted.nonterminal_height_pos S.graph r (selectedTerminals S) hzT'
  omega

theorem port_reachable_in_limb (S : TreeGeometry.TreeSolution I) (hc : S.IsClean)
    (hstar : ¬ Nonempty (ShortStar S)) (r : ↥S.vertices) (hr : (r : V) ∈ I.terminals)
    {v : ↥S.vertices} (hv2 : Rooted.height S.graph r (selectedTerminals S) v = 2)
    (L : Limb S v) (hchild : L.stem ∈ Rooted.children S.graph r v)
    {x : ↥S.vertices} (p : S.graph.Walk L.stem x) (hp : p.IsPath)
    (hnot : s(v, L.stem) ∉ p.edges) (hxT : (x : V) ∈ I.terminals) :
    ∃ t ∈ L.ports, (terminalGraph S).Reachable x t := by
  have hclean := rooted_clean S hc
  have hno := no_zero_core_star_of_no_star S hstar
  have hr' := (mem_selectedTerminals S r).mpr hr
  have hvNT : v ∉ selectedTerminals S :=
    fun h => L.attachment_nonterminal ((mem_selectedTerminals S v).mp h)
  have hheightlt := Rooted.child_height_lt S.graph r (selectedTerminals S) hvNT hchild
  have hdc := (Rooted.mem_children S.graph r v L.stem).mp hchild |>.2
  have hparent : s(L.stem, v) ∉ p.edges := by
    have he : s(L.stem, v) = s(v, L.stem) := Sym2.eq_swap
    rwa [he]
  cases L with
  | direct t hv ht hadj =>
    have ht' := (mem_selectedTerminals S t).mpr ht
    have hne := Rooted.no_terminal_height_one S.graph r (selectedTerminals S)
      S.isTree hr' hclean hno t ht'
    have hzero : Rooted.height S.graph r (selectedTerminals S) t = 0 := by
      change Rooted.height S.graph r (selectedTerminals S) t <
        Rooted.height S.graph r (selectedTerminals S) v at hheightlt
      omega
    refine ⟨(t : V), by simp [Limb.ports], ?_⟩
    exact (terminal_reachable_of_zero_height S r hzero p hp hadj.symm hdc.symm hparent).symm
  | cherry C =>
    change Rooted.height S.graph r (selectedTerminals S) C.center <
      Rooted.height S.graph r (selectedTerminals S) v at hheightlt
    change S.graph.dist r C.center = S.graph.dist r v + 1 at hdc
    have hcNT : C.center ∉ selectedTerminals S :=
      fun h => C.center_nonterminal ((mem_selectedTerminals S C.center).mp h)
    have hpos := Rooted.nonterminal_height_pos S.graph r (selectedTerminals S) hcNT
    have hc1 : Rooted.height S.graph r (selectedTerminals S) C.center = 1 := by omega
    cases p with
    | nil => exact False.elim (C.center_nonterminal hxT)
    | @cons c y x hcy p =>
      have hyChild := Rooted.first_step_child S.graph r S.isTree hcy p C.trunk.symm
        hdc.symm hparent
      have hyLt := Rooted.child_height_lt S.graph r (selectedTerminals S) hcNT hyChild
      have hy0 : Rooted.height S.graph r (selectedTerminals S) y = 0 := by omega
      have hport : (y : V) ∈ (Limb.cherry C).ports := by
        rcases C.neighbors y hcy with h | h | h
        · exact False.elim (Rooted.parent_not_child S.graph r hdc.symm (h ▸ hyChild))
        · simp [Limb.ports, h]
        · simp [Limb.ports, h]
      have hyDepth := (Rooted.mem_children S.graph r C.center y).mp hyChild |>.2
      have hnotTail : s(y, C.center) ∉ p.edges := by
        rw [Sym2.eq_swap]
        exact (SimpleGraph.Walk.isTrail_cons hcy p).mp hp.isTrail |>.2
      exact ⟨(y : V), hport,
        (terminal_reachable_of_zero_height S r hy0 p hp.of_cons hcy.symm hyDepth.symm hnotTail).symm⟩

namespace RootedFringe

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

theorem selected_port_cover (F : RootedFringe S parent v) (hc : S.IsClean)
    (hstar : ¬ Nonempty (ShortStar S)) {x : ↥S.vertices}
    (hxT : (x : V) ∈ I.terminals)
    (hxR : (S.graph.deleteEdges {s(parent, v)}).Reachable v x) :
    ∃ t ∈ F.fan.left.ports ∪ F.fan.right.ports, (terminalGraph S).Reachable x t := by
  obtain ⟨p, hpnot⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hxR
  obtain ⟨q, hq, hnot⟩ : ∃ q : S.graph.Walk v x,
      q.IsPath ∧ s(v, parent) ∉ q.edges := by
    refine ⟨p.toPath, p.toPath.isPath, ?_⟩
    have he : s(v, parent) = s(parent, v) := Sym2.eq_swap
    rw [he]
    exact fun h => hpnot (p.edges_toPath_subset_edges h)
  cases q with
  | nil => exact False.elim (F.fan.center_nonterminal hxT)
  | @cons v w x hvw q =>
    have hchild := Rooted.first_step_child S.graph F.root S.isTree hvw q
      F.fan.parent_edge.symm F.parent_lower hnot
    have hnotTail : s(v, w) ∉ q.edges :=
      (SimpleGraph.Walk.isTrail_cons hvw q).mp hq.isTrail |>.2
    rcases F.fan.neighbors w hvw with he | he | he
    · exact False.elim (Rooted.parent_not_child S.graph F.root F.parent_lower (he ▸ hchild))
    · subst w
      obtain ⟨t, ht, hreach⟩ := port_reachable_in_limb S hc hstar F.root F.root_terminal
        F.height_two F.fan.left hchild q hq.of_cons hnotTail hxT
      exact ⟨t, Finset.mem_union.mpr (Or.inl ht), hreach⟩
    · subst w
      obtain ⟨t, ht, hreach⟩ := port_reachable_in_limb S hc hstar F.root F.root_terminal
        F.height_two F.fan.right hchild q hq.of_cons hnotTail hxT
      exact ⟨t, Finset.mem_union.mpr (Or.inr ht), hreach⟩

theorem port_cover (F : RootedFringe S parent v) (hc : S.IsClean)
    (hstar : ¬ Nonempty (ShortStar S)) {x : V} (hxT : x ∈ I.terminals)
    (hxR : x ∈ F.fan.region) :
    ∃ t ∈ F.fan.left.ports ∪ F.fan.right.ports, (terminalGraph S).Reachable x t := by
  let x' : ↥S.vertices := ⟨x, S.contains hxT⟩
  exact F.selected_port_cover hc hstar hxT ((mem_region S parent v x').mp hxR)

theorem promoted_two_groups (F : RootedFringe S parent v) (hc : S.IsClean)
    (hstar : ¬ Nonempty (ShortStar S)) (R : Fan.FullyPromoted F.fan) :
    ∀ x ∈ F.fan.region, x ∈ I.terminals →
      (terminalGraph R.solution).Reachable x F.fan.left.primary ∨
      (terminalGraph R.solution).Reachable x F.fan.right.primary := by
  intro x hxR hxT
  obtain ⟨t, ht, hxt⟩ := F.port_cover hc hstar hxT hxR
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Or.inl ((hxt.mono R.permanent).trans (R.left_linked t ht))
  · exact Or.inr ((hxt.mono R.permanent).trans (R.right_linked t ht))

end RootedFringe

def TwoGroups (P : SimpleGraph V) (C : Finset V) : Prop :=
  ∃ a b, ∀ x ∈ C, P.Reachable x a ∨ P.Reachable x b

theorem TwoGroups.mono {P Q : SimpleGraph V} {C : Finset V}
    (h : TwoGroups P C) (hPQ : P ≤ Q) : TwoGroups Q C := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, fun x hx => (hab x hx).imp (fun h => h.mono hPQ) (fun h => h.mono hPQ)⟩

theorem TwoGroups.not_three {P : SimpleGraph V} {C : Finset V}
    (h : TwoGroups P C) {x y z : V} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : ¬ P.Reachable x y) (hxz : ¬ P.Reachable x z) (hyz : ¬ P.Reachable y z) : False := by
  obtain ⟨a, b, hab⟩ := h
  rcases hab x hx with hx | hx <;>
    rcases hab y hy with hy | hy <;>
    rcases hab z hz with hz | hz
  all_goals first
    | exact hxy (hx.trans hy.symm)
    | exact hxz (hx.trans hz.symm)
    | exact hyz (hy.trans hz.symm)

end SteinerUpperBound.Structural.Tree

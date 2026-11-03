module

public import SteinerUpperBound.Structural.DirectReconnection

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.ShortStar

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I}

theorem reconnected_exists (A : ShortStar S) :
    ∃ Q : TreeGeometry.TreeSolution I, Q.vertices ⊆ S.vertices ∧
      terminalGraph S ≤ terminalGraph Q ∧
      (∀ i j, (terminalGraph Q).Reachable (A.port i) (A.port j)) ∧
      ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
        GraphCost.cost (fun e => w (e.map Subtype.val)) Q.graph ≤
          GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph +
            (∑ C ∈ A.cherries, C.delta w) +
            ∑ i ∈ Finset.univ.erase A.kept,
              (w s(A.port A.kept, A.port i) - w s((A.attachment i : V), A.port i)) := by
  classical
  obtain ⟨R⟩ := A.batch_exists
  let D : Finset (Fin 3) := Finset.univ.erase A.kept
  let u := A.batchAttachment R
  let p := A.batchPort R
  let regions := fun i : Fin 3 => {x : ↥R.solution.vertices | (x : V) ∈ (A.limb i).region}
  have htarget : ∀ i ∈ D, p A.kept ∉ regions i := by
    intro i hi
    exact A.port_outside (Finset.mem_erase.mp hi).1
  have hother : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → p i ∉ regions j := by
    intro i hi j hj hij
    exact A.port_outside (Ne.symm hij)
  have hedges : ∀ i ∈ D, ∀ j ∈ D, i ≠ j → s(u i, p i) ≠ s(u j, p j) := by
    intro i hi j hj hij he
    apply A.direct_edges_ne hij
    simpa only [Sym2.map_mk] using congrArg (Sym2.map (Subtype.val : ↥R.solution.vertices → V)) he
  have hnew : ∀ i ∈ D, ∀ j ∈ D, s(p A.kept, p i) ≠ s(u j, p j) := by
    intro i hi j hj he
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
    · have hval := congrArg (fun z : ↥R.solution.vertices => (z : V)) h
      exact (A.limb j).attachment_nonterminal (hval ▸ A.port_terminal A.kept)
    · have hval := congrArg (fun z : ↥R.solution.vertices => (z : V)) h
      exact (A.limb j).attachment_nonterminal (hval ▸ A.port_terminal i)
  obtain ⟨H, hH, hkeep, hlinks, hcost⟩ := reconnect_direct_edges R.solution.graph R.solution.isTree
    D u p (p A.kept) regions
    (fun i hi => A.batch_direct_adj R i)
    (fun i hi => A.attachment_outside_all i i)
    (fun i hi => (A.limb i).primary_mem_region) htarget
    (fun i hi => pull_closed_cut R.solution (u i) (p i) _ (A.batch_direct_closed R i))
    hother hedges hnew
  let Q : TreeGeometry.TreeSolution I := ⟨R.solution.vertices, R.solution.contains, H, hH⟩
  have hperm : terminalGraph R.solution ≤ terminalGraph Q := by
    intro x y hxy
    obtain ⟨hxy, hT⟩ := hxy
    obtain ⟨hne, hxT, hyT⟩ := (Network.completeOn_adj _ _ _).mp hT
    change (R.solution.graph.map Subtype.val).Adj x y at hxy
    obtain ⟨_, a, b, hab, rfl, rfl⟩ :=
      (SimpleGraph.map_adj' Subtype.val R.solution.graph x y).mp hxy
    have hnot : s(a, b) ∉ (D.image (fun i => s(u i, p i)) : Set (Sym2 ↥R.solution.vertices)) := by
      intro he
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp he
      rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨h, _⟩
      · have hv := congrArg (fun z : ↥R.solution.vertices => (z : V)) h
        change (A.attachment i : V) = (a : V) at hv
        exact (A.limb i).attachment_nonterminal (by simpa only [hv] using hxT)
      · have hv := congrArg (fun z : ↥R.solution.vertices => (z : V)) h
        change (A.attachment i : V) = (b : V) at hv
        exact (A.limb i).attachment_nonterminal (by simpa only [hv] using hyT)
    have hhab : H.Adj a b := by
      apply hkeep
      apply SimpleGraph.deleteEdges_adj.mpr
      refine ⟨hab, ?_⟩
      intro he
      apply hnot
      simpa only [Finset.mem_coe, Finset.mem_image] using he
    exact ⟨SimpleGraph.map_adj_apply' (f := (Subtype.val : ↥Q.vertices → V)) hhab hne, hT⟩
  have hports : ∀ i, (terminalGraph Q).Reachable (A.port i) (A.port A.kept) := by
    intro i
    by_cases hi : i = A.kept
    · simpa only [hi] using SimpleGraph.Reachable.refl (G := terminalGraph Q) (A.port A.kept)
    · have hiD : i ∈ D := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
      have hAdj : (terminalGraph Q).Adj (A.port A.kept) (A.port i) := by
        have hne := A.ports_ne (Ne.symm hi)
        refine ⟨?_, (Network.completeOn_adj _ _ _).mpr
          ⟨hne, A.port_terminal A.kept, A.port_terminal i⟩⟩
        exact SimpleGraph.map_adj_apply' (f := (Subtype.val : ↥Q.vertices → V)) (hlinks i hiD) hne
      exact hAdj.symm.reachable
  refine ⟨Q, ?_, R.permanent.trans hperm, (fun i j => (hports i).trans (hports j).symm), ?_⟩
  · change R.solution.vertices ⊆ S.vertices
    rw [R.vertices_eq]
    exact Finset.sdiff_subset
  · intro w hw
    have hb := R.cost_le w hw
    have hd := hcost (fun e => w (e.map Subtype.val)) (fun e => hw _)
    change GraphCost.cost (fun e => w (e.map Subtype.val)) Q.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) R.solution.graph +
        ∑ i ∈ Finset.univ.erase A.kept,
          (w s(A.port A.kept, A.port i) - w s((A.attachment i : V), A.port i)) at hd
    linarith

end SteinerUpperBound.Structural.Tree.ShortStar

module

public import SteinerUpperBound.Structural.StarBatchData

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem graph_sup_adj {α : Type*} (A : Finset α) (f : α → SimpleGraph V) (x y : V) :
    (A.sup f).Adj x y ↔ ∃ a ∈ A, (f a).Adj x y := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih => simp [Finset.sup_insert, SimpleGraph.sup_adj, ih]

namespace ShortStar

variable {S : TreeGeometry.TreeSolution I}

theorem ports_ne (A : ShortStar S) {i j : Fin 3} (hij : i ≠ j) : A.port i ≠ A.port j := by
  intro he
  exact A.port_outside hij (by simpa only [he] using (A.limb i).primary_mem_region)

theorem direct_edges_ne (A : ShortStar S) {i j : Fin 3} (hij : i ≠ j) :
    s((A.attachment i : V), A.port i) ≠ s((A.attachment j : V), A.port j) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, _⟩
  · exact A.ports_ne hij h
  · exact (A.limb i).attachment_nonterminal (h ▸ A.port_terminal j)

theorem added_deleted_closed (A : ShortStar S) (i : Fin 3)
    (D : CherryData I) (hD : D ∈ A.cherries) :
    ClosedCut (D.addedGraph.deleteEdges {s((A.attachment i : V), A.port i)})
      ((A.limb i).region : Set V) := by
  obtain ⟨j, hj⟩ := (A.mem_cherries D).mp hD
  by_cases hji : j = i
  · subst j
    obtain ⟨C, hL, hData⟩ := ((A.limb i).mem_cherrySet D).mp hj
    subst D
    have hmem := (A.limb i).cherry_ports_in_region hj
    have hp : A.port i = (C.primary : V) := by simp only [port, hL, Limb.primary]
    intro x y hxy
    obtain ⟨hxy, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
    change (SimpleGraph.edge (C.primary : V) (C.secondary : V) ⊔
      SimpleGraph.edge (C.primary : V) (A.attachment i : V)).Adj x y at hxy
    rcases hxy with hxy | hxy
    · exact (closedCut_edge ((A.limb i).region : Set V) _ _ (iff_of_true hmem.1 hmem.2)) x y hxy
    · rw [hp] at hnot
      rcases (SimpleGraph.edge_adj (C.primary : V) (A.attachment i : V) x y).mp hxy with
        ⟨he | he, _⟩
      · rcases he with ⟨rfl, rfl⟩
        exact False.elim (hnot (Set.mem_singleton_iff.mpr Sym2.eq_swap))
      · rcases he with ⟨rfl, rfl⟩
        exact False.elim (hnot (Set.mem_singleton _))
  · have hports := (A.limb j).cherry_ports_in_region hj
    have hPrimary : D.primary ∉ (A.limb i).region := by
      intro h
      exact Finset.disjoint_left.mp (A.disjoint i j (Ne.symm hji)) h hports.1
    have hSecondary : D.secondary ∉ (A.limb i).region := by
      intro h
      exact Finset.disjoint_left.mp (A.disjoint i j (Ne.symm hji)) h hports.2
    have hAttachment : D.attachment ∉ (A.limb i).region := by
      rw [(A.limb j).cherry_attachment hj]
      exact A.attachment_outside_all j i
    have hc : ClosedCut D.addedGraph ((A.limb i).region : Set V) :=
      (closedCut_edge _ _ _ (iff_of_false hPrimary hSecondary)).sup
        (closedCut_edge _ _ _ (iff_of_false hPrimary hAttachment))
    exact closedCut_mono (SimpleGraph.deleteEdges_le _) hc

theorem batch_direct_closed (A : ShortStar S) (R : BatchPromoted S A.cherries) (i : Fin 3) :
    ClosedCut (R.solution.ambient.deleteEdges {s((A.attachment i : V), A.port i)})
      ((A.limb i).region : Set V) := by
  intro x y hxy
  obtain ⟨hQ, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hxy
  rcases R.ambient_le hQ with hold | hadd
  · have hOldNot : s(x, y) ∉
        ({s((A.attachment i : V), ((A.limb i).stem : V))} : Set (Sym2 V)) := by
      cases hL : A.limb i with
      | direct z hv hz h =>
        simpa only [port, hL, Limb.stem, Limb.primary] using hnot
      | cherry C =>
        have hD : C.data ∈ A.cherries :=
          (A.mem_cherries _).mpr ⟨i, by simp only [hL, Limb.cherrySet, Finset.mem_singleton]⟩
        have hCenterNot : (C.center : V) ∉ R.solution.vertices := by
          rw [R.vertices_eq]
          intro hc
          exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr ⟨C.data, hD, rfl⟩)
        simp only [hL, Limb.stem, Set.mem_singleton_iff]
        intro he
        have hxQ : x ∈ R.solution.vertices := R.solution.ambient_support_subset ⟨y, hQ⟩
        have hyQ : y ∈ R.solution.vertices := R.solution.ambient_support_subset ⟨x, hQ.symm⟩
        rcases Sym2.eq_iff.mp he with ⟨_, he⟩ | ⟨he, _⟩
        · exact hCenterNot (by simpa only [he] using hyQ)
        · exact hCenterNot (by simpa only [he] using hxQ)
    have hc : ClosedCut (S.ambient.deleteEdges {s((A.attachment i : V), ((A.limb i).stem : V))})
        ((A.limb i).region : Set V) := by
      simpa only [Limb.region] using ambient_region_closed S (A.attachment i) (A.limb i).stem
    exact hc x y (SimpleGraph.deleteEdges_adj.mpr ⟨hold, hOldNot⟩)
  · obtain ⟨D, hD, hDxy⟩ := (graph_sup_adj A.cherries CherryData.addedGraph x y).mp hadd
    exact A.added_deleted_closed i D hD x y (SimpleGraph.deleteEdges_adj.mpr ⟨hDxy, hnot⟩)

noncomputable abbrev batchAttachment (A : ShortStar S) (R : BatchPromoted S A.cherries)
    (i : Fin 3) : ↥R.solution.vertices :=
  ⟨A.attachment i, by
    rw [R.vertices_eq]
    exact Finset.mem_sdiff.mpr ⟨(A.attachment i).property, A.attachment_not_centers i⟩⟩

noncomputable abbrev batchPort (A : ShortStar S) (R : BatchPromoted S A.cherries)
    (i : Fin 3) : ↥R.solution.vertices :=
  ⟨A.port i, R.solution.contains (A.port_terminal i)⟩

theorem batch_direct_adj (A : ShortStar S) (R : BatchPromoted S A.cherries) (i : Fin 3) :
    R.solution.graph.Adj (A.batchAttachment R i) (A.batchPort R i) :=
  (ambient_adj_iff R.solution _ _).mp (A.batch_direct_edges R i)

theorem batch_region_eq (A : ShortStar S) (R : BatchPromoted S A.cherries) (i : Fin 3) :
    ∀ x : ↥R.solution.vertices,
      (x : V) ∈ region R.solution (A.batchAttachment R i) (A.batchPort R i) ↔
        (x : V) ∈ (A.limb i).region := by
  apply region_eq_of_closed R.solution _ _ (A.limb i).region
  · exact A.attachment_outside_all i i
  · exact (A.limb i).primary_mem_region
  · exact pull_closed_cut R.solution _ _ _ (A.batch_direct_closed R i)

end ShortStar

end SteinerUpperBound.Structural.Tree

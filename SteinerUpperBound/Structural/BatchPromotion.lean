module

public import SteinerUpperBound.Structural.CherryData
public import SteinerUpperBound.Structural.FanPromotionResult

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

structure BatchPromoted (S : TreeGeometry.TreeSolution I) (A : Finset (CherryData I)) where
  solution : TreeGeometry.TreeSolution I
  vertices_eq : solution.vertices = S.vertices \ A.image CherryData.center
  permanent : terminalGraph S ≤ terminalGraph solution
  survives : ∀ x y, x ∉ A.image CherryData.center → y ∉ A.image CherryData.center →
    S.ambient.Adj x y → solution.ambient.Adj x y
  new_stems : ∀ C ∈ A, solution.ambient.Adj C.attachment C.primary
  new_siblings : ∀ C ∈ A, (terminalGraph solution).Adj C.primary C.secondary
  ambient_le : solution.ambient ≤ S.ambient ⊔ A.sup CherryData.addedGraph
  cost_le : ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
    GraphCost.cost (fun e => w (e.map Subtype.val)) solution.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph + ∑ C ∈ A, C.delta w

theorem batch_promoted_exists (S : TreeGeometry.TreeSolution I) (A : Finset (CherryData I))
    (hOn : ∀ C ∈ A, C.OnTree S)
    (hAway : ∀ C ∈ A, ∀ D ∈ A, C.center ≠ D.attachment)
    (hCenters : Set.InjOn CherryData.center (A : Set (CherryData I))) :
    Nonempty (BatchPromoted S A) := by
  classical
  induction A using Finset.induction_on generalizing S with
  | empty =>
    refine ⟨{
      solution := S
      vertices_eq := by simp
      permanent := le_rfl
      survives := fun _ _ _ _ h => h
      new_stems := by simp
      new_siblings := by simp
      ambient_le := by simp
      cost_le := ?_ }⟩
    intro w hw
    simp
  | @insert C A hC ih =>
    have hc : C.OnTree S := hOn C (Finset.mem_insert_self _ _)
    let c := C.selected hc
    have hTailOn : ∀ D ∈ A, D.OnTree c.promote := by
      intro D hD
      have hDi : D ∈ insert C A := Finset.mem_insert_of_mem hD
      have hCi : C ∈ insert C A := Finset.mem_insert_self _ _
      have hattach : D.attachment ≠ C.center := (hAway C hCi D hDi).symm
      have hcenter := hAway D hDi C hCi
      have hcenters : D.center ≠ C.center := by
        intro he
        have hDC := hCenters hDi hCi he
        exact hC (hDC ▸ hD)
      exact D.onTree_promote c (hOn D hDi) hattach hcenter hcenters
    have hTailAway : ∀ D ∈ A, ∀ E ∈ A, D.center ≠ E.attachment :=
      fun D hD E hE => hAway D (Finset.mem_insert_of_mem hD) E (Finset.mem_insert_of_mem hE)
    have hTailCenters : Set.InjOn CherryData.center (A : Set (CherryData I)) :=
      fun D hD E hE he => hCenters (Finset.mem_insert_of_mem hD) (Finset.mem_insert_of_mem hE) he
    obtain ⟨R⟩ := ih c.promote hTailOn hTailAway hTailCenters
    have hsubset : A.image CherryData.center ⊆ (insert C A).image CherryData.center :=
      Finset.image_subset_image (Finset.subset_insert _ _)
    have hheadAdded : C.addedGraph ≤ (insert C A).sup CherryData.addedGraph :=
      Finset.le_sup (Finset.mem_insert_self _ _)
    have htailAdded : A.sup CherryData.addedGraph ≤ (insert C A).sup CherryData.addedGraph :=
      Finset.sup_le (fun D hD => Finset.le_sup (Finset.mem_insert_of_mem hD))
    have hstem : c.promote.ambient.Adj C.attachment C.primary := c.promote_primary_ambient
    have hleft : C.attachment ∉ A.image CherryData.center := by
      intro h
      obtain ⟨D, hD, he⟩ := Finset.mem_image.mp h
      exact hAway D (Finset.mem_insert_of_mem hD) C (Finset.mem_insert_self _ _) he
    have hright : C.primary ∉ A.image CherryData.center := by
      intro h
      obtain ⟨D, hD, he⟩ := Finset.mem_image.mp h
      exact D.center_nonterminal (by simpa only [he] using C.primary_terminal)
    refine ⟨{
      solution := R.solution
      vertices_eq := ?_
      permanent := c.promote_preserves_terminals.trans R.permanent
      survives := ?_
      new_stems := ?_
      new_siblings := ?_
      ambient_le := ?_
      cost_le := ?_ }⟩
    · rw [R.vertices_eq]
      change (S.vertices.erase C.center) \ A.image CherryData.center =
        S.vertices \ (insert C A).image CherryData.center
      rw [Finset.image_insert]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto
    · intro x y hx hy hxy
      have hxC : x ≠ C.center := by
        intro he
        exact hx (he ▸ Finset.mem_image.mpr ⟨C, Finset.mem_insert_self _ _, rfl⟩)
      have hyC : y ≠ C.center := by
        intro he
        exact hy (he ▸ Finset.mem_image.mpr ⟨C, Finset.mem_insert_self _ _, rfl⟩)
      exact R.survives x y (fun h => hx (hsubset h)) (fun h => hy (hsubset h))
        (c.promote_ambient_survives hxC hyC hxy)
    · intro D hD
      rcases Finset.mem_insert.mp hD with he | hD
      · subst D
        exact R.survives _ _ hleft hright hstem
      · exact R.new_stems D hD
    · intro D hD
      rcases Finset.mem_insert.mp hD with he | hD
      · subst D
        exact R.permanent c.sibling_permanent
      · exact R.new_siblings D hD
    · have hfirst : c.promote.ambient ≤ S.ambient ⊔ (insert C A).sup CherryData.addedGraph := by
        have hsib : SimpleGraph.edge C.primary C.secondary ≤
            S.ambient ⊔ (insert C A).sup CherryData.addedGraph :=
          (le_sup_left : SimpleGraph.edge C.primary C.secondary ≤ C.addedGraph).trans
            (hheadAdded.trans le_sup_right)
        have hdir : SimpleGraph.edge C.primary C.attachment ≤
            S.ambient ⊔ (insert C A).sup CherryData.addedGraph :=
          (le_sup_right : SimpleGraph.edge C.primary C.attachment ≤ C.addedGraph).trans
            (hheadAdded.trans le_sup_right)
        exact c.promote_ambient_le.trans (sup_le (sup_le le_sup_left hsib) hdir)
      exact R.ambient_le.trans (sup_le hfirst (htailAdded.trans le_sup_right))
    · intro w hw
      have hfirst := c.promote_cost_le w hw
      have htail := R.cost_le w hw
      have hfirst' : GraphCost.cost (fun e => w (e.map Subtype.val)) c.promote.graph ≤
          GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph + C.delta w := by
        change GraphCost.cost (fun e => w (e.map Subtype.val)) c.promote.graph ≤ _ at hfirst
        change GraphCost.cost (fun e => w (e.map Subtype.val)) c.promote.graph ≤
          GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph +
            (w s(C.primary, C.secondary) + w s(C.primary, C.attachment) -
              w s(C.center, C.secondary) - w s(C.center, C.attachment) - w s(C.center, C.primary))
        linarith
      rw [Finset.sum_insert hC]
      linarith

end SteinerUpperBound.Structural.Tree

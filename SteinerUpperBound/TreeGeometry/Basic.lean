module

public import SteinerUpperBound.Model
public import SteinerLowerBound.MetricComparison.Padding.Contraction

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open SteinerLowerBound
open scoped Classical BigOperators

variable {V W : Type*}

theorem cost_mono [Fintype V] (w : Sym2 V → ℝ)
    {G H : SimpleGraph V} (h : G ≤ H) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost w G ≤ GraphCost.cost w H :=
  Finset.sum_le_sum_of_subset_of_nonneg (SimpleGraph.edgeFinset_mono h)
    (fun e _ _ => hw e)

theorem cost_map_eq [Fintype V] [Fintype W] (G : SimpleGraph V)
    (f : V → W) (hf : Function.Injective f) (w : Sym2 W → ℝ) :
    GraphCost.cost w (G.map f) =
      GraphCost.cost (fun e => w (e.map f)) G := by
  classical
  let e : V ↪ W := ⟨f, hf⟩
  symm
  unfold GraphCost.cost
  apply Finset.sum_bij (fun a _ => a.map f)
  · intro a ha
    rcases a with ⟨x, y⟩
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at ha ⊢
    exact SimpleGraph.map_adj_apply' ha (hf.ne ha.ne)
  · intro a _ b _ hab
    exact e.sym2Map.injective hab
  · intro b hb
    rcases b with ⟨x, y⟩
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hb
    obtain ⟨_, a, b, hab, rfl, rfl⟩ :=
      (SimpleGraph.map_adj' _ _ _ _).mp hb
    refine ⟨s(a, b), ?_, rfl⟩
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hab
  · intro a _
    rfl

theorem reachable_map {G : SimpleGraph V} {x y : V}
    (h : G.Reachable x y) (f : V → W) :
    (G.map f).Reachable (f x) (f y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v z ha p ih =>
    by_cases he : f u = f v
    · simpa only [he] using ih
    · exact (SimpleGraph.map_adj_apply' ha he).reachable.trans ih

theorem induce_map_le (G : SimpleGraph V) (s : Set V) :
    (G.induce s).map Subtype.val ≤ G := by
  intro x y h
  obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
  exact hab

theorem cost_induce_le [Fintype V] (G : SimpleGraph V) (s : Finset V)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) (G.induce (s : Set V)) ≤
      GraphCost.cost w G := by
  rw [← cost_map_eq _ _ Subtype.val_injective]
  exact cost_mono w (induce_map_le G _) hw

/-- A tree has an explicit, finite set of selected vertices; unselected vertices do not
become spurious isolated vertices of the tree. -/
structure TreeSolution (I : Instance V) where
  vertices : Finset V
  contains : I.terminals ⊆ vertices
  graph : SimpleGraph ↥vertices
  isTree : graph.IsTree

namespace TreeSolution

variable {I : Instance V}

noncomputable def cost (S : TreeSolution I) : ℝ :=
  GraphCost.cost (fun e => I.weight (e.map Subtype.val)) S.graph

def ambient (S : TreeSolution I) : SimpleGraph V :=
  S.graph.map Subtype.val

theorem ambient_feasible (S : TreeSolution I) : Network.Feasible I.terminals S.ambient := by
  intro x hx y hy
  exact reachable_map (S.isTree.connected ⟨x, S.contains hx⟩ ⟨y, S.contains hy⟩) Subtype.val

theorem cost_ambient [Fintype V] (S : TreeSolution I) :
    GraphCost.cost I.weight S.ambient = S.cost :=
  cost_map_eq _ _ Subtype.val_injective _

theorem optimum_le_cost [Fintype V] (S : TreeSolution I) : I.optimum ≤ S.cost := by
  rw [← S.cost_ambient]
  exact I.optimum_le S.ambient S.ambient_feasible

theorem vertices_nonempty (S : TreeSolution I) : S.vertices.Nonempty := by
  obtain ⟨x⟩ := S.isTree.connected.nonempty
  exact ⟨x, x.property⟩

theorem edges_card (S : TreeSolution I) :
    S.graph.edgeFinset.card + 1 = S.vertices.card := by
  classical
  simpa only [Fintype.card_coe] using S.isTree.card_edgeFinset

end TreeSolution

theorem exists_tree_cost_le [Fintype V] (I : Instance V)
    (hT : I.terminals.Nonempty) (G : SimpleGraph V)
    (hG : Network.Feasible I.terminals G) :
    ∃ S : TreeSolution I, S.cost ≤ GraphCost.cost I.weight G := by
  classical
  obtain ⟨r, hr⟩ := hT
  let C := G.connectedComponentMk r
  let U := C.supp.toFinset
  have hU : (U : Set V) = C.supp := by
    ext x
    exact Set.mem_toFinset
  have hcontains : I.terminals ⊆ U := by
    intro x hx
    change x ∈ C.supp.toFinset
    rw [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound (hG x hx r hr)
  have hc : (G.induce (U : Set V)).Connected := by
    rw [hU]
    exact C.connected_toSimpleGraph
  obtain ⟨H, hH, ht⟩ := hc.exists_isTree_le
  refine ⟨⟨U, hcontains, H, ht⟩, ?_⟩
  exact (cost_mono _ hH (fun e => I.weight_nonneg _)).trans
    (cost_induce_le G U I.weight I.weight_nonneg)

theorem exists_tree_cost_le_subset [Fintype V] (I : Instance V)
    (hT : I.terminals.Nonempty) (G : SimpleGraph V)
    (hG : Network.Feasible I.terminals G) (U : Finset V)
    (hTU : I.terminals ⊆ U) (hGU : G.support ⊆ (U : Set V)) :
    ∃ S : TreeSolution I, S.vertices ⊆ U ∧ S.cost ≤ GraphCost.cost I.weight G := by
  classical
  obtain ⟨r, hr⟩ := hT
  let C := G.connectedComponentMk r
  let A := C.supp.toFinset
  have hA : (A : Set V) = C.supp := by
    ext x
    exact Set.mem_toFinset
  have hcontains : I.terminals ⊆ A := by
    intro x hx
    change x ∈ C.supp.toFinset
    rw [Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.sound (hG x hx r hr)
  have hsub : A ⊆ U := by
    intro x hx
    by_cases hxr : x = r
    · simpa only [hxr] using hTU hr
    · have hreach : G.Reachable x r := by
        apply SimpleGraph.ConnectedComponent.exact
        simpa only [A, Set.mem_toFinset, SimpleGraph.ConnectedComponent.mem_supp_iff] using hx
      exact hGU ((G.degree_pos_iff_mem_support x).mp (hreach.degree_pos_left hxr))
  have hc : (G.induce (A : Set V)).Connected := by
    rw [hA]
    exact C.connected_toSimpleGraph
  obtain ⟨H, hH, ht⟩ := hc.exists_isTree_le
  refine ⟨⟨A, hcontains, H, ht⟩, hsub, ?_⟩
  exact (cost_mono _ hH (fun e => I.weight_nonneg _)).trans
    (cost_induce_le G A I.weight I.weight_nonneg)

theorem optimum_tree_attained [Fintype V] (I : Instance V)
    (hT : I.terminals.Nonempty) :
    ∃ S : TreeSolution I, S.cost = I.optimum := by
  obtain ⟨G, hG, he⟩ := I.optimum_attained
  obtain ⟨S, hS⟩ := exists_tree_cost_le I hT G hG
  exact ⟨S, le_antisymm (hS.trans_eq he) S.optimum_le_cost⟩

end SteinerUpperBound.TreeGeometry

module

public import SteinerUpperBound.Structural.Exchange

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V W : Type*}

theorem cost_fintype_congr (i j : Fintype V) (w : Sym2 V → ℝ) (G : SimpleGraph V) :
    @GraphCost.cost V i w G = @GraphCost.cost V j w G := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

theorem cost_comap_equiv [Fintype V] [Fintype W] (G : SimpleGraph W)
    (e : V ≃ W) (w : Sym2 W → ℝ) :
    GraphCost.cost (fun a => w (a.map e)) (G.comap e) = GraphCost.cost w G := by
  have hg : (G.comap e).map e = G := by
    ext x y
    constructor
    · intro h
      obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
      exact hab
    · intro h
      exact (SimpleGraph.map_adj' _ _ _ _).mpr
        ⟨h.ne, e.symm x, e.symm y, by simpa using h, e.apply_symm_apply x, e.apply_symm_apply y⟩
  rw [← TreeGeometry.cost_map_eq _ _ e.injective, hg]

namespace Tree

variable {I : Instance V}

noncomputable abbrev eraseEmbedding (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices) :
    ↥(S.vertices.erase (v : V)) ↪ ↥S.vertices :=
  ⟨fun z => ⟨z.val, (Finset.mem_erase.mp z.property).2⟩,
    fun _ _ h => Subtype.ext (congrArg (fun z : ↥S.vertices => z.val) h)⟩

@[simp] theorem eraseEmbedding_val (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (z : ↥(S.vertices.erase (v : V))) : ((eraseEmbedding S v z : ↥S.vertices) : V) = (z : V) :=
  rfl

noncomputable abbrev eraseEquiv (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices) :
    ↥(S.vertices.erase (v : V)) ≃ ↥({v}ᶜ : Set ↥S.vertices) where
  toFun z := ⟨eraseEmbedding S v z, by
    intro h
    exact (Finset.mem_erase.mp z.property).1 (congrArg Subtype.val h)⟩
  invFun z := ⟨z.val.val, Finset.mem_erase.mpr
    ⟨fun h => z.property (Subtype.ext h), z.val.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

noncomputable abbrev eraseGraph (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (G : SimpleGraph ↥S.vertices) : SimpleGraph ↥(S.vertices.erase (v : V)) :=
  G.comap (eraseEmbedding S v)

theorem eraseGraph_leaf_tree (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (G : SimpleGraph ↥S.vertices) (ht : G.IsTree) (hd : G.degree v = 1) :
    (eraseGraph S v G).IsTree := by
  have ht' : (G.induce ({v}ᶜ : Set ↥S.vertices)).IsTree :=
    ⟨ht.connected.induce_compl_singleton_of_degree_eq_one hd, ht.isAcyclic.induce _⟩
  have h := (SimpleGraph.Iso.comap (eraseEquiv S v) (G.induce ({v}ᶜ : Set ↥S.vertices))).isTree_iff.mpr ht'
  exact h

theorem eraseGraph_cost_leaf_add (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (G : SimpleGraph ↥S.vertices) (x : ↥S.vertices) (hx : G.Adj v x)
    (hn : ∀ z, G.Adj v z → z = x) (w : Sym2 ↥S.vertices → ℝ) :
    GraphCost.cost (fun e => w (e.map (eraseEmbedding S v))) (eraseGraph S v G) +
      w s(v, x) = GraphCost.cost w G := by
  have hc : GraphCost.cost (fun e => w (e.map (eraseEmbedding S v))) (eraseGraph S v G) =
      GraphCost.cost (fun e => w (e.map Subtype.val)) (G.induce ({v}ᶜ : Set ↥S.vertices)) := by
    simpa [Sym2.map_map, Function.comp_def, eraseGraph, eraseEquiv, eraseEmbedding,
      SimpleGraph.induce, SimpleGraph.comap_comap] using
      cost_comap_equiv (G.induce ({v}ᶜ : Set ↥S.vertices)) (eraseEquiv S v)
        (fun e => w (e.map Subtype.val))
  rw [hc]
  convert TreeGeometry.cost_induce_leaf_add G w v x hx hn using 1
  congr 1
  exact cost_fintype_congr _ _ _ _

theorem terminals_subset_erase (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (hv : (v : V) ∉ I.terminals) : I.terminals ⊆ S.vertices.erase (v : V) := by
  intro x hx
  exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hx), S.contains hx⟩

noncomputable abbrev deleteLeaf (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (hv : (v : V) ∉ I.terminals) (hd : S.graph.degree v = 1) :
    TreeGeometry.TreeSolution I :=
  ⟨S.vertices.erase (v : V), terminals_subset_erase S v hv, eraseGraph S v S.graph,
    eraseGraph_leaf_tree S v S.graph S.isTree hd⟩

theorem deleteLeaf_cost_add (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (hv : (v : V) ∉ I.terminals) (hd : S.graph.degree v = 1)
    (w : Sym2 V → ℝ) :
    ∃ x : ↥S.vertices, S.graph.Adj v x ∧
      GraphCost.cost (fun e => w (e.map Subtype.val)) (deleteLeaf S v hv hd).graph +
        w s((v : V), (x : V)) =
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph := by
  obtain ⟨x, hx, hn⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
  refine ⟨x, hx, ?_⟩
  simpa only [deleteLeaf, Sym2.map_map, Function.comp_def, Sym2.map_mk,
    eraseEmbedding_val] using
    eraseGraph_cost_leaf_add S v S.graph x hx hn (fun e => w (e.map Subtype.val))

theorem deleteLeaf_preserves_terminals [Fintype V] (S : TreeGeometry.TreeSolution I)
    (v : ↥S.vertices) (hv : (v : V) ∉ I.terminals) (hd : S.graph.degree v = 1) :
    terminalGraph S ≤ terminalGraph (deleteLeaf S v hv hd) := by
  intro x y hxy
  obtain ⟨hxy, hT⟩ := hxy
  obtain ⟨hne, hxT, hyT⟩ := (Network.completeOn_adj _ _ _).mp hT
  obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hxy
  have ha : a.val ≠ v.val := fun h => hv (h ▸ hxT)
  have hb : b.val ≠ v.val := fun h => hv (h ▸ hyT)
  let a' : ↥(S.vertices.erase (v : V)) := ⟨a.val, Finset.mem_erase.mpr ⟨ha, a.property⟩⟩
  let b' : ↥(S.vertices.erase (v : V)) := ⟨b.val, Finset.mem_erase.mpr ⟨hb, b.property⟩⟩
  refine ⟨?_, hT⟩
  exact (SimpleGraph.map_adj' _ _ _ _).mpr ⟨hne, a', b', hab, rfl, rfl⟩

end Tree

end SteinerUpperBound.Structural

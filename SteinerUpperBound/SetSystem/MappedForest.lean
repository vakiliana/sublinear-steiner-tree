module

public import SteinerUpperBound.SetSystem.Forest
public import SteinerUpperBound.SetSystem.MapRank

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U V W : Type*}

theorem acyclic_of_rank_eq_edges [Fintype V] (G : SimpleGraph V)
    (hG : GraphRank.rank G = Nat.card G.edgeSet) : G.IsAcyclic := by
  classical
  let H := spanningForest G
  have hH : H.IsAcyclic := spanningForest_acyclic G
  have hr : GraphRank.rank H = GraphRank.rank G :=
    rank_eq_of_reachable H G (spanningForest_reachable G)
  have hc : Nat.card H.edgeSet = Nat.card G.edgeSet :=
    (forest_rank H hH).symm.trans (hr.trans hG)
  have hcf : H.edgeFinset.card = G.edgeFinset.card := by
    simpa only [SteinerLowerBound.GraphCost.edgeCount_eq_card] using hc
  have he : H.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono (spanningForest_le G)) hcf.symm.le
  have he' : H = G := by
    simpa only [GraphRank.ofEdges_edgeFinset] using congrArg GraphRank.ofEdges he
  exact he' ▸ hH

theorem acyclic_map [Fintype V] [Fintype W] (G : SimpleGraph V)
    (f : V → W) (hf : Function.Injective f) (hG : G.IsAcyclic) :
    (G.map f).IsAcyclic := by
  apply acyclic_of_rank_eq_edges
  rw [rank_map_injective G f hf, forest_rank G hG, edgeCount_map_injective G f hf]

noncomputable def mapPorts (ports : R → Finset U) (f : U → W) : R → Finset W :=
  fun r => (ports r).image f

theorem mem_mapPorts (ports : R → Finset U) (f : U → W) (r : R) (y : W) :
    y ∈ mapPorts ports f r ↔ ∃ x ∈ ports r, f x = y := by
  classical
  exact Finset.mem_image

theorem mapPorts_card (ports : R → Finset U) (f : U → W)
    (hf : Function.Injective f) (r : R) :
    (mapPorts ports f r).card = (ports r).card := by
  classical
  exact Finset.card_image_of_injective _ hf

theorem incidence_map_elements (ports : R → Finset U) (f : U → W) :
    incidenceGraph (mapPorts ports f) =
      (incidenceGraph ports).map (Sum.map f id) := by
  classical
  ext a b
  cases a <;> cases b <;>
    simp [mapPorts, incidenceGraph, SimpleGraph.map_adj', Sum.exists, Finset.mem_image, eq_comm]

theorem portGraph_map_elements (ports : R → Finset U) (f : U → W) :
    portGraph (mapPorts ports f) = (portGraph ports).map f := by
  classical
  ext a b
  constructor
  · rintro ⟨hab, r, ha, hb⟩
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp hb
    have hxy : x ≠ y := by
      intro he
      exact hab (hfx.symm.trans ((congrArg f he).trans hfy))
    exact (SimpleGraph.map_adj' f _ a b).mpr ⟨hab, x, y, ⟨hxy, r, hx, hy⟩, hfx, hfy⟩
  · intro h
    obtain ⟨hab, x, y, hxy, hfx, hfy⟩ := (SimpleGraph.map_adj' f _ a b).mp h
    obtain ⟨_, r, hx, hy⟩ := hxy
    exact ⟨hab, r, Finset.mem_image.mpr ⟨x, hx, hfx⟩,
      Finset.mem_image.mpr ⟨y, hy, hfy⟩⟩

theorem saving_forest_on_universe (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (hlarge : ∀ r ∈ E, 3 ≤ (A ∩ rows r).card) :
    ∃ (S : Finset R) (ports : ↥S → Finset ↥A),
      S ⊆ E ∧
      (∀ r, ∀ x ∈ ports r, x.val ∈ rows r.val) ∧
      (∀ r, 3 ≤ (ports r).card) ∧
      (incidenceGraph ports).IsAcyclic ∧
      saving E rows A / 2 ≤ (∑ r, ((ports r).card : ℝ)) - 2 * S.card ∧
      3 * S.card ≤ ∑ r, (ports r).card ∧
      GraphRank.rank (portGraph ports) + S.card = ∑ r, (ports r).card := by
  classical
  obtain ⟨B, S, P, hBA, hSE, hsound, hdegree, hforest, hprofit, hcount, _⟩ :=
    saving_forest E rows A hlarge
  let f : ↥B → ↥A := fun x => ⟨x.val, hBA x.property⟩
  have hf : Function.Injective f := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : ↥A => z.val) he)
  let ports : ↥S → Finset ↥A := mapPorts P f
  have hcard (r : ↥S) : (ports r).card = (P r).card := mapPorts_card P f hf r
  have hdeg (r : ↥S) : 3 ≤ (ports r).card := (hcard r).symm ▸ hdegree r
  have hacyc : (incidenceGraph ports).IsAcyclic := by
    change (incidenceGraph (mapPorts P f)).IsAcyclic
    rw [incidence_map_elements]
    apply acyclic_map _ _ (by
      intro a b he
      cases a <;> cases b <;> simp_all [hf.eq_iff]) hforest
  have hsound' (r : ↥S) (x : ↥A) (hx : x ∈ ports r) : x.val ∈ rows r.val := by
    obtain ⟨y, hy, rfl⟩ := (mem_mapPorts P f r x).mp hx
    exact hsound r y hy
  have hprofit' : saving E rows A / 2 ≤ (∑ r, ((ports r).card : ℝ)) - 2 * S.card := by
    simpa only [hcard] using hprofit
  have hcount' : 3 * S.card ≤ ∑ r, (ports r).card := by
    simpa only [hcard] using hcount
  have hrank := incidence_forest_port_rank ports
    (fun r => Finset.card_pos.mp (by have := hdeg r; omega)) hacyc
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hrank
  exact ⟨S, ports, hSE, hsound', hdeg, hacyc, hprofit', hcount', hrank⟩

theorem saving_forest_edges (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (hlarge : ∀ r ∈ E, 3 ≤ (A ∩ rows r).card) :
    ∃ (S : Finset R) (ports : ↥S → Finset ↥A),
      S ⊆ E ∧
      (∀ r, ∀ x ∈ ports r, x.val ∈ rows r.val) ∧
      (∀ r, 3 ≤ (incidenceGraph ports).degree (Sum.inr r)) ∧
      (incidenceGraph ports).IsAcyclic ∧
      saving E rows A / 2 ≤
        (Nat.card (incidenceGraph ports).edgeSet : ℝ) - 2 * S.card ∧
      3 * S.card ≤ Nat.card (incidenceGraph ports).edgeSet ∧
      GraphRank.rank (portGraph ports) + S.card = Nat.card (incidenceGraph ports).edgeSet := by
  classical
  obtain ⟨S, ports, hSE, hsound, hdegree, hforest, hprofit, hcount, hrank⟩ :=
    saving_forest_on_universe E rows A hlarge
  refine ⟨S, ports, hSE, hsound, ?_, hforest, ?_, ?_, ?_⟩
  · simpa only [incidence_row_degree] using hdegree
  · simpa only [incidence_edges_card, Nat.cast_sum] using hprofit
  · simpa only [incidence_edges_card] using hcount
  · simpa only [incidence_edges_card] using hrank

end SteinerUpperBound.SetSystem

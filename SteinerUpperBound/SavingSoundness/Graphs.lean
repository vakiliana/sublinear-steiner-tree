module

public import SteinerUpperBound.NetworkLifting
public import SteinerUpperBound.SetSystem.MappedForest
public import SteinerUpperBound.Structural.Exchange

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open SteinerLowerBound
open scoped Classical BigOperators

variable {V J C W : Type*}

noncomputable def graphUnion (graphs : J → SimpleGraph V) : SimpleGraph V := ⨆ j, graphs j

theorem graphUnion_adj (graphs : J → SimpleGraph V) (x y : V) :
    (graphUnion graphs).Adj x y ↔ ∃ j, (graphs j).Adj x y := by
  simp [graphUnion]

theorem le_graphUnion (graphs : J → SimpleGraph V) (j : J) : graphs j ≤ graphUnion graphs :=
  le_iSup graphs j

theorem graphUnion_edge (graphs : J → SimpleGraph V) (e : Sym2 V) :
    e ∈ (graphUnion graphs).edgeSet ↔ ∃ j, e ∈ (graphs j).edgeSet := by
  induction e using Sym2.inductionOn with
  | _ x y => simp only [SimpleGraph.mem_edgeSet, graphUnion_adj]

theorem contribution_nonneg (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (G : SimpleGraph V) (e : Sym2 V) : 0 ≤ SpanningForest.contribution w G e := by
  unfold SpanningForest.contribution
  split_ifs
  · exact hw e
  · rfl

theorem graphUnion_cost [Fintype V] [Fintype J] (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (graphs : J → SimpleGraph V) :
    GraphCost.cost w (graphUnion graphs) ≤ ∑ j, GraphCost.cost w (graphs j) := by
  have hp (e : Sym2 V) : SpanningForest.contribution w (graphUnion graphs) e ≤
      ∑ j, SpanningForest.contribution w (graphs j) e := by
    by_cases he : e ∈ (graphUnion graphs).edgeSet
    · obtain ⟨j, hj⟩ := (graphUnion_edge graphs e).mp he
      have hh := Finset.single_le_sum
        (fun k _ => contribution_nonneg w hw (graphs k) e) (Finset.mem_univ j)
      simpa only [SpanningForest.contribution, ite_eq_left he, ite_eq_left hj] using hh
    · simp only [SpanningForest.contribution, ite_eq_right he]
      exact Finset.sum_nonneg (fun j _ => by
        split_ifs
        · exact hw e
        · rfl)
  calc
    _ = ∑ e, SpanningForest.contribution w (graphUnion graphs) e := SpanningForest.cost_sum _ _
    _ ≤ ∑ e, ∑ j, SpanningForest.contribution w (graphs j) e :=
      Finset.sum_le_sum (fun e _ => hp e)
    _ = ∑ j, ∑ e, SpanningForest.contribution w (graphs j) e := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun j _ => (SpanningForest.cost_sum _ _).symm)

theorem edge_reachable (x y : V) : (SimpleGraph.edge x y).Reachable x y := by
  by_cases he : x = y
  · subst y; exact SimpleGraph.Reachable.refl _
  · exact ((SimpleGraph.edge_adj x y x y).mpr ⟨Or.inl ⟨rfl, rfl⟩, he⟩).reachable

noncomputable def chosenSets (ports : J → Finset C)
    (pick : ∀ j, ↥(ports j) → V) (j : J) : Finset V :=
  (ports j).attach.image (pick j)

theorem mem_chosenSets (ports : J → Finset C) (pick : ∀ j, ↥(ports j) → V)
    (j : J) (x : V) : x ∈ chosenSets ports pick j ↔ ∃ c, pick j c = x := by
  classical
  simp only [chosenSets, Finset.mem_image, Finset.mem_attach, true_and]

noncomputable def chosenLinks (ports : J → Finset C)
    (pick : ∀ j, ↥(ports j) → V) : SimpleGraph V :=
  SetSystem.portGraph (chosenSets ports pick)

noncomputable def chosenStars (ports : J → Finset C)
    (center : J → V) (pick : ∀ j, ↥(ports j) → V) : SimpleGraph V :=
  graphUnion (fun p : Σ j, ↥(ports j) => SimpleGraph.edge (center p.1) (pick p.1 p.2))

theorem star_leg (ports : J → Finset C) (center : J → V)
    (pick : ∀ j, ↥(ports j) → V) (j : J) (c : ↥(ports j)) :
    (chosenStars ports center pick).Reachable (center j) (pick j c) :=
  (edge_reachable _ _).mono (le_graphUnion _ ⟨j, c⟩)

theorem chosenLinks_connect (ports : J → Finset C) (center : J → V)
    (pick : ∀ j, ↥(ports j) → V) :
    ∀ x y, (chosenLinks ports pick).Adj x y →
      (chosenStars ports center pick).Reachable x y := by
  rintro x y ⟨_, j, hx, hy⟩
  obtain ⟨c, rfl⟩ := (mem_chosenSets ports pick j x).mp hx
  obtain ⟨d, rfl⟩ := (mem_chosenSets ports pick j y).mp hy
  exact (star_leg ports center pick j c).symm.trans (star_leg ports center pick j d)

theorem chosenLinks_terminalOnly (T : Finset V) (ports : J → Finset C)
    (pick : ∀ j, ↥(ports j) → V) (hT : ∀ j c, pick j c ∈ T) :
    Network.TerminalOnly T (chosenLinks ports pick) := by
  rintro x y ⟨_, j, hx, hy⟩
  obtain ⟨c, rfl⟩ := (mem_chosenSets ports pick j x).mp hx
  obtain ⟨d, rfl⟩ := (mem_chosenSets ports pick j y).mp hy
  exact ⟨hT j c, hT j d⟩

theorem chosenLinks_diameter (I : Instance V) (ports : J → Finset C)
    (center : J → V) (pick : ∀ j, ↥(ports j) → V) (radius : ℝ)
    (hnear : ∀ j c, I.distance (center j) (pick j c) ≤ radius) :
    ∀ x y, (chosenLinks ports pick).Adj x y → I.distance x y ≤ 2 * radius := by
  rintro x y ⟨_, j, hx, hy⟩
  obtain ⟨c, rfl⟩ := (mem_chosenSets ports pick j x).mp hx
  obtain ⟨d, rfl⟩ := (mem_chosenSets ports pick j y).mp hy
  have ht := I.distance_triangle (pick j c) (center j) (pick j d)
  rw [I.distance_comm (pick j c) (center j)] at ht
  linarith [hnear j c, hnear j d]

theorem chosenStars_cost [Fintype V] [Fintype J] (I : Instance V)
    (ports : J → Finset C) (center : J → V) (pick : ∀ j, ↥(ports j) → V)
    (radius : ℝ) (hnear : ∀ j c, I.distance (center j) (pick j c) ≤ radius) :
    GraphCost.cost I.weight (chosenStars ports center pick) ≤
      radius * (∑ j, ((ports j).card : ℝ)) := by
  calc
    _ ≤ ∑ p : Σ j, ↥(ports j),
        GraphCost.cost I.weight (SimpleGraph.edge (center p.1) (pick p.1 p.2)) :=
      graphUnion_cost I.weight I.weight_nonneg _
    _ ≤ ∑ _p : Σ j, ↥(ports j), radius := Finset.sum_le_sum (fun p _ =>
      (Structural.cost_edge_le I.weight I.weight_nonneg _ _).trans
        (by simpa only [Instance.weight_mk] using hnear p.1 p.2))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sigma,
        Fintype.card_coe, nsmul_eq_mul, Nat.cast_sum]
      ring

theorem chosenSets_image (ports : J → Finset C) (pick : ∀ j, ↥(ports j) → V)
    (q : V → W) (embed : C → W) (hq : ∀ j c, q (pick j c) = embed c.val) :
    SetSystem.mapPorts (chosenSets ports pick) q = SetSystem.mapPorts ports embed := by
  classical
  funext j
  ext y
  rw [SetSystem.mem_mapPorts, SetSystem.mem_mapPorts]
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨c, rfl⟩ := (mem_chosenSets ports pick j x).mp hx
    exact ⟨c.val, c.property, (hq j c).symm.trans hxy⟩
  · rintro ⟨c, hc, hcy⟩
    let c' : ↥(ports j) := ⟨c, hc⟩
    exact ⟨pick j c', (mem_chosenSets ports pick j _).mpr ⟨c', rfl⟩,
      (hq j c').trans hcy⟩

theorem chosenLinks_map (ports : J → Finset C) (pick : ∀ j, ↥(ports j) → V)
    (q : V → W) (embed : C → W) (hq : ∀ j c, q (pick j c) = embed c.val) :
    (chosenLinks ports pick).map q = (SetSystem.portGraph ports).map embed := by
  rw [chosenLinks, ← SetSystem.portGraph_map_elements,
    chosenSets_image ports pick q embed hq, SetSystem.portGraph_map_elements]

end SteinerUpperBound.SavingSoundness

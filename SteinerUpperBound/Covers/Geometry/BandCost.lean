module

public import SteinerUpperBound.Covers.Geometry.BandRank

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandCompleteness

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

/-- Only witness terminals move. An optional Steiner center outside the witness
is fixed, so the mapped network is still a one-center network. -/
noncomputable def witnessMap (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (Y : Finset V) (x : V) : V :=
  if x ∈ Y then project I I.terminals N ρ hc x else x

theorem witnessMap_on (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (Y : Finset V) {x : V} (hx : x ∈ Y) :
    witnessMap I N ρ hc Y x = project I I.terminals N ρ hc x := by
  simp [witnessMap, hx]

theorem witnessMap_move (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ)
    (Y : Finset V) (hY : Y ⊆ I.terminals) (x : V) :
    I.distance x (witnessMap I N ρ hc Y x) ≤ ρ := by
  by_cases hx : x ∈ Y
  · rw [witnessMap_on I N ρ hc Y hx]
    exact project_move I I.terminals N ρ hc hρ (hY hx)
  · simpa only [witnessMap, hx, ↓reduceIte, I.distance_self] using hρ

theorem witnessMap_distance (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ)
    (Y : Finset V) (hY : Y ⊆ I.terminals) (x y : V) :
    I.distance (witnessMap I N ρ hc Y x) (witnessMap I N ρ hc Y y) ≤
      I.distance x y + 2 * ρ := by
  have hx := witnessMap_move I N ρ hc hρ Y hY x
  have hy := witnessMap_move I N ρ hc hρ Y hY y
  have ht₁ := I.distance_triangle (witnessMap I N ρ hc Y x) x (witnessMap I N ρ hc Y y)
  have ht₂ := I.distance_triangle x y (witnessMap I N ρ hc Y y)
  rw [I.distance_comm (witnessMap I N ρ hc Y x) x] at ht₁
  linarith

theorem terminalOnly_edges_card (G : SimpleGraph V) (S : Finset V)
    (hG : Network.TerminalOnly S G) : G.edgeFinset.card ≤ S.card ^ 2 := by
  classical
  have hsub : G.edgeFinset ⊆ (S.product S).image (fun xy => Sym2.mk xy.1 xy.2) := by
    intro e he
    rcases e with ⟨x, y⟩
    have hxy : G.Adj x y := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    obtain ⟨hx, hy⟩ := hG x y hxy
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  have hc : G.edgeFinset.card ≤ (S.product S).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.product_eq_sprod, Finset.card_product] at hc
  simpa only [pow_two] using hc

theorem mapped_oneCenter (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (Y : Finset V) (G : SimpleGraph V)
    (hG : Structural.OneCenterNetwork Y G) :
    Structural.OneCenterNetwork (projected I N ρ hc Y) (G.map (witnessMap I N ρ hc Y)) := by
  classical
  obtain ⟨hfeas, U, hU, hterm⟩ := hG
  refine ⟨?_, U, hU, ?_⟩
  · intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hr := Network.reachable_map G (witnessMap I N ρ hc Y) (hfeas u hu v hv)
    simpa only [witnessMap_on I N ρ hc Y hu, witnessMap_on I N ρ hc Y hv] using hr
  · intro x y hxy
    obtain ⟨_, u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hxy
    obtain ⟨hu, hv⟩ := hterm u v huv
    have hm (z : V) (hz : z ∈ Y ∪ U) :
        witnessMap I N ρ hc Y z ∈ projected I N ρ hc Y ∪ U := by
      by_cases hzY : z ∈ Y
      · apply Finset.mem_union.mpr
        exact Or.inl (Finset.mem_image.mpr ⟨z, hzY, witnessMap_on I N ρ hc Y hzY |>.symm⟩)
      · have hzU : z ∈ U := (Finset.mem_union.mp hz).resolve_left hzY
        simpa [witnessMap, hzY] using Finset.mem_union_right (projected I N ρ hc Y) hzU
    exact ⟨hm u hu, hm v hv⟩

/-- A conservative bound avoids assuming an unproved cleaned one-center
optimizer: every attained network has at most `5²` possible edges. -/
theorem localCost_projected_le (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hρ : 0 ≤ ρ)
    (Y : Finset V) (hY : Y ⊆ I.terminals) (h4 : Y.card ≤ 4) :
    Structural.localCost I (projected I N ρ hc Y) ≤ Structural.localCost I Y + 50 * ρ := by
  classical
  obtain ⟨G, hG, hcost⟩ := Structural.localCost_attained I Y
  have hle := Structural.localCost_le I (projected I N ρ hc Y)
    (G.map (witnessMap I N ρ hc Y)) (mapped_oneCenter I N ρ hc Y G hG)
  have hmap : GraphCost.cost I.weight (G.map (witnessMap I N ρ hc Y)) ≤
      GraphCost.cost (fun e => I.weight e + 2 * ρ) G := by
    apply MetricComparison.Padding.cost_map_le G (witnessMap I N ρ hc Y)
      (fun e => I.weight e + 2 * ρ) I.weight I.weight_nonneg
    intro e _
    rcases e with ⟨x, y⟩
    simpa only [Sym2.map_mk, Instance.weight_mk] using
      witnessMap_distance I N ρ hc hρ Y hY x y
  have hcount : G.edgeFinset.card ≤ 25 := by
    obtain ⟨U, hU, hterm⟩ := hG.2
    have hsize : (Y ∪ U).card ≤ 5 := (Finset.card_union_le _ _).trans (by omega)
    have he := terminalOnly_edges_card G (Y ∪ U) hterm
    nlinarith
  have hcountR : (G.edgeFinset.card : ℝ) ≤ 25 := by exact_mod_cast hcount
  have hsum : GraphCost.cost (fun e => I.weight e + 2 * ρ) G =
      GraphCost.cost I.weight G + (G.edgeFinset.card : ℝ) * (2 * ρ) := by
    simp [GraphCost.cost, Finset.sum_add_distrib]
  rw [hsum, hcost] at hmap
  exact hle.trans (hmap.trans (by nlinarith))

end SteinerUpperBound.Covers.Geometry.BandCompleteness

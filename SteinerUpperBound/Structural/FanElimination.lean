module

public import SteinerUpperBound.Structural.FanPromotionConstruction

@[expose] public section

namespace SteinerUpperBound.Structural.Tree.Fan

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}
variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

theorem eliminate_weighted_of_order (F : Fan S parent v)
    (horder : I.distance v F.left.primary ≤ I.distance v F.right.primary)
    (a b : V) (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ F.region) (hbR : b ∉ F.region) :
    ∃ Z : TreeGeometry.TreeSolution I, Z.vertices ⊆ S.vertices ∧
      terminalGraph S ≤ terminalGraph Z ∧
      ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
        GraphCost.cost (fun e => w (e.map Subtype.val)) Z.graph ≤
          GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
            w s((parent : V), (v : V)) - F.left.edgeWeight w - F.right.edgeWeight w +
            F.left.siblingWeight w + F.right.siblingWeight w +
            w s((F.left.primary : V), (F.right.primary : V)) + w s(b, a) := by
  obtain ⟨R⟩ := F.fullyPromoted_exists
  let C : Cherry R.solution R.parentVertex :=
    { center := R.centerVertex
      primary := R.fan.left.primary
      secondary := R.fan.right.primary
      attachment_nonterminal := R.fan.parent_nonterminal
      center_nonterminal := R.fan.center_nonterminal
      primary_terminal := R.fan.left.primary_terminal
      secondary_terminal := R.fan.right.primary_terminal
      ports_ne := R.fan.ports_ne
      trunk := R.fan.parent_edge
      primary_arm := by simpa only [R.left_direct] using R.fan.left.stem_adj
      secondary_arm := by simpa only [R.right_direct] using R.fan.right.stem_adj
      neighbors := by
        intro z hz
        simpa only [R.left_direct, R.right_direct] using R.fan.neighbors z hz
      ordered := by
        rw [R.center_val, R.left_val, R.right_val]
        exact horder }
  have hK : ClosedCut (Network.completeOn F.localVertices) (F.region : Set V) := by
    intro x y hxy
    obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj _ _ _).mp hxy
    exact iff_of_true (F.localVertices_in_region hx) (F.localVertices_in_region hy)
  have hregion := region_eq_under_additions S R.solution parent v F.parent_edge
    R.parentVertex R.centerVertex R.parent_val R.center_val
    (Network.completeOn F.localVertices) R.ambient_le hK
  let a' : ↥R.solution.vertices := ⟨a, R.solution.contains ha⟩
  let b' : ↥R.solution.vertices := ⟨b, R.solution.contains hb⟩
  have hca : (R.solution.graph.deleteEdges {s(R.parentVertex, R.centerVertex)}).Reachable
      R.centerVertex a' := (mem_region _ _ _ _).mp ((hregion a').mpr haR)
  have hcb : ¬ (R.solution.graph.deleteEdges {s(R.parentVertex, R.centerVertex)}).Reachable
      R.centerVertex b' := fun h => hbR ((hregion b').mp ((mem_region _ _ _ _).mpr h))
  have hpb := (delete_edge_two_sides R.solution.graph R.solution.isTree.connected
    R.parentVertex R.centerVertex b').resolve_right hcb
  let Z := C.eliminate a' b' hca hpb ha hb
  refine ⟨Z, (Finset.erase_subset _ _).trans R.vertices_subset,
    R.permanent.trans (C.eliminate_preserves_terminals a' b' hca hpb ha hb), ?_⟩
  intro w hw
  have hp := R.cost_le w hw
  have he := C.eliminate_cost_le a' b' hca hpb ha hb w hw
  change GraphCost.cost (fun e => w (e.map Subtype.val)) Z.graph ≤
    GraphCost.cost (fun e => w (e.map Subtype.val)) R.solution.graph -
      w s((R.centerVertex : V), (R.fan.right.primary : V)) -
      w s((R.parentVertex : V), (R.centerVertex : V)) -
      w s((R.centerVertex : V), (R.fan.left.primary : V)) +
      w s((R.fan.left.primary : V), (R.fan.right.primary : V)) + w s(b, a) at he
  rw [R.center_val, R.parent_val, R.left_val, R.right_val] at he
  linarith

theorem eliminate_weighted (F : Fan S parent v)
    (a b : V) (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ F.region) (hbR : b ∉ F.region) :
    ∃ Z : TreeGeometry.TreeSolution I, Z.vertices ⊆ S.vertices ∧
      terminalGraph S ≤ terminalGraph Z ∧
      ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
        GraphCost.cost (fun e => w (e.map Subtype.val)) Z.graph ≤
          GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
            w s((parent : V), (v : V)) - F.left.edgeWeight w - F.right.edgeWeight w +
            F.left.siblingWeight w + F.right.siblingWeight w +
            w s((F.left.primary : V), (F.right.primary : V)) + w s(b, a) := by
  by_cases h : I.distance v F.left.primary ≤ I.distance v F.right.primary
  · exact F.eliminate_weighted_of_order h a b ha hb haR hbR
  · obtain ⟨Z, hsub, hperm, hc⟩ :=
      F.swap.eliminate_weighted_of_order (le_of_not_ge h) a b ha hb haR hbR
    refine ⟨Z, hsub, hperm, ?_⟩
    intro w hw
    have hh := hc w hw
    change GraphCost.cost (fun e => w (e.map Subtype.val)) Z.graph ≤
      GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph -
        w s((parent : V), (v : V)) - F.right.edgeWeight w - F.left.edgeWeight w +
        F.right.siblingWeight w + F.left.siblingWeight w +
        w s((F.right.primary : V), (F.left.primary : V)) + w s(b, a) at hh
    have he : w s((F.right.primary : V), (F.left.primary : V)) =
        w s((F.left.primary : V), (F.right.primary : V)) := congrArg w Sym2.eq_swap
    rw [he] at hh
    linarith

theorem eliminate_reduces (F : Fan S parent v)
    (a b : V) (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ F.region) (hbR : b ∉ F.region)
    (hcost : F.internalCost + I.distance a b ≤
      chi * (I.distance parent v + F.left.cost + F.right.cost)) :
    ∃ Z : TreeGeometry.TreeSolution I, Reduces S Z := by
  classical
  obtain ⟨Z, hsub, hperm, hc⟩ := F.eliminate_weighted a b ha hb haR hbR
  have hpot := hc (potentialWeight I) (potentialWeight_nonneg I)
  rw [Limb.edgeWeight_potential, Limb.edgeWeight_potential,
    Limb.siblingWeight_potential, Limb.siblingWeight_potential] at hpot
  simp only [potentialWeight_mk, potentialDistance, F.parent_nonterminal, F.center_nonterminal,
    F.left.primary_terminal, F.right.primary_terminal, ha, hb, false_and, and_self, ↓reduceIte] at hpot
  rw [I.distance_comm b a] at hpot
  have hnn := hc (nonterminalWeight I) (nonterminalWeight_nonneg I)
  rw [Limb.siblingWeight_nonterminal, Limb.siblingWeight_nonterminal] at hnn
  have hnold := F.left.edgeWeight_nonneg (nonterminalWeight I) (nonterminalWeight_nonneg I)
  have hnold' := F.right.edgeWeight_nonneg (nonterminalWeight I) (nonterminalWeight_nonneg I)
  have hparent := nonterminalWeight_nonneg I s((parent : V), (v : V))
  have hnewNN : nonterminalWeight I s((F.left.primary : V), (F.right.primary : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, F.left.primary_terminal]
  have hcrossNN : nonterminalWeight I s(b, a) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, hb]
  rw [hnewNN, hcrossNN] at hnn
  have hports : (F.left.primary : V) ≠ (F.right.primary : V) :=
    fun h => F.ports_ne (Subtype.ext h)
  have hba : b ≠ a := by
    intro h
    subst b
    exact hbR haR
  have hnewC : steinerCountWeight I s((F.left.primary : V), (F.right.primary : V)) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj,
      hports, F.left.primary_terminal, F.right.primary_terminal]
  have hcrossC : steinerCountWeight I s(b, a) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj, hba, hb, ha]
  have hcount := hc (steinerCountWeight I) (steinerCountWeight_nonneg I)
  rw [Limb.siblingWeight_count, Limb.siblingWeight_count, hnewC, hcrossC,
    steinerCountWeight_incident I F.parent_nonterminal, steinerCountWeight_cost Z,
      steinerCountWeight_cost S] at hcount
  have hl := F.left.edgeWeight_count_ge_one
  have hr := F.right.edgeWeight_count_ge_one
  have hcountN : (steinerEdges Z).card + 1 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges Z).card : ℝ) + 1 ≤ (steinerEdges S).card by linarith)
  refine ⟨Z, hsub, hperm, ?_, ?_, Nat.lt_of_succ_le hcountN⟩
  · unfold internalCost at hcost
    change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Z.graph ≤
      GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph
    nlinarith
  · change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) Z.graph ≤
      GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) S.graph
    linarith

theorem crossing_barrier (F : Fan S parent v) (hred : Reduced S)
    (a b : V) (ha : a ∈ I.terminals) (hb : b ∈ I.terminals)
    (haR : a ∈ F.region) (hbR : b ∉ F.region) :
    chi * I.distance parent v + b0 * F.pair.totalLength < I.distance a b := by
  have hh : chi * (I.distance parent v + F.left.cost + F.right.cost) <
      F.internalCost + I.distance a b := by
    by_contra h
    obtain ⟨Z, hz⟩ := F.eliminate_reduces a b ha hb haR hbR (le_of_not_gt h)
    exact hred Z hz
  have hleft := F.left.fan_barrier_contribution
  have hright := F.right.fan_barrier_contribution
  have hports := F.pair.port_distance_le
  change I.distance F.left.primary F.right.primary ≤ F.left.length + F.right.length at hports
  unfold internalCost at hh
  change chi * I.distance parent v + b0 * (F.left.length + F.right.length) < I.distance a b
  nlinarith

theorem regular_region_closed (F : Fan S parent v) (hred : Reduced S)
    (hparent : delta0 * F.pair.totalLength ≤ I.distance parent v)
    (a : ℝ) (ha : a ≤ omega * F.pair.totalLength / (chi - 1)) :
    ClosedCut (threshold I a ⊔ terminalGraph S) (F.region : Set V) := by
  apply threshold_sup_closedCut I (terminalGraph S) _ a a le_rfl
  · intro x hx y hy hxR hyR
    have hb := F.crossing_barrier hred x y hx hy hxR hyR
    have hpos : 0 < F.pair.totalLength := add_pos F.left.length_pos F.right.length_pos
    norm_num [delta0, omega, chi, e0, b0, p] at hparent ha hb
    linarith
  · exact terminalGraph_region_closed S parent v F.parent_nonterminal

theorem regular_component_contained (F : Fan S parent v) (hred : Reduced S)
    (hparent : delta0 * F.pair.totalLength ≤ I.distance parent v)
    (a : ℝ) (ha : a ≤ omega * F.pair.totalLength / (chi - 1)) :
    component I a F.left.primary ⊆ F.region := by
  intro x hx
  have hreach := (mem_component I a F.left.primary x).mp hx |>.2
  have hc := F.regular_region_closed hred hparent a ha
  exact (hc.reachable (hreach.mono le_sup_left)).mp
    (F.limb_primary_in_region F.left F.parent_ne_left)

end SteinerUpperBound.Structural.Tree.Fan

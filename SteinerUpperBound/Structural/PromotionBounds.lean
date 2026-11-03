module

public import SteinerUpperBound.Structural.FringeGroups

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

noncomputable abbrev smallCoefficient : ℝ := alpha0 / ((1 - alpha0) * (chi - 1))

theorem smallCoefficient_lt : smallCoefficient < (1 / 90 : ℝ) := by
  norm_num [smallCoefficient, alpha0, chi, e0]

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable def trunkWeight (L : Limb S v) : ℝ :=
  match L with
  | .direct _ _ _ _ => 0
  | .cherry C => I.distance v C.center

def Small (L : Limb S v) : Prop :=
  match L with
  | .direct _ _ _ _ => True
  | .cherry C => I.distance C.center C.primary < alpha0 * L.length

theorem edgeWeight_nonterminal (L : Limb S v) :
    L.edgeWeight (nonterminalWeight I) = L.trunkWeight := by
  cases L with
  | direct x hv hx h => simp [edgeWeight, trunkWeight, nonterminalWeight_mk, nonterminalDistance, hx]
  | cherry C =>
    simp [edgeWeight, trunkWeight, nonterminalWeight_mk, nonterminalDistance,
      C.attachment_nonterminal, C.center_nonterminal, C.primary_terminal, C.secondary_terminal]

theorem edgeWeight_count (L : Limb S v) :
    L.edgeWeight (steinerCountWeight I) = 1 + 2 * (L.cherryCount : ℝ) := by
  cases L with
  | direct x hv hx h =>
    simp [edgeWeight, cherryCount, steinerCountWeight_incident I hv]
  | cherry C =>
    norm_num [edgeWeight, cherryCount, steinerCountWeight_incident I C.attachment_nonterminal,
      steinerCountWeight_incident I C.center_nonterminal]

theorem small_charge_le (L : Limb S v) (hred : Reduced S) (hsmall : L.Small) :
    L.longerArm ≤ smallCoefficient * L.trunkWeight := by
  cases L with
  | direct x hv hx h => simp [longerArm, trunkWeight]
  | cherry C => exact (C.small_charge hred hsmall).le

end Limb

namespace Fan

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

def Small (F : Fan S parent v) : Prop := F.left.Small ∧ F.right.Small

noncomputable abbrev promotionCharge (F : Fan S parent v) : ℝ :=
  F.left.longerArm + F.right.longerArm

theorem FullyPromoted.potential_bound (F : Fan S parent v) (R : FullyPromoted F) :
    potential R.solution ≤ potential S + (2 - chi) * F.promotionCharge := by
  have hh := R.cost_le (potentialWeight I) (potentialWeight_nonneg I)
  have hleft := F.left.potential_reconnection_bound
  have hright := F.right.potential_reconnection_bound
  rw [Limb.edgeWeight_potential, Limb.edgeWeight_potential] at hh
  change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) R.solution.graph ≤
    GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph +
      (2 - chi) * (F.left.longerArm + F.right.longerArm)
  rw [Limb.edgeWeight_potential] at hleft hright
  nlinarith

theorem FullyPromoted.nonterminalCost_bound (F : Fan S parent v) (R : FullyPromoted F) :
    nonterminalCost R.solution ≤ nonterminalCost S - F.left.trunkWeight - F.right.trunkWeight := by
  have hh := R.cost_le (nonterminalWeight I) (nonterminalWeight_nonneg I)
  rw [Limb.edgeWeight_nonterminal, Limb.edgeWeight_nonterminal,
    Limb.siblingWeight_nonterminal, Limb.siblingWeight_nonterminal] at hh
  have hleft : nonterminalWeight I s((v : V), (F.left.primary : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, F.left.primary_terminal]
  have hright : nonterminalWeight I s((v : V), (F.right.primary : V)) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, F.right.primary_terminal]
  simpa only [nonterminalCost, hleft, hright, add_zero] using hh

theorem FullyPromoted.steinerEdges_lt (F : Fan S parent v) (R : FullyPromoted F)
    (hhas : 0 < F.cherryCount) :
    (steinerEdges R.solution).card < (steinerEdges S).card := by
  have hh := R.cost_le (steinerCountWeight I) (steinerCountWeight_nonneg I)
  rw [Limb.edgeWeight_count, Limb.edgeWeight_count, Limb.siblingWeight_count,
    Limb.siblingWeight_count, steinerCountWeight_incident I F.center_nonterminal,
    steinerCountWeight_incident I F.center_nonterminal,
    steinerCountWeight_cost R.solution, steinerCountWeight_cost S] at hh
  have hn : 1 ≤ F.left.cherryCount + F.right.cherryCount := by
    change 0 < F.left.cherryCount + F.right.cherryCount at hhas
    omega
  have hnR : (1 : ℝ) ≤ (F.left.cherryCount : ℝ) + (F.right.cherryCount : ℝ) := by exact_mod_cast hn
  have hN : (steinerEdges R.solution).card + 1 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges R.solution).card : ℝ) + 1 ≤ (steinerEdges S).card by linarith)
  exact Nat.lt_of_succ_le hN

theorem FullyPromoted.small_charge_paid (F : Fan S parent v) (R : FullyPromoted F)
    (hred : Reduced S) (hsmall : F.Small) :
    F.promotionCharge ≤ smallCoefficient * (nonterminalCost S - nonterminalCost R.solution) := by
  have hl := F.left.small_charge_le hred hsmall.1
  have hr := F.right.small_charge_le hred hsmall.2
  have hn := R.nonterminalCost_bound F
  have hcoef : 0 ≤ smallCoefficient := by norm_num [smallCoefficient, alpha0, chi, e0]
  have hpay := mul_le_mul_of_nonneg_left
    (show F.left.trunkWeight + F.right.trunkWeight ≤ nonterminalCost S - nonterminalCost R.solution by linarith)
      hcoef
  change F.left.longerArm + F.right.longerArm ≤ _
  nlinarith

end Fan

theorem nonterminalCost_le_cost {S : TreeGeometry.TreeSolution I} :
    nonterminalCost S ≤ S.cost := by
  apply Finset.sum_le_sum
  intro e he
  rcases e with ⟨x, y⟩
  simp only [Sym2.map_mk, nonterminalWeight_mk, Instance.weight_mk, nonterminalDistance]
  split_ifs
  · exact le_rfl
  · exact I.distance_nonneg _ _

theorem cherry_permanent_separated {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (C : Cherry S v) (R : Limb S v)
    (hdisj : Disjoint (Limb.cherry C).region R.region) :
    ¬ (terminalGraph S).Reachable C.primary C.secondary ∧
      ¬ (terminalGraph S).Reachable C.primary R.primary ∧
      ¬ (terminalGraph S).Reachable C.secondary R.primary := by
  have hout : (R.primary : V) ∉ (Limb.cherry C).region := by
    intro h
    exact Finset.disjoint_left.mp hdisj h R.primary_mem_region
  have htrunk := terminalGraph_region_closed S v C.center C.attachment_nonterminal
  have harm := terminalGraph_region_closed S C.center C.primary C.center_nonterminal
  refine ⟨harm.not_reachable ?_ C.secondary_outside_primary_arm,
    htrunk.not_reachable (Limb.cherry C).primary_mem_region hout,
    htrunk.not_reachable C.secondary_mem_region hout⟩
  exact (mem_region S C.center C.primary C.primary).mpr (SimpleGraph.Reachable.refl _)

end SteinerUpperBound.Structural.Tree

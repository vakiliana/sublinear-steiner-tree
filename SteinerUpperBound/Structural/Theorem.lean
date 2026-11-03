module

public import SteinerUpperBound.Structural.Process

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SteinerUpperBound.Structural.Tree

variable {V : Type*} [Fintype V] {I : Instance V} {g : Grid}

theorem Ledger.Valid.weaken_ceiling {S : TreeGeometry.TreeSolution I}
    {ceiling ceiling' : ℝ} {L : Ledger I g} (h : L.Valid S ceiling) (hc : ceiling ≤ ceiling') :
    L.Valid S ceiling' :=
  ⟨h.star_terminals, h.star_sound, h.star_expands, h.star_rank, h.regular_eligible,
    h.regular_groups, h.small_nonneg, h.small_paid.trans hc⟩

theorem Ledger.Valid.smallCharge_le_ceiling {S : TreeGeometry.TreeSolution I}
    {ceiling : ℝ} {L : Ledger I g} (h : L.Valid S ceiling) : L.smallCharge ≤ ceiling := by
  have hn := mul_nonneg (show 0 ≤ smallCoefficient by norm_num [smallCoefficient, alpha0, chi, e0])
    (nonterminalCost_nonneg S)
  linarith [h.small_paid]

theorem amortized_le_cost (S : TreeGeometry.TreeSolution I) :
    amortized S ≤ (2 - 89 * e0 / 90) * S.cost := by
  have hc : 0 ≤ S.cost := I.optimum_nonneg.trans S.optimum_le_cost
  have he : 0 ≤ e0 := by norm_num [e0]
  have hk : 0 ≤ smallCoefficient := by norm_num [smallCoefficient, alpha0, chi, e0]
  have hnn := mul_le_mul_of_nonneg_left (nonterminalCost_le_cost (S := S)) (mul_nonneg he hk)
  have hcoef := mul_le_mul_of_nonneg_left smallCoefficient_lt.le he
  have hcost := mul_le_mul_of_nonneg_right hcoef hc
  unfold amortized
  calc
    _ ≤ chi * S.cost + e0 * smallCoefficient * S.cost := add_le_add (potential_le_cost S) hnn
    _ ≤ chi * S.cost + (e0 * (1 / 90)) * S.cost := add_le_add le_rfl hcost
    _ = _ := by unfold chi; ring

/-- This witness is constructed from an attained metric optimum, actual local surgeries,
and well-founded elimination. Its ledger is not an assumption of the structural theorem. -/
theorem optimal_elimination (I : Instance V) (g : Grid)
    (hT : I.terminals.Nonempty) (hg : g.Covers I) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L : Ledger I g),
      Q.IsClean ∧ (steinerEdges Q).card = 0 ∧
      L.Valid Q (smallCoefficient * I.optimum) ∧
      Ledger.budget Q L ≤ (2 - 89 * e0 / 90) * I.optimum := by
  obtain ⟨S, hcost, _⟩ := TreeGeometry.clean_optimum_tree_attained I hT
  obtain ⟨Q, L, _, hclean, _, _, hzero, hvalid, hbudget⟩ := eliminate_from_tree S hT hg
  have hceiling : smallCoefficient * nonterminalCost S ≤ smallCoefficient * I.optimum := by
    have hh := mul_le_mul_of_nonneg_left (nonterminalCost_le_cost (S := S))
      (show 0 ≤ smallCoefficient by norm_num [smallCoefficient, alpha0, chi, e0])
    simpa only [hcost] using hh
  have hinit : amortized S ≤ (2 - 89 * e0 / 90) * I.optimum := by
    simpa only [hcost] using amortized_le_cost S
  exact ⟨Q, L, hclean, hzero, hvalid.weaken_ceiling hceiling, hbudget.trans hinit⟩

theorem optimal_elimination_charges (I : Instance V) (g : Grid)
    (hT : I.terminals.Nonempty) (hg : g.Covers I) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L : Ledger I g),
      Q.IsClean ∧ (steinerEdges Q).card = 0 ∧
      L.Valid Q (smallCoefficient * I.optimum) ∧
      L.starAmount ≤ gamma I g ∧ L.regularAmount ≤ lambda I g ∧
      L.smallCharge ≤ smallCoefficient * I.optimum ∧
      (0 < I.optimum → L.smallCharge < I.optimum / 90) ∧
      Ledger.budget Q L ≤ (2 - 89 * e0 / 90) * I.optimum := by
  obtain ⟨Q, L, hc, hz, hv, hb⟩ := optimal_elimination I g hT hg
  refine ⟨Q, L, hc, hz, hv, hv.starAmount_le, hv.regularAmount_le,
    hv.smallCharge_le_ceiling, ?_, hb⟩
  intro hpos
  have hlt := mul_lt_mul_of_pos_right smallCoefficient_lt hpos
  have hle := hv.smallCharge_le_ceiling
  calc
    L.smallCharge ≤ smallCoefficient * I.optimum := hle
    _ < (1 / 90 : ℝ) * I.optimum := hlt
    _ = I.optimum / 90 := by ring

theorem structural_bound (I : Instance V) (g : Grid)
    (hg : 2 ≤ I.terminals.card → g.Covers I) :
    I.mst ≤ (2 - 89 * e0 / 90) * I.optimum +
      (1001 / 4000 : ℝ) * gamma I g + e0 * lambda I g := by
  by_cases hk : I.terminals.card ≤ 1
  · rw [I.mst_eq_zero hk, I.optimum_eq_zero hk]
    simp only [mul_zero, zero_add]
    exact add_nonneg
      (mul_nonneg (by norm_num) (gamma_nonneg I g))
      (mul_nonneg (by norm_num [e0]) (lambda_nonneg I g))
  · have hk2 : 2 ≤ I.terminals.card := by omega
    have hT : I.terminals.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Q, L, _, hz, hv, hb⟩ := optimal_elimination I g hT (hg hk2)
    have hm := hv.terminal_bound hz
    change I.mst ≤ (2 - 89 * e0 / 90) * I.optimum +
      starCoefficient * gamma I g + e0 * lambda I g
    exact hm.trans (add_le_add (add_le_add hb le_rfl) le_rfl)

theorem structural_bound_of_covers (I : Instance V) (g : Grid) (hg : g.Covers I) :
    I.mst ≤ (2 - 89 * e0 / 90) * I.optimum +
      (1001 / 4000 : ℝ) * gamma I g + e0 * lambda I g :=
  structural_bound I g (fun _ => hg)

theorem negative_evidence (I : Instance V) (g : Grid)
    (hg : 2 ≤ I.terminals.card → g.Covers I)
    (hGamma : gamma I g ≤ e0 * I.mst / 100) (hLambda : lambda I g ≤ I.mst / 10) :
    I.mst ≤ (2 - e0 / 2) * I.optimum := by
  have hstruct := structural_bound I g hg
  have hdouble := TreeGeometry.mst_le_twice_optimum I
  have hG := mul_le_mul_of_nonneg_left hGamma (show (0 : ℝ) ≤ 1001 / 4000 by norm_num)
  have hL := mul_le_mul_of_nonneg_left hLambda (show 0 ≤ e0 by norm_num [e0])
  norm_num [e0] at hstruct hG hL ⊢
  nlinarith [I.optimum_nonneg]

theorem negative_evidence_of_covers (I : Instance V) (g : Grid) (hg : g.Covers I)
    (hGamma : gamma I g ≤ e0 * I.mst / 100) (hLambda : lambda I g ≤ I.mst / 10) :
    I.mst ≤ (2 - e0 / 2) * I.optimum :=
  negative_evidence I g (fun _ => hg) hGamma hLambda

end SteinerUpperBound.Structural

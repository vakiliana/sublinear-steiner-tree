module

public import SteinerUpperBound.Structural.LedgerUpdates

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SteinerUpperBound.Structural.Tree

variable {V : Type*} [Fintype V] {I : Instance V} {g : Grid}

namespace Tree

theorem Limb.trunkWeight_nonneg {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (L : Limb S v) : 0 ≤ L.trunkWeight := by
  cases L with
  | direct x hv hx h => exact le_rfl
  | cherry C => exact I.distance_nonneg _ _

theorem Limb.longerArm_nonneg {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (L : Limb S v) : 0 ≤ L.longerArm := by
  cases L with
  | direct x hv hx h => exact le_rfl
  | cherry C => exact I.distance_nonneg _ _

theorem Fan.promotionCharge_nonneg {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}
    (F : Fan S parent v) : 0 ≤ F.promotionCharge :=
  add_nonneg F.left.longerArm_nonneg F.right.longerArm_nonneg

theorem Fan.FullyPromoted.nonterminalCost_le {S : TreeGeometry.TreeSolution I}
    {parent v : ↥S.vertices} (F : Fan S parent v) (R : Fan.FullyPromoted F) :
    nonterminalCost R.solution ≤ nonterminalCost S := by
  linarith [R.nonterminalCost_bound F, F.left.trunkWeight_nonneg, F.right.trunkWeight_nonneg]

theorem Fan.RegularDatum.fresh_component {S : TreeGeometry.TreeSolution I}
    {parent v : ↥S.vertices} {F : Fan S parent v} {a : ℝ} {D : Finset V}
    (hD : Fan.RegularDatum F a D) {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling)
    (j : Fin (g.intervals + 1)) : (j, D) ∉ L.regular :=
  fun hused => hD.not_two_groups (hL.regular_groups (j, D) hused)

namespace RootedFringe

variable {S : TreeGeometry.TreeSolution I} {parent v : ↥S.vertices}

theorem small_recorded_exists (F : RootedFringe S parent v) (hred : Reduced S)
    (hsmall : F.fan.Small) {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling) :
    ∃ Q : TreeGeometry.TreeSolution I,
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      (L.addSmall F.fan.promotionCharge).Valid Q ceiling ∧
      Ledger.budget Q (L.addSmall F.fan.promotionCharge) ≤ Ledger.budget S L := by
  obtain ⟨R⟩ := F.fan.fullyPromoted_exists
  obtain ⟨Q, hQsub, hclean, hQperm, hQpot, hQnn, hQcount, hQred⟩ :=
    exists_reduced R.solution ⟨F.root, F.root_terminal⟩
  have hp := R.permanent.trans hQperm
  have hn := hQnn.trans (R.nonterminalCost_le F.fan)
  have hcoef : 0 ≤ smallCoefficient := by norm_num [smallCoefficient, alpha0, chi, e0]
  have hpaidR := R.small_charge_paid F.fan hred hsmall
  have hpaid : F.fan.promotionCharge ≤ smallCoefficient * (nonterminalCost S - nonterminalCost Q) :=
    hpaidR.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hQnn _) hcoef)
  have hpotR := R.potential_bound F.fan
  have hpot : potential Q ≤ potential S + e0 * F.fan.promotionCharge := by
    have he : 2 - chi = e0 := by unfold chi; ring
    rw [he] at hpotR
    exact hQpot.trans hpotR
  exact ⟨Q, hQsub.trans R.vertices_subset, hclean, hQred, hp, hn,
    lt_of_le_of_lt hQcount (R.steinerEdges_lt F.fan F.has_cherry),
    hL.addSmall hp hn _ F.fan.promotionCharge_nonneg hpaid,
    Ledger.budget_addSmall L _ (amortized_small _ hpot hpaid)⟩

theorem regular_recorded_exists (F : RootedFringe S parent v)
    (hc : S.IsClean) (hstar : ¬ Nonempty (ShortStar S)) (hred : Reduced S)
    (hnot : ¬ F.fan.Small) (hparent : delta0 * F.fan.pair.totalLength ≤ I.distance parent v)
    (hg : g.Covers I) {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling) :
    ∃ (i : Fin (g.intervals + 1)) (D : Finset V) (Q : TreeGeometry.TreeSolution I),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      (L.addRegular i D).Valid Q ceiling ∧
      Ledger.budget Q (L.addRegular i D) ≤ Ledger.budget S L := by
  classical
  obtain ⟨i, hlo, hhi⟩ := F.grid_scale hred hparent g hg
  obtain ⟨D, hD⟩ := F.fan.regular_datum hred hnot hparent (g.scale i) hlo hhi
  have hfresh := hD.fresh_component hL i
  obtain ⟨R⟩ := F.fan.fullyPromoted_exists
  have hgroups := Fan.RegularDatum.promoted_two_groups F hc hstar R hD
  obtain ⟨Q, hQsub, hclean, hQperm, hQpot, hQnn, hQcount, hQred⟩ :=
    exists_reduced R.solution ⟨F.root, F.root_terminal⟩
  have hp := R.permanent.trans hQperm
  have hn := hQnn.trans (R.nonterminalCost_le F.fan)
  have hpotR := R.potential_bound F.fan
  have hpot : potential Q ≤ potential S + e0 * g.scale i := by
    have he : 2 - chi = e0 := by unfold chi; ring
    rw [he] at hpotR
    have hcharge := mul_le_mul_of_nonneg_left hD.2.2.2.1.le
      (show 0 ≤ e0 by norm_num [e0])
    linarith
  exact ⟨i, D, Q, hQsub.trans R.vertices_subset, hclean, hQred, hp, hn,
    lt_of_le_of_lt hQcount (R.steinerEdges_lt F.fan F.has_cherry),
    hL.addRegular hp hn i D hD.1 hD.2.2.1 (hgroups.mono hQperm),
    Ledger.budget_addRegular L i D hfresh (amortized_price _ hpot hn)⟩

theorem recorded_exists (F : RootedFringe S parent v)
    (hc : S.IsClean) (hstar : ¬ Nonempty (ShortStar S)) (hred : Reduced S)
    (he : F.Eligible) (hg : g.Covers I)
    {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L' : Ledger I g),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      L'.Valid Q ceiling ∧ Ledger.budget Q L' ≤ Ledger.budget S L := by
  classical
  by_cases hs : F.fan.Small
  · obtain ⟨Q, hQ⟩ := F.small_recorded_exists hred hs hL
    exact ⟨Q, L.addSmall F.fan.promotionCharge, hQ⟩
  · have hp : delta0 * F.fan.pair.totalLength ≤ I.distance parent v := he.resolve_left hs
    obtain ⟨i, D, Q, hQ⟩ := F.regular_recorded_exists hc hstar hred hs hp hg hL
    exact ⟨Q, L.addRegular i D, hQ⟩

end RootedFringe

end Tree

end SteinerUpperBound.Structural

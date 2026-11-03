module

public import SteinerUpperBound.Structural.StarRecording
public import SteinerUpperBound.Structural.PromotionRecording

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SteinerUpperBound.Structural.Tree

variable {V : Type*} [Fintype V] {I : Instance V} {g : Grid}

theorem advance_exists (S : TreeGeometry.TreeSolution I) (hc : S.IsClean) (hred : Reduced S)
    (hT : I.terminals.Nonempty) (hpos : 0 < (steinerEdges S).card) (hg : g.Covers I)
    {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L' : Ledger I g),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      L'.Valid Q ceiling ∧ Ledger.budget Q L' ≤ Ledger.budget S L := by
  classical
  by_cases hstar : Nonempty (ShortStar S)
  · obtain ⟨A⟩ := hstar
    obtain ⟨i, Q, hQ⟩ := A.recorded_exists hred hg hL
    exact ⟨Q, L.addStar i A.center A.portSet, hQ⟩
  · obtain ⟨parent, v, F, he⟩ := (event_available S hc hred hT hpos).resolve_left hstar
    exact F.recorded_exists hc hstar hred he hg hL

/-- Every recursive call deletes a nonterminal edge. All histories are updated by the
actual star reconnections or fan promotions, rather than supplied as a charging hypothesis. -/
theorem eliminate (S : TreeGeometry.TreeSolution I) (hc : S.IsClean) (hred : Reduced S)
    (hT : I.terminals.Nonempty) (hg : g.Covers I)
    {ceiling : ℝ} {L : Ledger I g} (hL : L.Valid S ceiling) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L' : Ledger I g),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card = 0 ∧ L'.Valid Q ceiling ∧
      Ledger.budget Q L' ≤ Ledger.budget S L := by
  classical
  have hmain : ∀ n : ℕ, ∀ (R : TreeGeometry.TreeSolution I) (H : Ledger I g),
      (steinerEdges R).card = n → R.IsClean → Reduced R → H.Valid R ceiling →
      ∃ (Q : TreeGeometry.TreeSolution I) (L' : Ledger I g),
        Q.vertices ⊆ R.vertices ∧ Q.IsClean ∧ Reduced Q ∧
        terminalGraph R ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost R ∧
        (steinerEdges Q).card = 0 ∧ L'.Valid Q ceiling ∧
        Ledger.budget Q L' ≤ Ledger.budget R H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R H hn hclean hreduce hvalid
      by_cases hz : (steinerEdges R).card = 0
      · exact ⟨R, H, Finset.Subset.refl _, hclean, hreduce, le_rfl, le_rfl,
          hz, hvalid, le_rfl⟩
      · obtain ⟨A, HA, hsub, hAc, hAr, hperm, hnn, hcount, hAv, hbudget⟩ :=
          advance_exists R hclean hreduce hT (Nat.pos_of_ne_zero hz) hg hvalid
        have hlt : (steinerEdges A).card < n := by omega
        obtain ⟨Q, HQ, hQsub, hQc, hQr, hQperm, hQnn, hzero, hQv, hQbudget⟩ :=
          ih (steinerEdges A).card hlt A HA rfl hAc hAr hAv
        exact ⟨Q, HQ, hQsub.trans hsub, hQc, hQr, hperm.trans hQperm, hQnn.trans hnn,
          hzero, hQv, hQbudget.trans hbudget⟩
  exact hmain (steinerEdges S).card S L rfl hc hred hL

theorem eliminate_from_tree (S : TreeGeometry.TreeSolution I)
    (hT : I.terminals.Nonempty) (hg : g.Covers I) :
    ∃ (Q : TreeGeometry.TreeSolution I) (L : Ledger I g),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card = 0 ∧
      L.Valid Q (smallCoefficient * nonterminalCost S) ∧
      Ledger.budget Q L ≤ amortized S := by
  obtain ⟨R, hsub, hc, hp, hpot, hn, _, hred⟩ := exists_reduced S hT
  have hL : (Ledger.empty I g).Valid R (smallCoefficient * nonterminalCost S) := by
    have hvalid := (Ledger.empty_valid S g).mono hp hn
    exact hvalid
  obtain ⟨Q, L, hQsub, hQc, _, hQp, hQnn, hz, hQv, hQb⟩ :=
    eliminate R hc hred hT hg hL
  have hempty : Ledger.budget R (Ledger.empty I g) = amortized R := by
    simp [Ledger.budget, Ledger.starAmount, Ledger.regularAmount, Ledger.empty]
  exact ⟨Q, L, hQsub.trans hsub, hQc, hp.trans hQp, hQnn.trans hn, hz, hQv,
    hQb.trans (hempty.le.trans (amortized_mono hpot hn))⟩

end SteinerUpperBound.Structural

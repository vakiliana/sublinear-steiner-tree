module

public import SteinerUpperBound.Structural.Ledger

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SavingSoundness
open SteinerUpperBound.Structural.Tree

variable {V : Type*} [Fintype V] {I : Instance V} {g : Grid}

theorem gain_portList_cons (G : SimpleGraph V) (e : V × Finset V) (l : List (V × Finset V)) :
    GraphRank.gain G (portGraphList (e :: l)) =
      GraphRank.gain G (portGraphList l) +
        GraphRank.gain (G ⊔ portGraphList l) (Network.completeOn e.2) := by
  have he : G ⊔ (Network.completeOn e.2 ⊔ portGraphList l) =
      (G ⊔ portGraphList l) ⊔ Network.completeOn e.2 := by ac_rfl
  unfold GraphRank.gain
  rw [portGraphList_cons, he]
  ring

namespace Ledger

noncomputable abbrev addStar (L : Ledger I g) (i : Fin (g.intervals + 1))
    (center : V) (ports : Finset V) : Ledger I g :=
  { L with stars := Function.update L.stars i ((center, ports) :: L.stars i) }

noncomputable abbrev addRegular (L : Ledger I g) (i : Fin (g.intervals + 1))
    (C : Finset V) : Ledger I g :=
  { L with regular := insert (i, C) L.regular }

noncomputable abbrev addSmall (L : Ledger I g) (charge : ℝ) : Ledger I g :=
  { L with smallCharge := L.smallCharge + charge }

@[simp] theorem stars_addStar_same (L : Ledger I g) (i : Fin (g.intervals + 1))
    (center : V) (ports : Finset V) :
    (L.addStar i center ports).stars i = (center, ports) :: L.stars i :=
  Function.update_self _ _ _

theorem stars_addStar_ne (L : Ledger I g) (i : Fin (g.intervals + 1))
    (center : V) (ports : Finset V) (j : Fin (g.intervals + 1)) (h : j ≠ i) :
    (L.addStar i center ports).stars j = L.stars j :=
  Function.update_of_ne h _ _

theorem starAmount_addStar (L : Ledger I g) (i : Fin (g.intervals + 1))
    (center : V) (ports : Finset V) :
    (L.addStar i center ports).starAmount = L.starAmount + g.scale i := by
  classical
  unfold starAmount
  calc
    _ = ∑ j, (g.scale j * ((L.stars j).length : ℝ) +
        if j = i then g.scale i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : j = i
      · subst j
        simp only [Ledger.addStar, Function.update_self, List.length_cons, Nat.cast_add, Nat.cast_one, ↓reduceIte]
        ring
      · simp only [Ledger.addStar, Function.update_of_ne h, h, ↓reduceIte, add_zero]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem regularAmount_addRegular (L : Ledger I g) (i : Fin (g.intervals + 1)) (C : Finset V)
    (hfresh : (i, C) ∉ L.regular) :
    (L.addRegular i C).regularAmount = L.regularAmount + g.scale i := by
  unfold addRegular regularAmount
  rw [Finset.sum_insert hfresh]
  ring

theorem Valid.addSmall {S Q : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) (hp : terminalGraph S ≤ terminalGraph Q)
    (hn : nonterminalCost Q ≤ nonterminalCost S)
    (charge : ℝ) (hc : 0 ≤ charge)
    (hpay : charge ≤ smallCoefficient * (nonterminalCost S - nonterminalCost Q)) :
    Valid Q ceiling (L.addSmall charge) := by
  have hQ := h.mono hp hn
  refine ⟨hQ.star_terminals, hQ.star_sound, hQ.star_expands, hQ.star_rank,
    hQ.regular_eligible, hQ.regular_groups, add_nonneg h.small_nonneg hc, ?_⟩
  change (L.smallCharge + charge) + smallCoefficient * nonterminalCost Q ≤ ceiling
  linarith [h.small_paid]

theorem Valid.addRegular {S Q : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) (hp : terminalGraph S ≤ terminalGraph Q)
    (hn : nonterminalCost Q ≤ nonterminalCost S)
    (i : Fin (g.intervals + 1)) (C : Finset V)
    (hC : C ∈ components I (g.scale i)) (hscore : sigma0 * g.scale i ≤ localAdvantage I C)
    (hgroups : TwoGroups (terminalGraph Q) C) :
    Valid Q ceiling (L.addRegular i C) := by
  have hQ := h.mono hp hn
  refine ⟨hQ.star_terminals, hQ.star_sound, hQ.star_expands, hQ.star_rank, ?_, ?_,
    hQ.small_nonneg, hQ.small_paid⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact ⟨hC, hscore⟩
    · exact hQ.regular_eligible e he
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hgroups
    · exact hQ.regular_groups e he

theorem Valid.addStar {S Q : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) (hp : terminalGraph S ≤ terminalGraph Q)
    (hn : nonterminalCost Q ≤ nonterminalCost S)
    (i : Fin (g.intervals + 1)) (center : V) (ports : Finset V)
    (hT : ports ⊆ I.terminals)
    (hsound : center ∈ eligible I (g.scale i) ∧
      ports.image (component I (g.scale i)) ⊆ components I (g.scale i) ∩ row I (g.scale i) center)
    (hconnect : Network.Feasible ports (terminalGraph Q))
    (hgain : 2 ≤ GraphRank.gain (threshold I (g.scale i) ⊔ portGraphList (L.stars i))
      (Network.completeOn ports)) :
    Valid Q ceiling (L.addStar i center ports) := by
  classical
  have hQ := h.mono hp hn
  refine ⟨?_, ?_, ?_, ?_, hQ.regular_eligible, hQ.regular_groups, hQ.small_nonneg, hQ.small_paid⟩
  · intro j e he
    by_cases hj : j = i
    · subst j
      simp only [Ledger.addStar, Function.update_self] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact hT
      · exact hQ.star_terminals i e he
    · have he' : e ∈ L.stars j := by simpa only [Ledger.addStar, Function.update_of_ne hj] using he
      exact hQ.star_terminals j e he'
  · intro j e he
    by_cases hj : j = i
    · subst j
      simp only [Ledger.addStar, Function.update_self] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact hsound
      · exact hQ.star_sound i e he
    · have he' : e ∈ L.stars j := by simpa only [Ledger.addStar, Function.update_of_ne hj] using he
      exact hQ.star_sound j e he'
  · intro j x y hxy
    by_cases hj : j = i
    · subst j
      simp only [Ledger.addStar, Function.update_self, portGraphList_cons] at hxy
      rcases hxy with hxy | hxy
      · obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj _ _ _).mp hxy
        exact hconnect x hx y hy
      · exact hQ.star_expands i x y hxy
    · have hxy' : (portGraphList (L.stars j)).Adj x y := by
        simpa only [Ledger.addStar, Function.update_of_ne hj] using hxy
      exact hQ.star_expands j x y hxy'
  · intro j
    by_cases hj : j = i
    · subst j
      simp only [Ledger.addStar, Function.update_self]
      rw [gain_portList_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith [h.star_rank i]
    · simpa only [Ledger.addStar, Function.update_of_ne hj] using hQ.star_rank j

theorem budget_addStar {S Q : TreeGeometry.TreeSolution I} (L : Ledger I g)
    (i : Fin (g.intervals + 1)) (center : V) (ports : Finset V)
    (hprice : amortized Q ≤ amortized S + starCoefficient * g.scale i) :
    budget Q (L.addStar i center ports) ≤ budget S L := by
  unfold budget
  rw [starAmount_addStar]
  change amortized Q - starCoefficient * (L.starAmount + g.scale i) - e0 * L.regularAmount ≤ _
  nlinarith

theorem budget_addRegular {S Q : TreeGeometry.TreeSolution I} (L : Ledger I g)
    (i : Fin (g.intervals + 1)) (C : Finset V) (hfresh : (i, C) ∉ L.regular)
    (hprice : amortized Q ≤ amortized S + e0 * g.scale i) :
    budget Q (L.addRegular i C) ≤ budget S L := by
  unfold budget
  rw [regularAmount_addRegular L i C hfresh]
  change amortized Q - starCoefficient * L.starAmount - e0 * (L.regularAmount + g.scale i) ≤ _
  nlinarith

theorem budget_addSmall {S Q : TreeGeometry.TreeSolution I} (L : Ledger I g) (charge : ℝ)
    (hprice : amortized Q ≤ amortized S) : budget Q (L.addSmall charge) ≤ budget S L := by
  unfold budget
  change amortized Q - starCoefficient * L.starAmount - e0 * L.regularAmount ≤ _
  linarith

end Ledger

end SteinerUpperBound.Structural

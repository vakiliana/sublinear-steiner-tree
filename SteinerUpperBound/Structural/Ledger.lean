module

public import SteinerUpperBound.Structural.StarRankBridge
public import SteinerUpperBound.Structural.RegularData
public import SteinerUpperBound.Structural.GridScales

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SavingSoundness
open Tree

variable {V : Type*} [Fintype V] {I : Instance V}

noncomputable abbrev starCoefficient : ℝ := 1001 / 4000

noncomputable def amortized (S : TreeGeometry.TreeSolution I) : ℝ :=
  potential S + e0 * smallCoefficient * nonterminalCost S

theorem nonterminalCost_nonneg (S : TreeGeometry.TreeSolution I) : 0 ≤ nonterminalCost S :=
  Finset.sum_nonneg (fun e he => nonterminalWeight_nonneg I _)

theorem amortized_mono {S Q : TreeGeometry.TreeSolution I}
    (hp : potential Q ≤ potential S) (hn : nonterminalCost Q ≤ nonterminalCost S) :
    amortized Q ≤ amortized S := by
  have hcoef : 0 ≤ e0 * smallCoefficient := by
    norm_num [e0, smallCoefficient, alpha0, chi]
  have hh := mul_le_mul_of_nonneg_left hn hcoef
  unfold amortized
  linarith

theorem amortized_price {S Q : TreeGeometry.TreeSolution I} (price : ℝ)
    (hp : potential Q ≤ potential S + price) (hn : nonterminalCost Q ≤ nonterminalCost S) :
    amortized Q ≤ amortized S + price := by
  have hcoef : 0 ≤ e0 * smallCoefficient := by
    norm_num [e0, smallCoefficient, alpha0, chi]
  have hh := mul_le_mul_of_nonneg_left hn hcoef
  unfold amortized
  linarith

theorem amortized_small {S Q : TreeGeometry.TreeSolution I} (charge : ℝ)
    (hp : potential Q ≤ potential S + e0 * charge)
    (hpaid : charge ≤ smallCoefficient * (nonterminalCost S - nonterminalCost Q)) :
    amortized Q ≤ amortized S := by
  have hh := mul_le_mul_of_nonneg_left hpaid (show 0 ≤ e0 by norm_num [e0])
  unfold amortized
  nlinarith

structure Ledger (I : Instance V) (g : Grid) where
  stars : Fin (g.intervals + 1) → List (V × Finset V)
  regular : Finset (Fin (g.intervals + 1) × Finset V)
  smallCharge : ℝ

namespace Ledger

variable {g : Grid}

noncomputable def empty (I : Instance V) (g : Grid) : Ledger I g :=
  ⟨fun _ => [], ∅, 0⟩

noncomputable def starAmount (L : Ledger I g) : ℝ :=
  ∑ i, g.scale i * ((L.stars i).length : ℝ)

noncomputable def regularAmount (L : Ledger I g) : ℝ :=
  ∑ e ∈ L.regular, g.scale e.1

noncomputable def budget (S : TreeGeometry.TreeSolution I) (L : Ledger I g) : ℝ :=
  amortized S - starCoefficient * L.starAmount - e0 * L.regularAmount

structure Valid (S : TreeGeometry.TreeSolution I) (ceiling : ℝ) (L : Ledger I g) : Prop where
  star_terminals : ∀ i e, e ∈ L.stars i → e.2 ⊆ I.terminals
  star_sound : ∀ i e, e ∈ L.stars i →
    e.1 ∈ eligible I (g.scale i) ∧
      e.2.image (component I (g.scale i)) ⊆ components I (g.scale i) ∩ row I (g.scale i) e.1
  star_expands : ∀ i x y, (portGraphList (L.stars i)).Adj x y → (terminalGraph S).Reachable x y
  star_rank : ∀ i, 2 * ((L.stars i).length : ℝ) ≤
    GraphRank.gain (threshold I (g.scale i)) (portGraphList (L.stars i))
  regular_eligible : ∀ e ∈ L.regular,
    e.2 ∈ components I (g.scale e.1) ∧ sigma0 * g.scale e.1 ≤ localAdvantage I e.2
  regular_groups : ∀ e ∈ L.regular, TwoGroups (terminalGraph S) e.2
  small_nonneg : 0 ≤ L.smallCharge
  small_paid : L.smallCharge + smallCoefficient * nonterminalCost S ≤ ceiling

theorem empty_valid (S : TreeGeometry.TreeSolution I) (g : Grid) :
    Valid S (smallCoefficient * nonterminalCost S) (empty I g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, le_rfl, ?_⟩
  · simp [empty]
  · simp [empty]
  · simp [empty, portGraphList]
  · intro i
    simp [empty, portGraphList, GraphRank.gain]
  · simp [empty]
  · simp [empty]
  · simp [empty]

theorem Valid.mono {S Q : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) (hp : terminalGraph S ≤ terminalGraph Q)
    (hn : nonterminalCost Q ≤ nonterminalCost S) : Valid Q ceiling L := by
  refine ⟨h.star_terminals, h.star_sound, ?_, h.star_rank, h.regular_eligible, ?_,
    h.small_nonneg, ?_⟩
  · intro i x y hxy
    exact (h.star_expands i x y hxy).mono hp
  · intro e he
    exact (h.regular_groups e he).mono hp
  · have hc : 0 ≤ smallCoefficient := by norm_num [smallCoefficient, alpha0, chi, e0]
    have hh := mul_le_mul_of_nonneg_left hn hc
    linarith [h.small_paid]

theorem Valid.starAmount_le {S : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) : L.starAmount ≤ gamma I g := by
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left
    (star_events_le_rowSaving I (g.scale i) (L.stars i)
      (h.star_terminals i) (h.star_sound i) (h.star_rank i)) (g.positive i).le

noncomputable def regularBins (I : Instance V) (g : Grid) :
    Finset (Fin (g.intervals + 1) × Finset V) :=
  Finset.univ.biUnion (fun i => ((components I (g.scale i)).filter
    (fun C => sigma0 * g.scale i ≤ localAdvantage I C)).image (fun C => (i, C)))

theorem mem_regularBins (I : Instance V) (g : Grid) (i : Fin (g.intervals + 1)) (C : Finset V) :
    (i, C) ∈ regularBins I g ↔
      C ∈ components I (g.scale i) ∧ sigma0 * g.scale i ≤ localAdvantage I C := by
  classical
  simp only [regularBins, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨j, D, hD, hji, hDC⟩
    subst j
    subst D
    exact hD
  · intro h
    exact ⟨i, C, h, rfl, rfl⟩

theorem regularBins_sum (I : Instance V) (g : Grid) :
    (∑ e ∈ regularBins I g, g.scale e.1) = lambda I g := by
  classical
  unfold regularBins
  have hd : ((Finset.univ : Finset (Fin (g.intervals + 1))) :
      Set (Fin (g.intervals + 1))).PairwiseDisjoint
      (fun i => ((components I (g.scale i)).filter
        (fun C => sigma0 * g.scale i ≤ localAdvantage I C)).image (fun C => (i, C))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro e hiE hjE
    obtain ⟨C, _, hC⟩ := Finset.mem_image.mp hiE
    obtain ⟨D, _, hD⟩ := Finset.mem_image.mp hjE
    exact hij (congrArg Prod.fst (hC.trans hD.symm))
  rw [Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_image]
  · simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · intro C hC D hD he
    exact congrArg Prod.snd he

theorem Valid.regularAmount_le {S : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) : L.regularAmount ≤ lambda I g := by
  classical
  have hsub : L.regular ⊆ regularBins I g := by
    intro e he
    exact (mem_regularBins I g e.1 e.2).mpr (h.regular_eligible e he)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e he hnot => (g.positive e.1).le)).trans_eq (regularBins_sum I g)

theorem Valid.terminal_bound {S : TreeGeometry.TreeSolution I} {ceiling : ℝ} {L : Ledger I g}
    (h : Valid S ceiling L) (hzero : (steinerEdges S).card = 0) :
    I.mst ≤ budget S L + starCoefficient * gamma I g + e0 * lambda I g := by
  have hm := mst_le_potential_of_terminal S hzero
  have hn := nonterminalCost_nonneg S
  have hs := h.starAmount_le
  have hr := h.regularAmount_le
  have hstar : 0 ≤ starCoefficient := by norm_num [starCoefficient]
  have he : 0 ≤ e0 := by norm_num [e0]
  have hc : 0 ≤ e0 * smallCoefficient := by norm_num [e0, smallCoefficient, alpha0, chi]
  have hsm := mul_le_mul_of_nonneg_left hs hstar
  have hrm := mul_le_mul_of_nonneg_left hr he
  have hnn := mul_nonneg hc hn
  unfold budget amortized
  linarith

end Ledger

end SteinerUpperBound.Structural

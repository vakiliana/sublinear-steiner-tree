module

public import SteinerUpperBound.Structural.LedgerUpdates
public import SteinerUpperBound.Structural.StarBounds

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators
open SavingSoundness
open SteinerUpperBound.Structural.Tree

variable {V : Type*} [Fintype V] {I : Instance V} {g : Grid}

namespace Tree.ShortStar

variable {S : TreeGeometry.TreeSolution I}

noncomputable def portSet (A : ShortStar S) : Finset V := Finset.univ.image A.port

theorem mem_portSet (A : ShortStar S) (j : Fin 3) : A.port j ∈ A.portSet :=
  Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

theorem portSet_terminals (A : ShortStar S) : A.portSet ⊆ I.terminals := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact A.port_terminal j

theorem portSet_sound (A : ShortStar S) (hred : Reduced S) (a : ℝ)
    (ha : a ≤ p * A.ell) (hscale : p * A.ell < omega * a) :
    A.center ∈ eligible I a ∧
      A.portSet.image (component I a) ⊆ components I a ∩ row I a A.center := by
  refine ⟨A.center_eligible hred a ha hscale, ?_⟩
  intro C hC
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_inter.mpr ⟨component_mem_components I a (A.port_terminal j),
    component_mem_row I a A.center (A.port_terminal j) (A.ports_close hred a hscale j).le⟩

theorem history_gain {ceiling : ℝ} {L : Ledger I g} (A : ShortStar S) (hred : Reduced S)
    (hL : L.Valid S ceiling) (i : Fin (g.intervals + 1)) (ha : g.scale i ≤ p * A.ell) :
    2 ≤ GraphRank.gain (threshold I (g.scale i) ⊔ portGraphList (L.stars i))
      (Network.completeOn A.portSet) := by
  have hsim : ∀ x y, (threshold I (g.scale i) ⊔ portGraphList (L.stars i)).Adj x y →
      (threshold I (g.scale i) ⊔ terminalGraph S).Reachable x y := by
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact hxy.reachable.mono le_sup_left
    · exact (hL.star_expands i x y hxy).mono le_sup_right
  have hsep {j k : Fin 3} (hjk : j ≠ k) :
      ¬ (threshold I (g.scale i) ⊔ portGraphList (L.stars i)).Reachable (A.port j) (A.port k) :=
    fun h => A.ports_augmented_separated hred (g.scale i) ha hjk
      (reachable_of_adj_reachable hsim h)
  exact gain_ge_two _ A.portSet (A.mem_portSet 0) (A.mem_portSet 1) (A.mem_portSet 2)
    (hsep (by decide)) (hsep (by decide)) (hsep (by decide))

theorem recorded_exists {ceiling : ℝ} {L : Ledger I g} (A : ShortStar S)
    (hred : Reduced S) (hg : g.Covers I) (hL : L.Valid S ceiling) :
    ∃ (i : Fin (g.intervals + 1)) (Q : TreeGeometry.TreeSolution I),
      Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧ Reduced Q ∧
      terminalGraph S ≤ terminalGraph Q ∧ nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      (L.addStar i A.center A.portSet).Valid Q ceiling ∧
      Ledger.budget Q (L.addStar i A.center A.portSet) ≤ Ledger.budget S L := by
  classical
  obtain ⟨i, hi, hi'⟩ := A.grid_scale hred g hg
  obtain ⟨R, hRsub, _, hRperm, hports, hRnn, hRcount, hRpot⟩ := A.operated_exists hred
  obtain ⟨Q, hQsub, hclean, hQperm, hQpot, hQnn, hQcount, hQred⟩ :=
    exists_reduced R ⟨A.port 0, A.port_terminal 0⟩
  have hp := hRperm.trans hQperm
  have hn := hQnn.trans hRnn
  have hconnect : Network.Feasible A.portSet (terminalGraph Q) := by
    intro x hx y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact (hports j k).mono hQperm
  have hvalid := hL.addStar hp hn i A.center A.portSet A.portSet_terminals
    (A.portSet_sound hred _ hi hi') hconnect (A.history_gain hred hL i hi)
  have hcoef : 0 ≤ (21 / 10 : ℝ) - chi := by norm_num [chi, e0]
  have hcharge := mul_le_mul_of_nonneg_left (A.charge_le_scale hred _ hi') hcoef
  have hprice : potential Q ≤ potential S + starCoefficient * g.scale i := by
    norm_num [chi, e0, starCoefficient] at hcharge hRpot ⊢
    linarith
  have hb := Ledger.budget_addStar L i A.center A.portSet
    (amortized_price _ hprice hn)
  exact ⟨i, Q, hQsub.trans hRsub, hclean, hQred, hp, hn,
    lt_of_le_of_lt hQcount hRcount, hvalid, hb⟩

end Tree.ShortStar

end SteinerUpperBound.Structural

module

public import SteinerUpperBound.BandStatistic
public import SteinerUpperBound.StructuralSemantics
public import SteinerUpperBound.NetworkLifting
public import SteinerUpperBound.Covers.Geometry.Structural

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandCompleteness

open SteinerLowerBound MeasureTheory
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

noncomputable def projected (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (Y : Finset V) : Finset V :=
  Y.image (project I I.terminals N ρ hc)

theorem projected_card_le (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (Y : Finset V) :
    (projected I N ρ hc Y).card ≤ Y.card := Finset.card_image_le

theorem projected_subset_terminals (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals)
    {Y : Finset V} (hY : Y ⊆ I.terminals) :
    projected I N ρ hc Y ⊆ I.terminals := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  exact hNT (project_mem I I.terminals N ρ hc (hY hy))

theorem below_eq_thresholdOn (I : Instance V) (S : Finset V) (t : ℝ) :
    TerminalMST.below I.weight S t = thresholdOn I S t := by
  ext x y
  rw [TerminalMST.below_adj, thresholdOn_adj]
  simp only [Instance.weight_mk]

theorem space_le_of_reachable (G H : SimpleGraph V)
    (h : ∀ x y, G.Adj x y → H.Reachable x y) : GraphRank.space G ≤ GraphRank.space H := by
  apply Submodule.span_le.mpr
  rintro z ⟨x, y, hxy, rfl⟩
  exact GraphRank.reachable_mem H (h x y hxy)

theorem gain_eq_of_reachable_links (G : SimpleGraph V) (Y : Finset V) (f : V → V)
    (hf : ∀ y ∈ Y, G.Reachable y (f y)) :
    GraphRank.gain G (Network.completeOn Y) =
      GraphRank.gain G (Network.completeOn (Y.image f)) := by
  classical
  let A := G ⊔ Network.completeOn Y
  let B := G ⊔ Network.completeOn (Y.image f)
  have hAB : GraphRank.space A ≤ GraphRank.space B := by
    apply space_le_of_reachable
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact hxy.reachable.mono le_sup_left
    · obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj Y x y).mp hxy
      have hmiddle := Network.completeOn_feasible (Y.image f)
        (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        (f y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
      exact ((hf x hx).mono le_sup_left).trans
        ((hmiddle.mono le_sup_right).trans ((hf y hy).symm.mono le_sup_left))
  have hBA : GraphRank.space B ≤ GraphRank.space A := by
    apply space_le_of_reachable
    intro x y hxy
    rcases hxy with hxy | hxy
    · exact hxy.reachable.mono le_sup_left
    · obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj (Y.image f) x y).mp hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      have hmiddle := Network.completeOn_feasible Y u hu v hv
      exact ((hf u hu).symm.mono le_sup_left).trans
        ((hmiddle.mono le_sup_right).trans ((hf v hv).mono le_sup_left))
  have he : GraphRank.space A = GraphRank.space B := le_antisymm hAB hBA
  unfold GraphRank.gain GraphRank.rank
  rw [show GraphRank.space (G ⊔ Network.completeOn Y) =
      GraphRank.space (G ⊔ Network.completeOn (Y.image f)) from he]

theorem gain_zero_of_feasible (G : SimpleGraph V) (Y : Finset V)
    (hY : Network.Feasible Y G) : GraphRank.gain G (Network.completeOn Y) = 0 := by
  have hs : GraphRank.space (Network.completeOn Y) ≤ GraphRank.space G := by
    apply space_le_of_reachable
    intro x y hxy
    obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj Y x y).mp hxy
    exact hY x hx y hy
  unfold GraphRank.gain GraphRank.rank
  rw [GraphRank.space_sup, sup_eq_left.mpr hs, sub_self]

theorem gain_le_three (G : SimpleGraph V) (Y : Finset V) (h4 : Y.card ≤ 4) :
    GraphRank.gain G (Network.completeOn Y) ≤ 3 := by
  have h := GraphRank.gain_le_rank G (Network.completeOn Y)
  rw [GraphRank.rank_completeOn] at h
  have hn : Y.card - 1 ≤ 3 := by omega
  exact h.trans (by exact_mod_cast hn)

theorem gain_zero_of_card_le_one (G : SimpleGraph V) (Y : Finset V) (h1 : Y.card ≤ 1) :
    GraphRank.gain G (Network.completeOn Y) = 0 := by
  have h := GraphRank.gain_le_rank G (Network.completeOn Y)
  rw [GraphRank.rank_completeOn, Nat.sub_eq_zero_of_le h1, Nat.cast_zero] at h
  exact le_antisymm h (GraphRank.gain_nonneg _ _)

noncomputable def globalGain (I : Instance V) (Y : Finset V) (t : ℝ) : ℝ :=
  GraphRank.gain (Structural.threshold I t) (Network.completeOn Y)

theorem globalGain_integrable (I : Instance V) (Y : Finset V) (lo hi : ℝ) :
    IntervalIntegrable (globalGain I Y) volume lo hi := by
  change IntervalIntegrable
    (fun t => GraphRank.gain (Structural.threshold I t) (Network.completeOn Y)) volume lo hi
  simpa only [sup_bot_eq] using
    Structural.gain_intervalIntegrable I ⊥ (Network.completeOn Y) lo hi

theorem projected_gain_eq (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    {Y : Finset V} (hY : Y ⊆ I.terminals) (t : ℝ) (hρt : ρ < t) :
    globalGain I Y t = globalGain I (projected I N ρ hc Y) t := by
  apply gain_eq_of_reachable_links
  intro y hy
  rw [← thresholdOn_terminals_eq]
  exact terminal_attachment I I.terminals N ρ hc hNT hρ t hρt (hY hy)

theorem globalGain_zero_on_component (I : Instance V) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I I.terminals a) (hY : Y ⊆ C)
    {t : ℝ} (hat : a ≤ t) : globalGain I Y t = 0 := by
  apply gain_zero_of_feasible
  intro x hx y hy
  rw [← thresholdOn_terminals_eq]
  exact reachable_mono I (Finset.Subset.refl I.terminals) hat
    (componentOn_pair_reachable I I.terminals a hC (hY hx) (hY hy))

theorem globalGain_zero_above_horizon (I : Instance V)
    {Y : Finset V} (hY : Y ⊆ I.terminals) {t : ℝ} (ht : Structural.horizon I ≤ t) :
    globalGain I Y t = 0 := by
  apply gain_zero_of_feasible
  intro x hx y hy
  by_cases he : x = y
  · rw [he]
  · apply SimpleGraph.Adj.reachable
    exact (Structural.threshold_adj I t x y).mpr
      ⟨he, hY hx, hY hy, (Structural.distance_lt_horizon I (hY hx) (hY hy)).trans_le ht⟩

theorem band_benefit_zero_card_le_one (I : Instance V) (C Y : Finset V)
    (h1 : Y.card ≤ 1) (lo hi : ℝ) : Band.benefit I C Y lo hi = 0 := by
  unfold Band.benefit
  simp_rw [gain_zero_of_card_le_one _ Y h1]
  simp

end SteinerUpperBound.Covers.Geometry.BandCompleteness

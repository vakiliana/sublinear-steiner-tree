module

public import SteinerUpperBound.MSTBand
public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Band

open MeasureTheory
open scoped Classical Interval

variable {V : Type*} [Fintype V]

noncomputable def benefit (I : Instance V) (C Y : Finset V) (lo hi : ℝ) : ℝ :=
  ∫ a in lo..hi, GraphRank.gain (TerminalMST.below I.weight C a) (Network.completeOn Y)

theorem links_terminalOnly (C Y : Finset V) (hY : Y ⊆ C) :
    Network.TerminalOnly C (Network.completeOn Y) := by
  intro x y hxy
  obtain ⟨_, hx, hy⟩ := (Network.completeOn_adj Y x y).mp hxy
  exact ⟨hY hx, hY hy⟩

theorem benefit_eq_finiteMST (I : Instance V) (C Y : Finset V) (hY : Y ⊆ C)
    (lo hi : ℝ) (hlohi : lo ≤ hi) :
    benefit I C Y lo hi =
      TerminalMST.value (TerminalMST.clipped I.weight lo hi) C -
        TerminalMST.value
          (TerminalMST.zeroed (TerminalMST.clipped I.weight lo hi) (Network.completeOn Y)) C :=
  (TerminalMST.clipped_value_difference I.weight C (Network.completeOn Y)
    (links_terminalOnly C Y hY) lo hi hlohi).symm

theorem benefit_integrable (I : Instance V) (C Y : Finset V) (hY : Y ⊆ C)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    IntervalIntegrable
      (fun a => GraphRank.gain (TerminalMST.below I.weight C a) (Network.completeOn Y))
        volume lo hi :=
  TerminalMST.gain_integrable I.weight C (Network.completeOn Y)
    (links_terminalOnly C Y hY) lo hi hlo hlohi

noncomputable def smallSets (C : Finset V) : Finset (Finset V) :=
  C.powerset.filter (fun Y => 2 ≤ Y.card ∧ Y.card ≤ 4)

theorem mem_smallSets (C Y : Finset V) :
    Y ∈ smallSets C ↔ Y ⊆ C ∧ 2 ≤ Y.card ∧ Y.card ≤ 4 := by
  simp only [smallSets, Finset.mem_filter, Finset.mem_powerset]

noncomputable def candidates (I : Instance V) (C : Finset V) (a rho tau : ℝ) : Finset ℝ :=
  insert 0 ((smallSets C).image
    (fun Y => benefit I C Y (tau * a) (a - 2 * rho) - Structural.localCost I Y - 6 * rho))

noncomputable def score (I : Instance V) (C : Finset V) (a rho tau : ℝ) : ℝ :=
  (candidates I C a rho tau).max' (by simp [candidates])

theorem score_nonneg (I : Instance V) (C : Finset V) (a rho tau : ℝ) :
    0 ≤ score I C a rho tau :=
  Finset.le_max' _ _ (by simp [candidates])

theorem score_witness (I : Instance V) (C Y : Finset V) (a rho tau : ℝ)
    (hY : Y ⊆ C) (h2 : 2 ≤ Y.card) (h4 : Y.card ≤ 4) :
    benefit I C Y (tau * a) (a - 2 * rho) - Structural.localCost I Y - 6 * rho ≤
      score I C a rho tau := by
  apply Finset.le_max'
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨Y, (mem_smallSets C Y).mpr ⟨hY, h2, h4⟩, rfl⟩

theorem score_attained_positive (I : Instance V) (C : Finset V) (a rho tau : ℝ)
    (h : 0 < score I C a rho tau) :
    ∃ Y, Y ⊆ C ∧ 2 ≤ Y.card ∧ Y.card ≤ 4 ∧
      score I C a rho tau =
        benefit I C Y (tau * a) (a - 2 * rho) - Structural.localCost I Y - 6 * rho := by
  have hm : score I C a rho tau ∈ candidates I C a rho tau := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hm with hm | hm
  · rw [hm] at h
    exact (lt_irrefl _ h).elim
  · obtain ⟨Y, hY, heq⟩ := Finset.mem_image.mp hm
    obtain ⟨hYC, h2, h4⟩ := (mem_smallSets C Y).mp hY
    exact ⟨Y, hYC, h2, h4, heq.symm⟩

end SteinerUpperBound.Band

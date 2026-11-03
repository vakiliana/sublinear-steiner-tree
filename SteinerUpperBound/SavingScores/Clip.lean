module

public import SteinerUpperBound.SavingScores.Law
public import SteinerUpperBound.SetSystem.Scores
public import SteinerUpperBound.EstimationAlgebra

@[expose] public section

namespace SteinerUpperBound.SavingScores

open SteinerLowerBound
open scoped Classical BigOperators

variable {X A R D : Type*}

/-- The selected-center deduction is `2*s`, not `s`. -/
noncomputable def Z (gminus empirical xi : ℝ) (s : ℕ) : ℝ :=
  max 0 (Estimation.lowerCount gminus empirical xi - 2 * s)

noncomputable def fullSaving [Fintype A] (E : Finset R) (rows : R → Finset A) : ℝ :=
  SetSystem.saving E rows Finset.univ

theorem capped_Z_contract [Fintype X] [Fintype A] [Fintype D] [Nonempty X]
    (part : X → A) (hsurj : Function.Surjective part)
    (allRows E : Finset R) (rows : R → Finset A) (hE : E ⊆ allRows)
    (large covered U : Finset A) (S : Finset R) (s : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ allRows) (hs : S.card ≤ s)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (rows r).card ≤ 2)
    (b : ℕ) (hb : 1 ≤ b) (cap : SetSystem.IncidenceCap allRows rows U b)
    (G : Matching.Graph A D) (hreal : SetSystem.Realizes G (SetSystem.mutualGraph U E cap.lists))
    (gminus empirical xi : ℝ) (hxi₀ : 0 ≤ xi) (hxi₁ : xi ≤ 1)
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - scoreMean part hsurj covered U G| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - (large.card : ℝ) / 2 - (allRows.card : ℝ) / b -
          2 * s - 3 * xi * Nat.card X ≤ Z gminus empirical xi s := by
  have hends : ∀ e, G.left e ∈ U ∧ G.right e ∈ U := by
    intro e
    have hh := hreal.copy_adj e
    exact ⟨hh.1, hh.2.1⟩
  have hbadU : ∀ r ∈ allRows, r ∉ E → (U ∩ rows r).card ≤ 2 := by
    intro r hr hrE
    exact (Finset.card_le_card Finset.inter_subset_right).trans (hineligible r hr hrE)
  have hm := SetSystem.mutualCap_expected_greedy_half allRows E rows hE U b hb cap hbadU
    G hreal (Matching.Rank.uniform (E := D))
  change SetSystem.saving E rows U / 2 - (allRows.card : ℝ) / b ≤ expectedMatching G ∧
    expectedMatching G ≤ SetSystem.saving E rows U at hm
  have hbadS : ∀ r ∈ S, r ∉ E → ((Finset.univ : Finset A) ∩ rows r).card ≤ 2 := by
    intro r hr hrE
    simpa only [Finset.univ_inter] using hineligible r (hS hr) hrE
  have hsave := SetSystem.saving_scores E rows Finset.univ large covered U S hparts
    (Finset.subset_univ _) (Finset.subset_univ _) hdisj hcover hbadS
  change fullSaving E rows ≤ _ ∧ _ ≤ fullSaving E rows at hsave
  have hp := scoreMean_eq part hsurj covered U hdisj G hends
  have hmean := scoreMean_bounds part hsurj covered U G
  have hg : (0 : ℝ) < Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hprod : (Nat.card X : ℝ) * scoreMean part hsurj covered U G =
      (covered.card : ℝ) + expectedMatching G := by
    have hh := (eq_div_iff (ne_of_gt hg)).mp hp
    nlinarith
  have hlower := Estimation.lowerCount_bounds (Nat.card X : ℝ) gminus
    (scoreMean part hsurj covered U G) empirical xi hg.le hxi₀ hxi₁
    hmean.1 hmean.2 hcal hcal₁ he
  have hscard : (S.card : ℝ) ≤ s := by exact_mod_cast hs
  have hcovered₀ : 0 ≤ (covered.card : ℝ) := Nat.cast_nonneg _
  have hPhi₀ : 0 ≤ fullSaving E rows := SetSystem.saving_nonneg _ _ _
  have hupper : Estimation.lowerCount gminus empirical xi - 2 * s ≤ fullSaving E rows := by
    linarith
  refine ⟨le_max_left _ _, max_le hPhi₀ hupper, ?_⟩
  have hz : Estimation.lowerCount gminus empirical xi - 2 * s ≤ Z gminus empirical xi s :=
    le_max_right _ _
  linarith

end SteinerUpperBound.SavingScores

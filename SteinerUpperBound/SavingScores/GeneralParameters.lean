module

public import SteinerUpperBound.SavingScores.GeneralClip
public import SteinerUpperBound.SavingScores.Parameters

@[expose] public section

namespace SteinerUpperBound.SavingScores

open SteinerLowerBound
open scoped Classical BigOperators

variable {X A R D : Type*} [Fintype X] [Fintype A] [Fintype D]

theorem ordered_Z_contractFor [Nonempty X]
    (μ : Law (Matching.Rank D)) (part : X → A) (hsurj : Function.Surjective part)
    (order : List R) (horder : order.Nodup)
    (E : Finset R) (rows : R → Finset A) (hE : E ⊆ order.toFinset)
    (large covered U : Finset A) (S : Finset R) (s : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ order.toFinset) (hs : S.card ≤ s)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (rows r).card ≤ 2)
    (b : ℕ) (hb : 1 ≤ b) (G : Matching.Graph A D)
    (hreal : SetSystem.Realizes G
      (SetSystem.mutualGraph U E (SetSystem.firstIncident order rows b)))
    (gminus empirical xi : ℝ) (hxi₀ : 0 ≤ xi) (hxi₁ : xi ≤ 1)
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - scoreMeanFor μ part hsurj covered U G| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - (large.card : ℝ) / 2 - (order.toFinset.card : ℝ) / b -
          2 * s - 3 * xi * Nat.card X ≤ Z gminus empirical xi s :=
  capped_Z_contractFor μ part hsurj order.toFinset E rows hE large covered U S s
    hparts hdisj hcover hS hs hineligible b hb
    (SetSystem.orderedCap order horder rows U b) G hreal
    gminus empirical xi hxi₀ hxi₁ hcal hcal₁ he

theorem large_branch_contractFor [Nonempty X]
    (μ : Law (Matching.Rank D)) (part : X → A) (hsurj : Function.Surjective part)
    (allRows E : Finset R) (hrows : 0 < allRows.card)
    (rows : R → Finset A) (hE : E ⊆ allRows)
    (large covered U : Finset A) (S : Finset R) (s t : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ allRows) (hs : S.card ≤ s) (hst : s ≤ t)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (rows r).card ≤ 2)
    (eps gminus empirical xi : ℝ) (heps : 0 < eps) (heps₁ : eps ≤ 1)
    (hlarge : ∀ a ∈ large, smallThreshold eps < partSize part a)
    (hbranch : 50 * (t : ℝ) / eps < Nat.card X)
    (hxi₀ : 0 ≤ xi) (hxi : xi ≤ eps / 100)
    (cap : SetSystem.IncidenceCap allRows rows U (incidenceBudget allRows.card eps gminus))
    (G : Matching.Graph A D) (hreal : SetSystem.Realizes G (SetSystem.mutualGraph U E cap.lists))
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - scoreMeanFor μ part hsurj covered U G| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - eps * Nat.card X ≤ Z gminus empirical xi s := by
  have hg : (0 : ℝ) < Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hxi₁ : xi ≤ 1 := by linarith
  have hgminus : 0 < gminus :=
    (mul_pos (by linarith : 0 < 1 - xi) hg).trans_le hcal
  have hb := incidenceBudget_pos allRows.card hrows eps gminus heps hgminus
  have hc := capped_Z_contractFor μ part hsurj allRows E rows hE large covered U S s
    hparts hdisj hcover hS hs hineligible (incidenceBudget allRows.card eps gminus)
    hb cap G hreal gminus empirical xi hxi₀ hxi₁ hcal hcal₁ he
  have hlargeLoss := large_count_loss part large eps heps hlarge
  have hbudgetLoss := incidenceBudget_loss allRows.card hrows eps gminus heps hgminus
  have hbudgetLoss' : (allRows.card : ℝ) / incidenceBudget allRows.card eps gminus ≤
      eps * Nat.card X / 100 := by
    have hm := mul_le_mul_of_nonneg_left hcal₁ heps.le
    linarith
  have hs' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hbranch' := (div_lt_iff₀ heps).mp hbranch
  have hselected : 2 * (s : ℝ) ≤ eps * Nat.card X / 25 := by nlinarith
  have hsampling : 3 * xi * Nat.card X ≤ 3 * eps * Nat.card X / 100 := by
    have hh := mul_le_mul_of_nonneg_right hxi hg.le
    nlinarith
  refine ⟨hc.1, hc.2.1, ?_⟩
  have hmass : 0 ≤ eps * (Nat.card X : ℝ) := mul_nonneg heps.le hg.le
  linarith [hc.2.2]

theorem ordered_large_branch_contractFor [Nonempty X]
    (μ : Law (Matching.Rank D)) (part : X → A) (hsurj : Function.Surjective part)
    (order : List R) (horder : order.Nodup) (hrows : 0 < order.toFinset.card)
    (E : Finset R) (rows : R → Finset A) (hE : E ⊆ order.toFinset)
    (large covered U : Finset A) (S : Finset R) (s t : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ order.toFinset) (hs : S.card ≤ s) (hst : s ≤ t)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (rows r).card ≤ 2)
    (eps gminus empirical xi : ℝ) (heps : 0 < eps) (heps₁ : eps ≤ 1)
    (hlarge : ∀ a ∈ large, smallThreshold eps < partSize part a)
    (hbranch : 50 * (t : ℝ) / eps < Nat.card X)
    (hxi₀ : 0 ≤ xi) (hxi : xi ≤ eps / 100) (G : Matching.Graph A D)
    (hreal : SetSystem.Realizes G (SetSystem.mutualGraph U E
      (SetSystem.firstIncident order rows (incidenceBudget order.toFinset.card eps gminus))))
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - scoreMeanFor μ part hsurj covered U G| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - eps * Nat.card X ≤ Z gminus empirical xi s :=
  large_branch_contractFor μ part hsurj order.toFinset E hrows rows hE large covered U S s t
    hparts hdisj hcover hS hs hst hineligible eps gminus empirical xi heps heps₁
    hlarge hbranch hxi₀ hxi
    (SetSystem.orderedCap order horder rows U (incidenceBudget order.toFinset.card eps gminus))
    G hreal hcal hcal₁ he

end SteinerUpperBound.SavingScores

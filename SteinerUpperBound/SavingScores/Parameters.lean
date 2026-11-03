module

public import SteinerUpperBound.SavingScores.Ordered

@[expose] public section

namespace SteinerUpperBound.SavingScores

open scoped Classical BigOperators

noncomputable def smallThreshold (eps : ℝ) : ℕ := ⌈10 / eps⌉₊

noncomputable def incidenceBudget (nrows : ℕ) (eps gminus : ℝ) : ℕ :=
  ⌈100 * (nrows : ℝ) / (eps * gminus)⌉₊

theorem incidenceBudget_pos (nrows : ℕ) (hn : 0 < nrows) (eps gminus : ℝ)
    (heps : 0 < eps) (hgminus : 0 < gminus) :
    1 ≤ incidenceBudget nrows eps gminus := by
  have hn' : (0 : ℝ) < nrows := by exact_mod_cast hn
  have hp : 0 < 100 * (nrows : ℝ) / (eps * gminus) := by positivity
  have hh : 100 * (nrows : ℝ) / (eps * gminus) ≤ incidenceBudget nrows eps gminus :=
    Nat.le_ceil _
  by_contra h
  have hz : incidenceBudget nrows eps gminus = 0 := by omega
  rw [hz, Nat.cast_zero] at hh
  linarith

theorem incidenceBudget_loss (nrows : ℕ) (hn : 0 < nrows) (eps gminus : ℝ)
    (heps : 0 < eps) (hgminus : 0 < gminus) :
    (nrows : ℝ) / incidenceBudget nrows eps gminus ≤ eps * gminus / 100 := by
  have hb : (0 : ℝ) < incidenceBudget nrows eps gminus := by
    exact_mod_cast incidenceBudget_pos nrows hn eps gminus heps hgminus
  have hh : 100 * (nrows : ℝ) / (eps * gminus) ≤ incidenceBudget nrows eps gminus :=
    Nat.le_ceil _
  have hm := (div_le_iff₀ (mul_pos heps hgminus)).mp hh
  apply (div_le_iff₀ hb).mpr
  nlinarith

variable {X A R : Type*} [Fintype X] [Fintype A]

theorem large_count_loss (part : X → A) (large : Finset A) (eps : ℝ) (heps : 0 < eps)
    (hlarge : ∀ a ∈ large, smallThreshold eps < partSize part a) :
    (large.card : ℝ) / 2 ≤ eps * Nat.card X / 20 := by
  have hc : ((smallThreshold eps : ℝ) + 1) * (large.card : ℝ) ≤ Nat.card X := by
    exact_mod_cast large_parts_count part large (smallThreshold eps) hlarge
  have hb : (10 : ℝ) / eps ≤ smallThreshold eps := Nat.le_ceil _
  have hb' := (div_le_iff₀ heps).mp hb
  have hB : 10 ≤ eps * ((smallThreshold eps : ℝ) + 1) := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hc heps.le
  have hL : 0 ≤ (large.card : ℝ) := Nat.cast_nonneg _
  have hn := mul_le_mul_of_nonneg_right hB hL
  nlinarith

theorem ordered_large_branch_contract [Nonempty X]
    (part : X → A) (hsurj : Function.Surjective part)
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
    (hxi₀ : 0 ≤ xi) (hxi : xi ≤ eps / 100)
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal₁ : gminus ≤ Nat.card X)
    (he : |empirical - orderedMean part hsurj order E rows covered U
      (incidenceBudget order.toFinset.card eps gminus)| ≤ xi) :
    0 ≤ Z gminus empirical xi s ∧ Z gminus empirical xi s ≤ fullSaving E rows ∧
      fullSaving E rows / 2 - eps * Nat.card X ≤ Z gminus empirical xi s := by
  have hg : (0 : ℝ) < Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hxi₁ : xi ≤ 1 := by linarith
  have hgminus : 0 < gminus :=
    (mul_pos (by linarith : 0 < 1 - xi) hg).trans_le hcal
  have hb := incidenceBudget_pos order.toFinset.card hrows eps gminus heps hgminus
  have hc := ordered_Z_contract part hsurj order horder E rows hE large covered U S s
    hparts hdisj hcover hS hs hineligible (incidenceBudget order.toFinset.card eps gminus)
    hb gminus empirical xi hxi₀ hxi₁ hcal hcal₁ he
  have hlargeLoss := large_count_loss part large eps heps hlarge
  have hbudgetLoss := incidenceBudget_loss order.toFinset.card hrows eps gminus heps hgminus
  have hbudgetLoss' : (order.toFinset.card : ℝ) / incidenceBudget order.toFinset.card eps gminus ≤
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

end SteinerUpperBound.SavingScores

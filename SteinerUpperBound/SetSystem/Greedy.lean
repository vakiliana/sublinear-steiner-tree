module

public import SteinerUpperBound.SetSystem.Basic

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

noncomputable def claimed (rows : R → Finset U) (A : Finset U) (S : Finset R) :
    Finset U := A ∩ S.biUnion rows

theorem claimed_subset (rows : R → Finset U) (A : Finset U) (S : Finset R) :
    claimed rows A S ⊆ A := Finset.inter_subset_left

theorem claimed_mono (rows : R → Finset U) (A : Finset U)
    {S T : Finset R} (hST : S ⊆ T) : claimed rows A S ⊆ claimed rows A T := by
  classical
  exact Finset.inter_subset_inter (Finset.Subset.refl A)
    (Finset.biUnion_subset_biUnion_of_subset_left rows hST)

theorem claimed_contains_row (rows : R → Finset U) (A : Finset U)
    {S : Finset R} {r : R} (hr : r ∈ S) : A ∩ rows r ⊆ claimed rows A S := by
  classical
  intro x hx
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
    Finset.mem_biUnion.mpr ⟨r, hr, (Finset.mem_inter.mp hx).2⟩⟩

/-- Every row is inspected once in the supplied order; an accepted row claims all its elements. -/
noncomputable def smallCoverAux (rows : R → Finset U) (A : Finset U) :
    List R → Finset R → Finset R
  | [], S => S
  | r :: rs, S =>
      if 2 ≤ ((A ∩ rows r) \ claimed rows A S).card then
        smallCoverAux rows A rs (insert r S)
      else smallCoverAux rows A rs S

theorem smallCoverAux_mono (rows : R → Finset U) (A : Finset U)
    (order : List R) (S : Finset R) : S ⊆ smallCoverAux rows A order S := by
  classical
  induction order generalizing S with
  | nil => exact Finset.Subset.refl S
  | cons r rs ih =>
      simp only [smallCoverAux]
      split_ifs
      · exact (Finset.subset_insert r S).trans (ih _)
      · exact ih _

theorem smallCoverAux_subset (rows : R → Finset U) (A : Finset U)
    (order : List R) (S : Finset R) :
    smallCoverAux rows A order S ⊆ S ∪ order.toFinset := by
  classical
  induction order generalizing S with
  | nil => simp [smallCoverAux]
  | cons r rs ih =>
      simp only [smallCoverAux]
      split_ifs
      · exact (ih _).trans (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at hx ⊢
          tauto)
      · exact (ih _).trans (by
          intro x hx
          simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons] at hx ⊢
          tauto)

theorem smallCoverAux_growth (rows : R → Finset U) (A : Finset U)
    (order : List R) (S : Finset R)
    (hS : 2 * S.card ≤ (claimed rows A S).card) :
    2 * (smallCoverAux rows A order S).card ≤
      (claimed rows A (smallCoverAux rows A order S)).card := by
  classical
  induction order generalizing S with
  | nil => exact hS
  | cons r rs ih =>
      simp only [smallCoverAux]
      split_ifs with h
      · apply ih
        have hr : r ∉ S := by
          intro hr
          have he : (A ∩ rows r) \ claimed rows A S = ∅ :=
            Finset.sdiff_eq_empty_iff_subset.mpr (claimed_contains_row rows A hr)
          simp only [he, Finset.card_empty] at h
          omega
        have he : claimed rows A (insert r S) =
            claimed rows A S ∪ ((A ∩ rows r) \ claimed rows A S) := by
          have hins : claimed rows A (insert r S) =
              claimed rows A S ∪ (A ∩ rows r) := by
            ext x
            simp only [claimed, Finset.biUnion_insert, Finset.mem_inter, Finset.mem_union]
            tauto
          rw [hins]
          ext x
          simp only [Finset.mem_union, Finset.mem_sdiff]
          tauto
        have hd : Disjoint (claimed rows A S) ((A ∩ rows r) \ claimed rows A S) := by
          exact Finset.disjoint_left.mpr (fun x hx hy => (Finset.mem_sdiff.mp hy).2 hx)
        rw [he, Finset.card_union_of_disjoint hd, Finset.card_insert_of_notMem hr]
        omega
      · exact ih S hS

theorem smallCoverAux_residual (rows : R → Finset U) (A : Finset U)
    (order : List R) (S : Finset R) :
    ∀ r ∈ order,
      ((A ∩ rows r) \ claimed rows A (smallCoverAux rows A order S)).card ≤ 1 := by
  classical
  induction order generalizing S with
  | nil => simp
  | cons r rs ih =>
      intro q hq
      simp only [List.mem_cons] at hq
      simp only [smallCoverAux]
      split_ifs with h
      · rcases hq with hqr | hq
        · subst q
          have hs : insert r S ⊆ smallCoverAux rows A rs (insert r S) :=
            smallCoverAux_mono rows A rs _
          have hr : r ∈ smallCoverAux rows A rs (insert r S) :=
            hs (Finset.mem_insert_self _ _)
          rw [Finset.sdiff_eq_empty_iff_subset.mpr (claimed_contains_row rows A hr)]
          simp
        · exact ih _ q hq
      · rcases hq with hqr | hq
        · subst q
          have hs := claimed_mono rows A (smallCoverAux_mono rows A rs S)
          have hc := Finset.card_le_card
            (Finset.sdiff_subset_sdiff (Finset.Subset.refl (A ∩ rows r)) hs)
          omega
        · exact ih _ q hq

noncomputable def smallCover (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) : Finset R :=
  smallCoverAux rows A (order.filter (fun r => r ∈ E)) ∅

theorem smallCover_subset (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) : smallCover E rows A order ⊆ E := by
  classical
  intro r hr
  have h := smallCoverAux_subset rows A (order.filter (fun r => r ∈ E)) ∅ hr
  have hh : r ∈ order ∧ r ∈ E := by simpa using h
  exact hh.2

theorem smallCover_growth (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) :
    2 * (smallCover E rows A order).card ≤
      (claimed rows A (smallCover E rows A order)).card := by
  apply smallCoverAux_growth
  simp [claimed]

theorem smallCover_residual (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) (horder : E ⊆ order.toFinset) :
    ∀ r ∈ E, ((A ∩ rows r) \ claimed rows A (smallCover E rows A order)).card ≤ 1 := by
  classical
  intro r hr
  apply smallCoverAux_residual
  simpa using (show r ∈ order ∧ r ∈ E from ⟨List.mem_toFinset.mp (horder hr), hr⟩)

noncomputable def smallCoverEstimate (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) : ℝ :=
  ((claimed rows A (smallCover E rows A order)).card : ℝ) -
    (smallCover E rows A order).card

theorem smallCover_guarantee (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (order : List R) (horder : E ⊆ order.toFinset) :
    0 ≤ smallCoverEstimate E rows A order ∧
      smallCoverEstimate E rows A order ≤ saving E rows A ∧
      saving E rows A / 2 ≤ smallCoverEstimate E rows A order := by
  have hg := smallCover_growth E rows A order
  have hg' : 2 * ((smallCover E rows A order).card : ℝ) ≤
      (claimed rows A (smallCover E rows A order)).card := by exact_mod_cast hg
  have hn : 0 ≤ ((smallCover E rows A order).card : ℝ) := Nat.cast_nonneg _
  have hw := saving_witness E rows A (smallCover E rows A order)
    (smallCover_subset E rows A order)
  have hu := saving_le_claimed E rows A (claimed rows A (smallCover E rows A order))
    (claimed_subset rows A _) (smallCover_residual E rows A order horder)
  change _ ≤ saving E rows A at hw
  change 0 ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
  dsimp only [smallCoverEstimate]
  exact ⟨by linarith, hw, by linarith⟩

end SteinerUpperBound.SetSystem

module

public import SteinerUpperBound.Model

@[expose] public section

namespace SteinerUpperBound.Structural

open scoped Classical BigOperators

variable {R U : Type*}

/-- Eligibility is fixed in `E`; shrinking `A` never reclassifies a row. -/
noncomputable def saving (E : Finset R) (rows : R → Finset U) (A : Finset U) : ℝ :=
  E.powerset.sup' (by exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩)
    (fun F => ((A ∩ F.biUnion rows).card : ℝ) - (F.card : ℝ))

theorem saving_witness (E : Finset R) (rows : R → Finset U) (A : Finset U)
    (F : Finset R) (hF : F ⊆ E) :
    ((A ∩ F.biUnion rows).card : ℝ) - (F.card : ℝ) ≤ saving E rows A := by
  unfold saving
  exact Finset.le_sup'
    (fun F : Finset R => ((A ∩ F.biUnion rows).card : ℝ) - (F.card : ℝ))
    (Finset.mem_powerset.mpr hF)

theorem saving_attained (E : Finset R) (rows : R → Finset U) (A : Finset U) :
    ∃ F ⊆ E, saving E rows A =
      ((A ∩ F.biUnion rows).card : ℝ) - (F.card : ℝ) := by
  obtain ⟨F, hF, he⟩ := Finset.exists_mem_eq_sup'
    (by exact ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset E)⟩)
    (fun F : Finset R => ((A ∩ F.biUnion rows).card : ℝ) - (F.card : ℝ))
  exact ⟨F, Finset.mem_powerset.mp hF, he⟩

theorem saving_nonneg (E : Finset R) (rows : R → Finset U) (A : Finset U) :
    0 ≤ saving E rows A := by
  simpa only [Finset.biUnion_empty, Finset.inter_empty, Finset.card_empty,
    Nat.cast_zero, sub_zero] using saving_witness E rows A ∅ (Finset.empty_subset E)

theorem saving_le_card (E : Finset R) (rows : R → Finset U) (A : Finset U) :
    saving E rows A ≤ (A.card : ℝ) := by
  apply Finset.sup'_le
  intro F _
  have hc : ((A ∩ F.biUnion rows).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card
      (Finset.inter_subset_left (s₁ := A) (s₂ := F.biUnion rows))
  have hn : 0 ≤ (F.card : ℝ) := Nat.cast_nonneg _
  linarith

theorem saving_mono_universe (E : Finset R) (rows : R → Finset U)
    {A B : Finset U} (hAB : A ⊆ B) : saving E rows A ≤ saving E rows B := by
  apply Finset.sup'_le
  intro F hF
  have hc : ((A ∩ F.biUnion rows).card : ℝ) ≤ (B ∩ F.biUnion rows).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter hAB (le_refl (F.biUnion rows)))
  have hh := saving_witness E rows B F (Finset.mem_powerset.mp hF)
  linarith

theorem saving_deletion (E : Finset R) (rows : R → Finset U) (A B : Finset U) :
    saving E rows A - ((A \ B).card : ℝ) ≤ saving E rows B := by
  classical
  apply sub_le_iff_le_add.mpr
  apply Finset.sup'_le
  intro F hF
  have hsub : A ∩ F.biUnion rows ⊆ (B ∩ F.biUnion rows) ∪ (A \ B) := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := Finset.mem_inter.mp hx
    by_cases hxB : x ∈ B
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hxB, hxU⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxA, hxB⟩))
  have hc : ((A ∩ F.biUnion rows).card : ℝ) ≤
      ((B ∩ F.biUnion rows).card : ℝ) + ((A \ B).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hh := saving_witness E rows B F (Finset.mem_powerset.mp hF)
  linarith

theorem saving_domination {U' : Type*} (E E' : Finset R)
    (rows : R → Finset U) (rows' : R → Finset U')
    (A : Finset U) (A' : Finset U') (f : U' → U)
    (hE : E ⊆ E')
    (hrows : ∀ r ∈ E, A ∩ rows r ⊆ (A' ∩ rows' r).image f) :
    saving E rows A ≤ saving E' rows' A' := by
  classical
  apply Finset.sup'_le
  intro F hF
  have hFE := Finset.mem_powerset.mp hF
  have hsub : A ∩ F.biUnion rows ⊆ (A' ∩ F.biUnion rows').image f := by
    intro x hx
    obtain ⟨hxA, hxU⟩ := Finset.mem_inter.mp hx
    obtain ⟨r, hrF, hxr⟩ := Finset.mem_biUnion.mp hxU
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp
      (hrows r (hFE hrF) (Finset.mem_inter.mpr ⟨hxA, hxr⟩))
    obtain ⟨hyA, hyr⟩ := Finset.mem_inter.mp hy
    exact Finset.mem_image.mpr
      ⟨y, Finset.mem_inter.mpr ⟨hyA, Finset.mem_biUnion.mpr ⟨r, hrF, hyr⟩⟩, he⟩
  have hc : ((A ∩ F.biUnion rows).card : ℝ) ≤ (A' ∩ F.biUnion rows').card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le)
  have hh := saving_witness E' rows' A' F (hFE.trans hE)
  linarith

theorem saving_domination_of_rows {U' : Type*} (E E' : Finset R)
    (rows : R → Finset U) (rows' : R → Finset U')
    (A : Finset U) (A' : Finset U') (f : U' → U)
    (hE : E ⊆ E') (hrows : ∀ r ∈ E, rows r ⊆ (rows' r).image f)
    (hA' : ∀ r ∈ E, rows' r ⊆ A') :
    saving E rows A ≤ saving E' rows' A' := by
  classical
  apply saving_domination E E' rows rows' A A' f hE
  intro r hr x hx
  obtain ⟨y, hy, he⟩ := Finset.mem_image.mp (hrows r hr (Finset.mem_inter.mp hx).2)
  exact Finset.mem_image.mpr ⟨y, Finset.mem_inter.mpr ⟨hA' r hr hy, hy⟩, he⟩

end SteinerUpperBound.Structural

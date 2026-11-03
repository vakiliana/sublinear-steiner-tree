module

public import SteinerUpperBound.Structural.Saving

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

export SteinerUpperBound.Structural
  (saving saving_witness saving_attained saving_nonneg saving_le_card
    saving_mono_universe saving_deletion saving_domination saving_domination_of_rows)

variable {R U : Type*}

theorem saving_remove (E : Finset R) (rows : R → Finset U) (A B : Finset U) :
    saving E rows A - (B.card : ℝ) ≤ saving E rows (A \ B) := by
  have h := saving_deletion E rows A (A \ B)
  have hc : ((A \ (A \ B)).card : ℝ) ≤ B.card := by
    exact_mod_cast Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_sdiff] at hx ⊢
      tauto)
  linarith

theorem inter_biUnion_card_le (F : Finset R) (rows : R → Finset U)
    (I : Finset U) (k : ℕ) (h : ∀ r ∈ F, (I ∩ rows r).card ≤ k) :
    (I ∩ F.biUnion rows).card ≤ F.card * k := by
  classical
  have he : I ∩ F.biUnion rows = F.biUnion (fun r => I ∩ rows r) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    aesop
  rw [he]
  exact Finset.card_biUnion_le_card_mul F _ k h

theorem saving_le_of_sparse (E : Finset R) (rows : R → Finset U)
    (A I : Finset U) (hIA : I ⊆ A)
    (hsparse : ∀ r ∈ E, (I ∩ rows r).card ≤ 1) :
    saving E rows A ≤ (A.card : ℝ) - I.card := by
  classical
  obtain ⟨F, hF, he⟩ := saving_attained E rows A
  have hsub : A ∩ F.biUnion rows ⊆ (A \ I) ∪ (I ∩ F.biUnion rows) := by
    intro x hx
    by_cases hxI : x ∈ I
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
        ⟨hxI, (Finset.mem_inter.mp hx).2⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨(Finset.mem_inter.mp hx).1, hxI⟩))
  have hc : (A ∩ F.biUnion rows).card ≤ (A \ I).card + F.card := by
    calc
      _ ≤ ((A \ I) ∪ (I ∩ F.biUnion rows)).card := Finset.card_le_card hsub
      _ ≤ (A \ I).card + (I ∩ F.biUnion rows).card := Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (by
        simpa using inter_biUnion_card_le F rows I 1 (fun r hr => hsparse r (hF hr))) _
  have hd := Finset.card_sdiff_add_card_eq_card hIA
  have hc' : ((A ∩ F.biUnion rows).card : ℝ) ≤ (A \ I).card + (F.card : ℝ) := by
    exact_mod_cast hc
  have hd' : ((A \ I).card : ℝ) + (I.card : ℝ) = A.card := by exact_mod_cast hd
  rw [he]
  linarith

theorem saving_le_claimed (E : Finset R) (rows : R → Finset U)
    (A C : Finset U) (hCA : C ⊆ A)
    (hsparse : ∀ r ∈ E, ((A ∩ rows r) \ C).card ≤ 1) :
    saving E rows A ≤ (C.card : ℝ) := by
  classical
  have he (r : R) : (A \ C) ∩ rows r = (A ∩ rows r) \ C := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have h := saving_le_of_sparse E rows A (A \ C) (Finset.sdiff_subset)
    (by simpa only [he] using hsparse)
  have hd := Finset.card_sdiff_add_card_eq_card hCA
  have hd' : ((A \ C).card : ℝ) + (C.card : ℝ) = A.card := by exact_mod_cast hd
  linarith

end SteinerUpperBound.SetSystem

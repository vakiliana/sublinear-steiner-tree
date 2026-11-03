module

public import SteinerUpperBound.SetSystem.Basic

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

theorem saving_score_upper (E : Finset R) (rows : R → Finset U)
    (A large covered remaining : Finset U)
    (hpartition : A ⊆ large ∪ covered ∪ remaining) :
    saving E rows A ≤
      (large.card : ℝ) + covered.card + saving E rows remaining := by
  classical
  have hsub : A \ remaining ⊆ large ∪ covered := by
    intro x hx
    obtain ⟨hxA, hxR⟩ := Finset.mem_sdiff.mp hx
    have hp := hpartition hxA
    simp only [Finset.mem_union] at hp ⊢
    tauto
  have hc : ((A \ remaining).card : ℝ) ≤ (large.card : ℝ) + covered.card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hd := saving_deletion E rows A remaining
  linarith

theorem saving_score_lower (E : Finset R) (rows : R → Finset U)
    (A covered remaining : Finset U) (S : Finset R)
    (hcoveredA : covered ⊆ A) (hremainingA : remaining ⊆ A)
    (hdisjoint : Disjoint covered remaining)
    (hcovered : covered ⊆ S.biUnion rows)
    (hineligible : ∀ r ∈ S, r ∉ E → (A ∩ rows r).card ≤ 2) :
    (covered.card : ℝ) - 2 * S.card + saving E rows remaining ≤ saving E rows A := by
  classical
  let good := S ∩ E
  let bad := S \ E
  let D := covered ∩ good.biUnion rows
  obtain ⟨F, hF, he⟩ := saving_attained E rows remaining
  have hgood : good ⊆ E := Finset.inter_subset_right
  have hloss : covered \ D ⊆ A ∩ bad.biUnion rows := by
    intro x hx
    obtain ⟨hxC, hxD⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨r, hrS, hxr⟩ := Finset.mem_biUnion.mp (hcovered hxC)
    have hrE : r ∉ E := by
      intro hrE
      exact hxD (Finset.mem_inter.mpr ⟨hxC, Finset.mem_biUnion.mpr
        ⟨r, Finset.mem_inter.mpr ⟨hrS, hrE⟩, hxr⟩⟩)
    exact Finset.mem_inter.mpr ⟨hcoveredA hxC,
      Finset.mem_biUnion.mpr ⟨r, Finset.mem_sdiff.mpr ⟨hrS, hrE⟩, hxr⟩⟩
  have hloss_card : (covered \ D).card ≤ 2 * bad.card := by
    calc
      _ ≤ (A ∩ bad.biUnion rows).card := Finset.card_le_card hloss
      _ ≤ bad.card * 2 := inter_biUnion_card_le bad rows A 2 (by
        intro r hr
        exact hineligible r (Finset.mem_sdiff.mp hr).1 (Finset.mem_sdiff.mp hr).2)
      _ = _ := Nat.mul_comm _ _
  have hDU : Disjoint D (remaining ∩ F.biUnion rows) := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxR
    exact Finset.disjoint_left.mp hdisjoint
      (Finset.mem_inter.mp hxD).1 (Finset.mem_inter.mp hxR).1
  have hsub : D ∪ (remaining ∩ F.biUnion rows) ⊆
      A ∩ (F ∪ good).biUnion rows := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxC, hxG⟩ := Finset.mem_inter.mp hx
      obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hxG
      exact Finset.mem_inter.mpr ⟨hcoveredA hxC,
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hxr⟩⟩
    · obtain ⟨hxR, hxF⟩ := Finset.mem_inter.mp hx
      obtain ⟨r, hr, hxr⟩ := Finset.mem_biUnion.mp hxF
      exact Finset.mem_inter.mpr ⟨hremainingA hxR,
        Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_left _ hr, hxr⟩⟩
  have hcovered_card : D.card + (remaining ∩ F.biUnion rows).card ≤
      (A ∩ (F ∪ good).biUnion rows).card := by
    rw [← Finset.card_union_of_disjoint hDU]
    exact Finset.card_le_card hsub
  have hfamily_card : (F ∪ good).card ≤ F.card + good.card := Finset.card_union_le _ _
  have hDC : D ⊆ covered := Finset.inter_subset_left
  have hsplit := Finset.card_sdiff_add_card_eq_card hDC
  have hgoodbad : bad.card + good.card = S.card := by
    have hh := Finset.card_sdiff_add_card_eq_card
      (Finset.inter_subset_left (s₁ := S) (s₂ := E))
    have hs : S \ (S ∩ E) = bad := by
      ext r
      simp only [bad, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    simpa only [hs] using hh
  have hw := saving_witness E rows A (F ∪ good) (Finset.union_subset hF hgood)
  have hcovered_card' :
      (D.card : ℝ) + (remaining ∩ F.biUnion rows).card ≤
        (A ∩ (F ∪ good).biUnion rows).card := by exact_mod_cast hcovered_card
  have hfamily_card' : ((F ∪ good).card : ℝ) ≤ (F.card : ℝ) + good.card := by
    exact_mod_cast hfamily_card
  have hloss_card' : ((covered \ D).card : ℝ) ≤ 2 * (bad.card : ℝ) := by
    exact_mod_cast hloss_card
  have hsplit' : ((covered \ D).card : ℝ) + D.card = covered.card := by
    exact_mod_cast hsplit
  have hgoodbad' : (bad.card : ℝ) + good.card = S.card := by exact_mod_cast hgoodbad
  have hgood_nonneg : 0 ≤ (good.card : ℝ) := Nat.cast_nonneg _
  rw [he]
  linarith

theorem saving_scores (E : Finset R) (rows : R → Finset U)
    (A large covered remaining : Finset U) (S : Finset R)
    (hpartition : A ⊆ large ∪ covered ∪ remaining)
    (hcoveredA : covered ⊆ A) (hremainingA : remaining ⊆ A)
    (hdisjoint : Disjoint covered remaining)
    (hcovered : covered ⊆ S.biUnion rows)
    (hineligible : ∀ r ∈ S, r ∉ E → (A ∩ rows r).card ≤ 2) :
    saving E rows A ≤ (large.card : ℝ) + covered.card + saving E rows remaining ∧
      (covered.card : ℝ) - 2 * S.card + saving E rows remaining ≤ saving E rows A :=
  ⟨saving_score_upper E rows A large covered remaining hpartition,
    saving_score_lower E rows A covered remaining S hcoveredA hremainingA
      hdisjoint hcovered hineligible⟩

end SteinerUpperBound.SetSystem

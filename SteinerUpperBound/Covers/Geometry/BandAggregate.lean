module

public import SteinerUpperBound.Covers.Geometry.BandComplete

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandCompleteness

open SteinerLowerBound
open scoped Classical BigOperators Interval

variable {V : Type*} [Fintype V]

noncomputable def highComponents (I : Instance V) (a : ℝ) : Finset (Finset V) :=
  (Structural.components I a).filter
    (fun C => Structural.sigma0 * a ≤ Structural.localAdvantage I C)

noncomputable def smallRetained (I : Instance V) (N : Finset V) (a : ℝ) (BQ : ℕ) :
    Finset (Finset V) :=
  (componentsOn I N a).filter (fun D => D.card ≤ BQ)

noncomputable def largeRetained (I : Instance V) (N : Finset V) (a : ℝ) (BQ : ℕ) :
    Finset (Finset V) :=
  (componentsOn I N a).filter (fun D => BQ < D.card)

noncomputable def smallScore (I : Instance V) (N : Finset V) (a ρ : ℝ) (BQ : ℕ) : ℝ :=
  ∑ D ∈ smallRetained I N a BQ, Band.score I D a ρ bandTau

/-- Single-scale deterministic completeness. High exact components charge
injectively to small retained band scores, deterministic phase-bad components,
or large retained components. -/
theorem single_scale_completeness (I : Instance V) (N : Finset V) (ρ : ℝ)
    (hc : CoverOn I I.terminals N ρ) (hNT : N ⊆ I.terminals) (hρ : 0 ≤ ρ)
    (a : ℝ) (ha : 0 < a) (hsmall : ρ ≤ bandDelta * a) (BQ : ℕ) :
    a * (highComponents I a).card ≤
      2 * smallScore I N a ρ BQ / Structural.sigma0 +
        a * (phaseBad I I.terminals (a - 2 * ρ) a).card +
        a * (largeRetained I N a BQ).card := by
  classical
  let H := highComponents I a
  let P := phaseBad I I.terminals (a - 2 * ρ) a
  let S := H.filter (fun C => C ∉ P ∧ (N ∩ C).card ≤ BQ)
  let L := H.filter (fun C => C ∉ P ∧ BQ < (N ∩ C).card)
  let f : Finset V → Finset V := fun C => N ∩ C
  let q : Finset V → ℝ := fun D => Band.score I D a ρ bandTau
  have hρa := (band_parameters a ρ ha hρ hsmall).1
  have hH (C : Finset V) (hC : C ∈ H) :
      C ∈ componentsOn I I.terminals a ∧
        Structural.sigma0 * a ≤ Structural.localAdvantage I C := by
    obtain ⟨hCcomp, hhigh⟩ := Finset.mem_filter.mp hC
    exact ⟨by rwa [componentsOn_terminals_eq], hhigh⟩
  have hcomp (C : Finset V) (hC : C ∈ H) (hCP : C ∉ P) :
      f C ∈ componentsOn I N a ∧ componentMap I I.terminals a (f C) = C :=
    persistent_retained_component I N ρ hc hNT hρ a hρa (hH C hC).1 hCP
  have hscore (C : Finset V) (hC : C ∈ H) (hCP : C ∉ P) :
      Structural.sigma0 * a / 2 ≤ q (f C) := by
    have hCstruct : C ∈ Structural.components I a := (Finset.mem_filter.mp hC).1
    exact (retained_band_completeness I N ρ hc hNT hρ a ha hsmall
      hCstruct hCP (hH C hC).2).2.2
  have hinj (C : Finset V) (hC : C ∈ H) (hCP : C ∉ P)
      (D : Finset V) (hD : D ∈ H) (hDP : D ∉ P) (he : f C = f D) : C = D := by
    have he' := congrArg (componentMap I I.terminals a) he
    rwa [(hcomp C hC hCP).2, (hcomp D hD hDP).2] at he'
  have hinjS : Set.InjOn f (S : Set (Finset V)) := by
    intro C hC D hD he
    obtain ⟨hCH, hCP, _⟩ := Finset.mem_filter.mp hC
    obtain ⟨hDH, hDP, _⟩ := Finset.mem_filter.mp hD
    exact hinj C hCH hCP D hDH hDP he
  have hinjL : Set.InjOn f (L : Set (Finset V)) := by
    intro C hC D hD he
    obtain ⟨hCH, hCP, _⟩ := Finset.mem_filter.mp hC
    obtain ⟨hDH, hDP, _⟩ := Finset.mem_filter.mp hD
    exact hinj C hCH hCP D hDH hDP he
  have hSimage : S.image f ⊆ smallRetained I N a BQ := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hCH, hCP, hsize⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨(hcomp C hCH hCP).1, hsize⟩
  have hLimage : L.image f ⊆ largeRetained I N a BQ := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hD
    obtain ⟨hCH, hCP, hsize⟩ := Finset.mem_filter.mp hC
    exact Finset.mem_filter.mpr ⟨(hcomp C hCH hCP).1, hsize⟩
  have hLcard : L.card ≤ (largeRetained I N a BQ).card := by
    rw [← Finset.card_image_of_injOn hinjL]
    exact Finset.card_le_card hLimage
  have hSsum : (∑ C ∈ S, q (f C)) ≤ smallScore I N a ρ BQ := by
    calc
      _ = ∑ D ∈ S.image f, q D := by rw [Finset.sum_image hinjS]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSimage
        (fun D _ _ => Band.score_nonneg I D a ρ bandTau)
  have hpoint (C : Finset V) (hC : C ∈ S) : a ≤ (2 / Structural.sigma0) * q (f C) := by
    obtain ⟨hCH, hCP, _⟩ := Finset.mem_filter.mp hC
    have hs := mul_le_mul_of_nonneg_left (hscore C hCH hCP) (by norm_num : (0 : ℝ) ≤ 2)
    have he : 2 * (Structural.sigma0 * a / 2) = Structural.sigma0 * a := by ring
    rw [he] at hs
    calc
      a ≤ (2 * q (f C)) / Structural.sigma0 :=
        (le_div_iff₀ sigma0_pos).mpr (by simpa only [mul_comm] using hs)
      _ = _ := by ring
  have hScharge : a * (S.card : ℝ) ≤ 2 * smallScore I N a ρ BQ / Structural.sigma0 := by
    have hs := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum] at hs
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    have hq := mul_le_mul_of_nonneg_left hSsum
      (by positivity : 0 ≤ 2 / Structural.sigma0)
    calc
      _ ≤ (2 / Structural.sigma0) * ∑ C ∈ S, q (f C) := by
        simpa only [mul_comm] using hs
      _ ≤ (2 / Structural.sigma0) * smallScore I N a ρ BQ := hq
      _ = _ := by ring
  have hcover : H ⊆ P ∪ (S ∪ L) := by
    intro C hC
    by_cases hCP : C ∈ P
    · exact Finset.mem_union.mpr (Or.inl hCP)
    · apply Finset.mem_union.mpr
      apply Or.inr
      by_cases hsize : (N ∩ C).card ≤ BQ
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hC, hCP, hsize⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hC, hCP, Nat.lt_of_not_ge hsize⟩))
  have hcard : H.card ≤ P.card + S.card + L.card := by
    have h₁ := Finset.card_le_card hcover
    have h₂ := Finset.card_union_le P (S ∪ L)
    have h₃ := Finset.card_union_le S L
    omega
  have hcardR : (H.card : ℝ) ≤ (P.card : ℝ) + S.card + L.card := by exact_mod_cast hcard
  have hmass := mul_le_mul_of_nonneg_left hcardR ha.le
  have hlargeR : (L.card : ℝ) ≤ (largeRetained I N a BQ).card := by exact_mod_cast hLcard
  have hlargeMass := mul_le_mul_of_nonneg_left hlargeR ha.le
  rw [mul_add, mul_add] at hmass
  change a * (H.card : ℝ) ≤
    2 * smallScore I N a ρ BQ / Structural.sigma0 +
      a * (P.card : ℝ) + a * (largeRetained I N a BQ).card
  linarith

noncomputable def totalSmallScore (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (ρ : Fin (g.intervals + 1) → ℝ) (BQ : ℕ) : ℝ :=
  ∑ i, smallScore I (N i) (g.scale i) (ρ i) BQ

noncomputable def weightedPhaseBad (I : Instance V) (g : Structural.Grid)
    (ρ : Fin (g.intervals + 1) → ℝ) : ℝ :=
  ∑ i, g.scale i * (phaseBad I I.terminals (g.scale i - 2 * ρ i) (g.scale i)).card

noncomputable def weightedLarge (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (BQ : ℕ) : ℝ :=
  ∑ i, g.scale i * (largeRetained I (N i) (g.scale i) BQ).card

/-- The aggregate completeness inequality for the actual `Structural.lambda`
and actual retained band scores. Phase and large-component accounting are
deterministic terms; no shift distribution or cover-conditioned independence
is assumed. -/
theorem lambda_le_smallScore_and_bad (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (ρ : Fin (g.intervals + 1) → ℝ)
    (hc : ∀ i, CoverOn I I.terminals (N i) (ρ i))
    (hNT : ∀ i, N i ⊆ I.terminals) (hρ : ∀ i, 0 ≤ ρ i)
    (hsmall : ∀ i, ρ i ≤ bandDelta * g.scale i) (BQ : ℕ) :
    Structural.lambda I g ≤
      2 * totalSmallScore I g N ρ BQ / Structural.sigma0 +
        weightedPhaseBad I g ρ + weightedLarge I g N BQ := by
  calc
    _ ≤ ∑ i, (2 * smallScore I (N i) (g.scale i) (ρ i) BQ / Structural.sigma0 +
        g.scale i * (phaseBad I I.terminals (g.scale i - 2 * ρ i) (g.scale i)).card +
        g.scale i * (largeRetained I (N i) (g.scale i) BQ).card) := by
      apply Finset.sum_le_sum
      intro i _
      exact single_scale_completeness I (N i) (ρ i) (hc i) (hNT i) (hρ i)
        (g.scale i) (g.positive i) (hsmall i) BQ
    _ = _ := by
      simp only [totalSmallScore, weightedPhaseBad, weightedLarge,
        Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]

end SteinerUpperBound.Covers.Geometry.BandCompleteness

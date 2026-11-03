module

public import SteinerLowerBound.Screening.LuckyProbability
public import SteinerLowerBound.MetricComparison.Experiments

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {S G I C W : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def liftSpecial (H : Finset S) : Finset (Terminal S G I) :=
  H.map Function.Embedding.inl

@[simp]
theorem mem_liftSpecial (H : Finset S) (u : S) :
    Sum.inl u ∈ liftSpecial (G := G) (I := I) H ↔ u ∈ H := by
  simp [liftSpecial]

@[simp]
theorem ordinary_not_mem_liftSpecial (H : Finset S) (p : G × I) :
    Sum.inr p ∉ liftSpecial H := by simp [liftSpecial]

@[simp]
theorem card_liftSpecial (H : Finset S) :
    (liftSpecial (G := G) (I := I) H).card = H.card := by simp [liftSpecial]

theorem liftSpecial_supported (H : Finset S) (v : Terminal S G I)
    (hv : v ∈ liftSpecial H) : specialPosition v := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_map.mp hv
  trivial

namespace Experiment

open HardDistribution

abbrev Base (S C W : Type*) := (S → W) × (C → Filler S)

noncomputable def baseLaw (k : Setup S W) (μ : Law W) : Law (Base S C W) :=
  Law.conditionalProduct (μ.iid S) (fun _ _ =>
    fillerLaw (by have := k.d_ge_three; have := k.enough_special; omega))

noncomputable def kernel (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (b : Base S C W) (c : C) :
    Law (Option (Subsets S k.d)) :=
  MetricComparison.markLaw k b.1 hsmall (b.2 c)

noncomputable def fillers (b : Base S C W) (c : C) : Finset (Terminal S G I) :=
  liftSpecial (fillerNeighbors (b.2 c))

noncomputable def starSupport (d : ℕ) (H : Subsets S d) : Finset (Terminal S G I) :=
  liftSpecial H.val

noncomputable def law (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    Law ((Base S C W × (C → Option (Subsets S k.d))) × Equiv.Perm (Terminal S G I)) :=
  shuffledLaw (Law.conditionalProduct (baseLaw (C := C) k μ) (kernel k hsmall))

theorem fillers_supported (b : Base S C W) : Supported (fillers (G := G) (I := I) b) :=
  fun _ _ hv => liftSpecial_supported _ _ hv

theorem fillers_card (b : Base S C W) (c : C) :
    (fillers (G := G) (I := I) b c).card ≤ 2 := by
  simpa only [fillers, card_liftSpecial] using filler_card_le_two (b.2 c)

theorem stars_supported (d : ℕ) (a : Subsets S d) (u : Terminal S G I)
    (hu : u ∈ starSupport d a) : specialPosition u :=
  liftSpecial_supported _ _ hu

theorem kernel_present_le (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (b : Base S C W) (c : C) :
    (kernel k hsmall b c).prob {a | a ≠ none} ≤ anchorConstant k.d k.H0 k.M / k.R := by
  classical
  have hnonneg : 0 ≤ anchorConstant k.d k.H0 k.M / k.R := by
    unfold anchorConstant
    have hM : 0 ≤ k.M := by
      obtain ⟨s⟩ : Nonempty S := Fintype.card_pos_iff.mp
        (by have := k.d_ge_three; have := k.enough_special; omega)
      exact (k.bounded (b.1 s)).1.trans (k.bounded (b.1 s)).2
    have hH0 := k.H0_nonneg
    have hR := k.R_pos
    positivity
  rcases hf : b.2 c with (_ | u | e)
  · simp [kernel, MetricComparison.markLaw, hf, Law.prob_pure, hnonneg]
  · simp [kernel, MetricComparison.markLaw, hf, Law.prob_pure, hnonneg]
  · have hh := anchor_mass_le k.d (by have := k.d_ge_three; omega)
      k.enough_special e k.H0_nonneg k.R_pos
      (fun u => (k.bounded (b.1 u)).1) (fun u => (k.bounded (b.1 u)).2)
    simpa [kernel, MetricComparison.markLaw, hf, potentialLaw, Law.prob,
      Law.withNone, Fintype.sum_option] using hh

theorem kernel_absent_ge_half (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hhalf : anchorConstant k.d k.H0 k.M / k.R ≤ 1 / 2)
    (b : Base S C W) (c : C) :
    1 / 2 ≤ (kernel k hsmall b c).mass none := by
  let ν := kernel k hsmall b c
  have hp := kernel_present_le k hsmall b c
  have ht := ν.total
  have he : ν.prob {a | a ≠ none} = ∑ a, ν.mass (some a) := by
    simp [Law.prob, Fintype.sum_option]
  rw [Fintype.sum_option] at ht
  change ν.prob {a | a ≠ none} ≤ _ at hp
  rw [he] at hp
  dsimp only [ν] at *
  linarith

theorem kernel_anchor_support (k : Setup S W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (b : Base S C W) (c : C) (H : Subsets S k.d)
    (hpos : 0 < (kernel k hsmall b c).mass (some H)) :
    fillerNeighbors (b.2 c) ⊆ H.val := by
  classical
  rcases hf : b.2 c with (_ | u | e)
  · simp [kernel, MetricComparison.markLaw, hf, Law.pure] at hpos
  · simp [kernel, MetricComparison.markLaw, hf, Law.pure] at hpos
  · by_contra hn
    simp only [fillerNeighbors] at hn
    simp [kernel, MetricComparison.markLaw, hf, potentialLaw, Law.withNone,
      hn] at hpos

theorem positive_configuration_anchor_support (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (ω : (Base S C W × (C → Option (Subsets S k.d))) × Equiv.Perm (Terminal S G I))
    (hpos : 0 < (law k μ hsmall).mass ω) :
    ∀ c, (starSupports (starSupport (G := G) (I := I) k.d) ω.1.2 c).Nonempty →
      fillers (G := G) (I := I) ω.1.1 c ⊆
        starSupports (starSupport (G := G) (I := I) k.d) ω.1.2 c := by
  classical
  have hdata : 0 < (Law.conditionalProduct (baseLaw (C := C) k μ) (kernel k hsmall)).mass ω.1 :=
    pos_of_mul_pos_left hpos (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hpi : 0 < (Law.pi (kernel k hsmall ω.1.1)).mass ω.1.2 :=
    pos_of_mul_pos_right hdata ((baseLaw k μ).nonneg _)
  intro c hc
  have hk := Law.pi_mass_positive (kernel k hsmall ω.1.1) ω.1.2 hpi c
  cases he : ω.1.2 c with
  | none => simp [starSupports, he] at hc
  | some H =>
      have hF := kernel_anchor_support k hsmall ω.1.1 c H (he ▸ hk)
      intro v hv
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hv
      change Sum.inl s ∈ starSupports (starSupport k.d) ω.1.2 c
      simp only [starSupports, he, Option.elim_some, starSupport]
      exact (mem_liftSpecial _ _).mpr (hF hs)

end Experiment

end Screening

end SteinerLowerBound

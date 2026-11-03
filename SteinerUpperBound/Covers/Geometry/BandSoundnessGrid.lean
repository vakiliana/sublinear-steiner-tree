module

public import SteinerUpperBound.Covers.Geometry.BandSoundnessIntegral
public import SteinerUpperBound.SavingSoundness.Grid

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry.BandSoundness

open SteinerLowerBound
open scoped Classical BigOperators Interval
open BandCompleteness

theorem bandTau_pos : 0 < bandTau := div_pos sigma0_pos (by norm_num)

theorem grid_scale_band_separated (g : Structural.Grid) (q : ℕ)
    (hsep : Structural.omega ^ (-(q : ℤ)) < bandTau / 2)
    (i j : Fin (g.intervals + 1)) (hgap : i.val + q ≤ j.val) :
    g.scale i < bandTau * g.scale j := by
  have hω : (1 : ℝ) ≤ Structural.omega := by norm_num [Structural.omega]
  have hωpos : (0 : ℝ) < Structural.omega := by norm_num [Structural.omega]
  have hpow : 0 < Structural.omega ^ q := pow_pos hωpos _
  have hsep' : Structural.omega ^ (-(q : ℤ)) < bandTau :=
    hsep.trans (by linarith [bandTau_pos])
  have hdiv : (1 : ℝ) / Structural.omega ^ q < bandTau := by
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv, one_mul] using hsep'
  have hcoef : 1 < bandTau * Structural.omega ^ q := (div_lt_iff₀ hpow).mp hdiv
  have hscale : Structural.omega ^ q * g.scale i ≤ g.scale j := by
    rw [SavingSoundness.grid_scale_pow g i, SavingSoundness.grid_scale_pow g j,
      ← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hω (by omega)) (g.positive 0).le
  calc
    _ = 1 * g.scale i := by ring
    _ < (bandTau * Structural.omega ^ q) * g.scale i :=
      mul_lt_mul_of_pos_right hcoef (g.positive i)
    _ = bandTau * (Structural.omega ^ q * g.scale i) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale bandTau_pos.le

variable {V : Type*} [Fintype V]

noncomputable def gridScaleData (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (ρ : Fin (g.intervals + 1) → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hsmall : ∀ i, ρ i ≤ bandDelta * g.scale i)
    (hN : ∀ i, N i ⊆ I.terminals) (hc : ∀ i, CoverOn I I.terminals (N i) (ρ i))
    (i : Fin (g.intervals + 1)) : ScaleData I where
  a := g.scale i
  rho := ρ i
  retained := N i
  positive := g.positive i
  rho_nonneg := hρ i
  rho_small := hsmall i
  subset := hN i
  cover := hc i

theorem residue_separated (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (ρ : Fin (g.intervals + 1) → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hsmall : ∀ i, ρ i ≤ bandDelta * g.scale i)
    (hN : ∀ i, N i ⊆ I.terminals) (hc : ∀ i, CoverOn I I.terminals (N i) (ρ i))
    (q : ℕ) (hsep : Structural.omega ^ (-(q : ℤ)) < bandTau / 2) (r : Fin q) :
    ((SavingSoundness.residueIndices g q r).map
      (gridScaleData I g N ρ hρ hsmall hN hc)).Pairwise Separated := by
  rw [List.pairwise_map]
  have ho : (SavingSoundness.residueIndices g q r).Pairwise (fun i j => i.val < j.val) :=
    (SavingSoundness.finRange_pairwise _).filter _
  apply List.Pairwise.imp_of_mem (p := ho)
  intro i j hi hj hij
  have himod : i.val % q = r.val := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hi).2
  have hjmod : j.val % q = r.val := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp hj).2
  have hgap := SavingSoundness.residue_gap i.val j.val q hij (himod.trans hjmod.symm)
  exact grid_scale_band_separated g q hsep i j hgap

/-- Exact grid soundness, with arbitrary actual cover radii below `10⁻¹⁰ a`.
All band separation follows from the actual geometric grid ratio. -/
theorem grid_soundness (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (ρ : Fin (g.intervals + 1) → ℝ)
    (hN : ∀ i, N i ⊆ I.terminals) (hc : ∀ i, CoverOn I I.terminals (N i) (ρ i))
    (hρ : ∀ i, 0 ≤ ρ i) (hsmall : ∀ i, ρ i ≤ bandDelta * g.scale i)
    (Qq : ℕ) (hQq : 0 < Qq)
    (hsep : Structural.omega ^ (-(Qq : ℤ)) < bandTau / 2) :
    (∑ i, ∑ C ∈ componentsOn I (N i) (g.scale i),
      Band.score I C (g.scale i) (ρ i) bandTau) ≤ (Qq : ℝ) * (I.mst - I.optimum) := by
  classical
  let w := fun i : Fin (g.intervals + 1) =>
    ∑ C ∈ componentsOn I (N i) (g.scale i), Band.score I C (g.scale i) (ρ i) bandTau
  have hclass (r : Fin Qq) :
      ∑ i ∈ (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % Qq = r.val)), w i ≤
        I.mst - I.optimum := by
    have hh := separated_sound I
      ((SavingSoundness.residueIndices g Qq r).map (gridScaleData I g N ρ hρ hsmall hN hc))
      (residue_separated I g N ρ hρ hsmall hN hc Qq hsep r)
    have hn : (SavingSoundness.residueIndices g Qq r).Nodup :=
      (List.nodup_finRange _).filter _
    have he : (SavingSoundness.residueIndices g Qq r).toFinset =
        Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % Qq = r.val) := by
      ext i
      simp [SavingSoundness.residueIndices]
    have hh' : ((SavingSoundness.residueIndices g Qq r).map w).sum ≤ I.mst - I.optimum := by
      simpa only [List.map_map, Function.comp_def, gridScaleData, scaleScore, w] using hh
    rw [← List.sum_toFinset w hn, he] at hh'
    exact hh'
  let residue : Fin (g.intervals + 1) → Fin Qq :=
    fun i => ⟨i.val % Qq, Nat.mod_lt _ hQq⟩
  have hsplit :
      (∑ r : Fin Qq, ∑ i ∈
        (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % Qq = r.val)), w i) =
        ∑ i, w i := by
    simpa only [Fin.ext_iff, residue] using
      (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin (g.intervals + 1))))
        (t := (Finset.univ : Finset (Fin Qq))) (g := residue)
        (fun i _ => Finset.mem_univ (residue i)) w)
  change (∑ i, w i) ≤ _
  calc
    _ = ∑ r : Fin Qq, ∑ i ∈
        (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % Qq = r.val)), w i :=
      hsplit.symm
    _ ≤ ∑ _r : Fin Qq, (I.mst - I.optimum) := Finset.sum_le_sum (fun r _ => hclass r)
    _ = _ := by simp; ring

theorem retained_band_sound (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (bandDelta * g.scale i))
    (Qq : ℕ) (hQq : 0 < Qq)
    (hsep : Structural.omega ^ (-(Qq : ℤ)) < bandTau / 2) :
    (∑ i, ∑ C ∈ componentsOn I (N i) (g.scale i),
      Band.score I C (g.scale i) (bandDelta * g.scale i) bandTau) ≤
        (Qq : ℝ) * (I.mst - I.optimum) :=
  grid_soundness I g N (fun i => bandDelta * g.scale i) hN hc
    (fun i => mul_nonneg (by norm_num [bandDelta]) (g.positive i).le)
    (fun _ => le_rfl) Qq hQq hsep

theorem small_retained_band_sound (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (bandDelta * g.scale i))
    (BQ Qq : ℕ) (hQq : 0 < Qq)
    (hsep : Structural.omega ^ (-(Qq : ℤ)) < bandTau / 2) :
    totalSmallScore I g N (fun i => bandDelta * g.scale i) BQ ≤
      (Qq : ℝ) * (I.mst - I.optimum) := by
  apply le_trans _ (retained_band_sound I g N hN hc Qq hQq hsep)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
  intro C _ _
  exact Band.score_nonneg I C (g.scale i) (bandDelta * g.scale i) bandTau

end SteinerUpperBound.Covers.Geometry.BandSoundness

module

public import SteinerUpperBound.SavingSoundness.Separated
public import Mathlib.Data.List.FinRange

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open Covers.Geometry
open scoped Classical BigOperators

theorem grid_scale_pow (g : Structural.Grid) (i : Fin (g.intervals + 1)) :
    g.scale i = Structural.omega ^ i.val * g.scale 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
      rw [g.ratio i, ih]
      simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
      ring

theorem residue_gap (i j q : ℕ) (hij : i < j) (hmod : i % q = j % q) :
    i + q ≤ j := by
  have hi := Nat.mod_add_div i q
  have hj := Nat.mod_add_div j q
  have hd : i / q < j / q := by
    by_contra hn
    have hh := Nat.mul_le_mul_left q (Nat.le_of_not_gt hn)
    omega
  have hh := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hd)
  simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hh
  omega

theorem grid_scale_separated (g : Structural.Grid) (δ : ℝ)
    (hδ : 64 * δ ≤ 1) (q : ℕ)
    (hsep : (5 / 4 : ℝ) * Structural.omega ^ (-(q : ℤ)) < 1 - 2 * δ)
    (i j : Fin (g.intervals + 1)) (hgap : i.val + q ≤ j.val) :
    5 * g.scale i / 4 < g.scale j - 2 * (δ * g.scale j) := by
  have hω : (1 : ℝ) ≤ Structural.omega := by norm_num [Structural.omega]
  have hωpos : (0 : ℝ) < Structural.omega := by norm_num [Structural.omega]
  have hpow : 0 < Structural.omega ^ q := pow_pos hωpos _
  have hdiv : (5 / 4 : ℝ) / Structural.omega ^ q < 1 - 2 * δ := by
    simpa only [zpow_neg, zpow_natCast, div_eq_mul_inv] using hsep
  have hr : (5 / 4 : ℝ) < (1 - 2 * δ) * Structural.omega ^ q :=
    (div_lt_iff₀ hpow).mp hdiv
  have hscale : Structural.omega ^ q * g.scale i ≤ g.scale j := by
    rw [grid_scale_pow g i, grid_scale_pow g j, ← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hω (by omega)) (g.positive 0).le
  have hcoef : 0 ≤ 1 - 2 * δ := by linarith
  calc
    _ = (5 / 4 : ℝ) * g.scale i := by ring
    _ < ((1 - 2 * δ) * Structural.omega ^ q) * g.scale i :=
      mul_lt_mul_of_pos_right hr (g.positive i)
    _ = (1 - 2 * δ) * (Structural.omega ^ q * g.scale i) := by ring
    _ ≤ (1 - 2 * δ) * g.scale j := mul_le_mul_of_nonneg_left hscale hcoef
    _ = _ := by ring

def residueIndices (g : Structural.Grid) (q : ℕ) (r : Fin q) :
    List (Fin (g.intervals + 1)) :=
  (List.finRange (g.intervals + 1)).filter (fun i => i.val % q = r.val)

theorem finRange_pairwise (n : ℕ) :
    (List.finRange n).Pairwise (fun i j => i.val < j.val) := by
  apply List.pairwise_iff_get.mpr
  intro i j hij
  simpa [List.get_finRange] using hij

variable {V : Type*} [Fintype V]

noncomputable def gridScaleData (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (δ : ℝ) (hδ₀ : 0 ≤ δ)
    (hδ : 64 * δ ≤ 1) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (δ * g.scale i))
    (i : Fin (g.intervals + 1)) : ScaleData I where
  a := g.scale i
  rho := δ * g.scale i
  retained := N i
  positive := g.positive i
  rho_nonneg := mul_nonneg hδ₀ (g.positive i).le
  rho_small := by nlinarith [mul_le_mul_of_nonneg_right hδ (g.positive i).le]
  subset := hN i
  cover := hc i

omit [Fintype V] in
theorem residue_separated (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (δ : ℝ) (hδ₀ : 0 ≤ δ)
    (hδ : 64 * δ ≤ 1) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (δ * g.scale i))
    (q : ℕ) (hsep : (5 / 4 : ℝ) * Structural.omega ^ (-(q : ℤ)) < 1 - 2 * δ)
    (r : Fin q) :
    ((residueIndices g q r).map (gridScaleData I g N δ hδ₀ hδ hN hc)).Pairwise Separated := by
  rw [List.pairwise_map]
  have ho : (residueIndices g q r).Pairwise (fun i j => i.val < j.val) :=
    (finRange_pairwise _).filter _
  apply List.Pairwise.imp_of_mem (p := ho)
  intro i j hi hj hij
  have himod : i.val % q = r.val := by
    simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hi).2
  have hjmod : j.val % q = r.val := by
    simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hj).2
  have hg := residue_gap i.val j.val q hij (himod.trans hjmod.symm)
  exact grid_scale_separated g δ hδ q hsep i j hg

theorem grid_soundness (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (δ : ℝ) (hδ₀ : 0 ≤ δ)
    (hδ : 64 * δ ≤ 1) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (δ * g.scale i))
    (q : ℕ) (hq : 0 < q)
    (hsep : (5 / 4 : ℝ) * Structural.omega ^ (-(q : ℤ)) < 1 - 2 * δ) :
    (∑ i, g.scale i * retainedSaving I (N i) (g.scale i)) ≤
      32 * (q : ℝ) * (I.mst - I.optimum) := by
  classical
  let w := fun i : Fin (g.intervals + 1) => g.scale i * retainedSaving I (N i) (g.scale i)
  have hclass (r : Fin q) :
      ∑ i ∈ (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % q = r.val)), w i ≤
        32 * (I.mst - I.optimum) := by
    have hh := separated_sound I
      ((residueIndices g q r).map (gridScaleData I g N δ hδ₀ hδ hN hc))
      (residue_separated I g N δ hδ₀ hδ hN hc q hsep r)
    have hn : (residueIndices g q r).Nodup := (List.nodup_finRange _).filter _
    have he : (residueIndices g q r).toFinset =
        Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % q = r.val) := by
      ext i
      simp [residueIndices]
    have hh' : ((residueIndices g q r).map w).sum ≤ 32 * (I.mst - I.optimum) := by
      simpa only [List.map_map, Function.comp_def, gridScaleData, w] using hh
    rw [← List.sum_toFinset w hn, he] at hh'
    exact hh'
  let residue : Fin (g.intervals + 1) → Fin q := fun i => ⟨i.val % q, Nat.mod_lt _ hq⟩
  have hsplit :
      (∑ r : Fin q, ∑ i ∈
        (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % q = r.val)), w i) =
        ∑ i, w i := by
    simpa only [Fin.ext_iff, residue] using
      (Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin (g.intervals + 1))))
        (t := (Finset.univ : Finset (Fin q))) (g := residue)
        (fun i _ => Finset.mem_univ (residue i)) w)
  change (∑ i, w i) ≤ _
  calc
    _ = ∑ r : Fin q, ∑ i ∈
        (Finset.univ.filter (fun i : Fin (g.intervals + 1) => i.val % q = r.val)), w i :=
      hsplit.symm
    _ ≤ ∑ _r : Fin q, 32 * (I.mst - I.optimum) :=
      Finset.sum_le_sum (fun r _ => hclass r)
    _ = _ := by simp; ring

noncomputable abbrev delta : ℝ := 1 / 10000000000

theorem retained_saving_sound (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (delta * g.scale i))
    (Qs : ℕ) (hQs : 0 < Qs)
    (hsep : (5 / 4 : ℝ) * Structural.omega ^ (-(Qs : ℤ)) < 1 - 2 * delta) :
    (∑ i, g.scale i * savingOn I (N i) (g.scale i) (5 * g.scale i / 8)) ≤
      32 * (Qs : ℝ) * (I.mst - I.optimum) :=
  grid_soundness I g N delta (by norm_num [delta]) (by norm_num [delta]) hN hc Qs hQs hsep

theorem separation_32 :
    (5 / 4 : ℝ) * Structural.omega ^ (-(32 : ℤ)) < 1 - 2 * delta := by
  norm_num [Structural.omega, delta]

theorem retained_saving_sound_32 (I : Instance V) (g : Structural.Grid)
    (N : Fin (g.intervals + 1) → Finset V) (hN : ∀ i, N i ⊆ I.terminals)
    (hc : ∀ i, CoverOn I I.terminals (N i) (delta * g.scale i)) :
    (∑ i, g.scale i * savingOn I (N i) (g.scale i) (5 * g.scale i / 8)) ≤
      1024 * (I.mst - I.optimum) := by
  simpa only [Nat.cast_ofNat, show (32 : ℝ) * 32 = 1024 by norm_num] using
    retained_saving_sound I g N hN hc 32 (by omega) separation_32

end SteinerUpperBound.SavingSoundness

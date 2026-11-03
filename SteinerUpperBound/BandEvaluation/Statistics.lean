module

public import SteinerUpperBound.BandEvaluation.Mean
public import SteinerUpperBound.EstimationAlgebra

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

noncomputable def estimate (a gminus empirical xi : ℝ) : ℝ :=
  3 * a * Estimation.lowerCount gminus empirical xi

noncomputable def estimateCode {M Q : Type*} (a gminus empirical xi : ℝ) : Code M Q ℝ :=
  .tick 7 (.pure (estimate a gminus empirical xi))

theorem estimateCode_evaluates {M Q : Type*} (m : M → ℝ) (b : Q → Bool)
    (a gminus empirical xi : ℝ) :
    Code.Evaluates m b (estimateCode a gminus empirical xi)
      ((Outcome.pure (estimate a gminus empirical xi)).add 8 0 0 0) :=
  Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 7

variable {V : Type*} [Fintype V]

noncomputable def trueMean (I : Instance V) (N : Finset V) (hN : N.Nonempty)
    (a rho tau : ℝ) (B : ℕ) : ℝ :=
  (uniformPoints N hN).expect (fun x => pointScore I N a rho tau B x.val)

theorem trueMean_bounds (I : Instance V) (N : Finset V) (hN : N.Nonempty)
    (a rho tau : ℝ) (B : ℕ) (ha : 0 < a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) :
    0 ≤ trueMean I N hN a rho tau B ∧ trueMean I N hN a rho tau B ≤ 1 :=
  ScoreSampling.mean_bounds (uniformPoints N hN) (fun x => pointScore I N a rho tau B x.val)
    (fun x => (pointScore_bounds I N a rho tau B ha hrho htau hband x.val).1)
    (fun x => (pointScore_bounds I N a rho tau B ha hrho htau hband x.val).2)

theorem trueMean_count (I : Instance V) (N : Finset V) (hN : N.Nonempty)
    (a rho tau : ℝ) (B : ℕ) (ha : 0 < a) :
    3 * a * ((N.card : ℝ) * trueMean I N hN a rho tau B) = smallBandSum I N a rho tau B := by
  have hg : (0 : ℝ) < N.card := by exact_mod_cast Finset.card_pos.mpr hN
  have hm := uniform_component_mean I N hN a rho tau B
  change trueMean I N hN a rho tau B = _ at hm
  have hh := (eq_div_iff (by positivity : 3 * a * (N.card : ℝ) ≠ 0)).mp hm
  nlinarith

theorem estimate_bounds (I : Instance V) (N : Finset V) (hN : N.Nonempty)
    (a rho tau : ℝ) (B : ℕ) (ha : 0 < a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho) (gminus empirical xi : ℝ)
    (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hcal : (1 - xi) * (N.card : ℝ) ≤ gminus) (hcal1 : gminus ≤ N.card)
    (he : |empirical - trueMean I N hN a rho tau B| ≤ xi) :
    0 ≤ estimate a gminus empirical xi ∧ estimate a gminus empirical xi ≤ smallBandSum I N a rho tau B ∧
      smallBandSum I N a rho tau B - estimate a gminus empirical xi ≤ 9 * xi * a * N.card := by
  have hm := trueMean_bounds I N hN a rho tau B ha hrho htau hband
  have hc := Estimation.lowerCount_bounds (N.card : ℝ) gminus
    (trueMean I N hN a rho tau B) empirical xi (Nat.cast_nonneg _) hxi hxi1 hm.1 hm.2 hcal hcal1 he
  have heq := trueMean_count I N hN a rho tau B ha
  have hpos : 0 ≤ 3 * a := by positivity
  have hu := mul_le_mul_of_nonneg_left hc.2.1 hpos
  have hl := mul_le_mul_of_nonneg_left hc.2.2 hpos
  refine ⟨mul_nonneg hpos hc.1, ?_, ?_⟩ <;> unfold estimate <;> nlinarith

variable {ι : Type*} [Fintype ι]

noncomputable def aggregateTarget (I : Instance V) (N : ι → Finset V)
    (a rho tau : ι → ℝ) (B : ℕ) : ℝ := ∑ i, smallBandSum I (N i) (a i) (rho i) (tau i) B

noncomputable def aggregateEstimate (a gminus empirical : ι → ℝ) (xi : ℝ) : ℝ :=
  ∑ i, estimate (a i) (gminus i) (empirical i) xi

theorem aggregate_bounds (I : Instance V) (N : ι → Finset V) (hN : ∀ i, (N i).Nonempty)
    (a rho tau : ι → ℝ) (B : ℕ) (ha : ∀ i, 0 < a i)
    (hrho : ∀ i, 0 ≤ rho i) (htau : ∀ i, 0 ≤ tau i)
    (hband : ∀ i, tau i * a i ≤ a i - 2 * rho i)
    (gminus empirical : ι → ℝ) (xi : ℝ) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hcal : ∀ i, (1 - xi) * ((N i).card : ℝ) ≤ gminus i)
    (hcal1 : ∀ i, gminus i ≤ (N i).card)
    (he : ∀ i, |empirical i - trueMean I (N i) (hN i) (a i) (rho i) (tau i) B| ≤ xi)
    (A L : ℝ) (hA : 0 < A) (hL : 0 ≤ L)
    (hmass : (∑ i, a i * (N i).card) ≤ A * L)
    (haccuracy : xi ≤ Structural.sigma0 / (100000 * A)) :
    0 ≤ aggregateEstimate a gminus empirical xi ∧
      aggregateEstimate a gminus empirical xi ≤ aggregateTarget I N a rho tau B ∧
      aggregateTarget I N a rho tau B - aggregateEstimate a gminus empirical xi ≤
        Structural.sigma0 * L / 1000 := by
  have hi (i : ι) := estimate_bounds I (N i) (hN i) (a i) (rho i) (tau i) B
    (ha i) (hrho i) (htau i) (hband i) (gminus i) (empirical i) xi hxi hxi1 (hcal i) (hcal1 i) (he i)
  have hn : 0 ≤ aggregateEstimate a gminus empirical xi :=
    Finset.sum_nonneg (fun i _ => (hi i).1)
  have hu : aggregateEstimate a gminus empirical xi ≤ aggregateTarget I N a rho tau B :=
    Finset.sum_le_sum (fun i _ => (hi i).2.1)
  have hl : aggregateTarget I N a rho tau B - aggregateEstimate a gminus empirical xi ≤
      9 * xi * (∑ i, a i * (N i).card) := by
    calc
      _ = ∑ i, (smallBandSum I (N i) (a i) (rho i) (tau i) B -
          estimate (a i) (gminus i) (empirical i) xi) := by
        rw [Finset.sum_sub_distrib]
        rfl
      _ ≤ ∑ i, 9 * xi * a i * (N i).card := Finset.sum_le_sum (fun i _ => (hi i).2.2)
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 9 * xi by positivity)
  have hacc := (le_div_iff₀ (by positivity : 0 < 100000 * A)).mp haccuracy
  have haccL := mul_le_mul_of_nonneg_right hacc hL
  have hsL : 0 ≤ Structural.sigma0 * L := mul_nonneg (by norm_num [Structural.sigma0]) hL
  refine ⟨hn, hu, ?_⟩
  calc
    _ ≤ 9 * xi * (∑ i, a i * (N i).card) := hl
    _ ≤ 9 * xi * (A * L) := hm
    _ = (9 / 100000 : ℝ) * (xi * (100000 * A) * L) := by ring
    _ ≤ (9 / 100000 : ℝ) * (Structural.sigma0 * L) :=
      mul_le_mul_of_nonneg_left haccL (by norm_num)
    _ ≤ (1 / 1000 : ℝ) * (Structural.sigma0 * L) :=
      mul_le_mul_of_nonneg_right (by norm_num) hsL
    _ = _ := by ring

end SteinerUpperBound.BandEvaluation

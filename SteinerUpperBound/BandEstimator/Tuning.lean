module

public import SteinerUpperBound.EstimatorParameters.Configuration
public import SteinerUpperBound.Covers.OracleProgramMean

@[expose] public section

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

structure Data where
  cutoff : ℕ
  inverse : ℕ
  samples : ℕ
  rowCap : ℕ
  totalCap : ℕ

def ofParameters (p : EstimatorParameters.PublicParameters) (terminalCount : ℕ) : Data :=
  ⟨p.bandCutoff, p.bandAccuracyDenominator, p.bandSamples, p.bandProposalCap,
    16 * terminalCount * (p.bandSamples + p.confidenceDenominator)⟩

def publicData (n terminalCount : ℕ) : Data :=
  ⟨EstimatorParameters.BQ n, EstimatorParameters.xiBandInv n,
    EstimatorParameters.meanSamples n (EstimatorParameters.xiBandInv n),
    EstimatorParameters.samplerCap n terminalCount (EstimatorParameters.xiBandInv n),
    16 * terminalCount * (EstimatorParameters.meanSamples n (EstimatorParameters.xiBandInv n) +
      EstimatorParameters.betaDenom n)⟩

theorem ofParameters_eq (n terminalCount : ℕ) :
    ofParameters (EstimatorParameters.parameters n terminalCount) terminalCount =
      publicData n terminalCount := rfl

noncomputable def accuracy (d : Data) : ℝ := 1 / (d.inverse : ℝ)

theorem accuracy_eq (n terminalCount : ℕ) :
    accuracy (publicData n terminalCount) = EstimatorParameters.xiBand n := by
  simp only [accuracy, publicData, EstimatorParameters.xiBand, EstimatorParameters.xiBandQ,
    Rat.cast_div, Rat.cast_one, Rat.cast_natCast]

theorem accuracy_bounds (n terminalCount : ℕ) :
    0 < accuracy (publicData n terminalCount) ∧ accuracy (publicData n terminalCount) ≤ 1 := by
  rw [accuracy_eq]
  exact ⟨(EstimatorParameters.score_ranges n).2.2.2.2.1,
    (EstimatorParameters.score_ranges n).2.2.2.2.2.1⟩

theorem samples_positive (n terminalCount : ℕ) : 0 < (publicData n terminalCount).samples :=
  EstimatorParameters.meanSamples_positive n _ (EstimatorParameters.integer_budget_pos n).2.2.2.2.1

theorem samples_budget (n terminalCount : ℕ) :
    EstimatorParameters.beta n *
      (((publicData n terminalCount).samples : ℝ) * accuracy (publicData n terminalCount) ^ 2) = 256 :=
  EstimatorParameters.meanSamples_exact n _ (EstimatorParameters.integer_budget_pos n).2.2.2.2.1

theorem accuracy_mass_budget (n terminalCount : ℕ) :
    accuracy (publicData n terminalCount) =
      Structural.sigma0 / (100000 * (EstimatorParameters.A n : ℝ)) := by
  rw [accuracy_eq]
  exact (EstimatorParameters.score_scalar_equations n).2.2.1

variable {U : Type*} [Fintype U] [Nonempty U]

theorem survival_public (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty) (n : ℕ) :
    (1 - Covers.Rejection.hitRate b) ^ (publicData n (Fintype.card U)).rowCap ≤
      EstimatorParameters.beta n * accuracy (publicData n (Fintype.card U)) /
        (16 * (publicData n (Fintype.card U)).samples) := by
  rw [← Covers.Rejection.first_failure b hb]
  exact (Covers.Rejection.first_failure_exp b hb _).trans
    (EstimatorParameters.samplerCap_test n (Fintype.card U) _
      Fintype.card_pos (EstimatorParameters.integer_budget_pos n).2.2.2.2.1)

theorem proposals_public (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty) (n : ℕ) :
    (Covers.Rejection.poolLaw (publicData n (Fintype.card U)).rowCap
      (publicData n (Fintype.card U)).samples).prob
        {rows | (publicData n (Fintype.card U)).totalCap <
          Covers.Rejection.proposals b (publicData n (Fintype.card U)).rowCap
            (publicData n (Fintype.card U)).samples rows} ≤ EstimatorParameters.beta n / 2 := by
  let d := publicData n (Fintype.card U)
  let D := EstimatorParameters.betaDenom n
  have hD : (0 : ℝ) < D := by exact_mod_cast EstimatorParameters.betaDenom_pos n
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hcap : (d.totalCap : ℝ) / (4 * Fintype.card U) =
      4 * ((d.samples : ℝ) + D) := by
    dsimp only [d, D, publicData]
    push_cast
    field_simp
    ring
  apply (Covers.Rejection.proposals_tail b hb d.rowCap d.samples d.totalCap).trans
  rw [hcap]
  have he : Real.exp ((d.samples : ℝ) - 4 * ((d.samples : ℝ) + D)) ≤
      Real.exp (-(2 * (D : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hs : (0 : ℝ) ≤ d.samples := Nat.cast_nonneg _
    nlinarith
  have hi : Real.exp (-(2 * (D : ℝ))) ≤ (2 * (D : ℝ))⁻¹ := by
    rw [Real.exp_neg]
    apply inv_anti₀ (by positivity)
    linarith [Real.add_one_le_exp (2 * (D : ℝ))]
  apply (he.trans hi).trans_eq
  rw [EstimatorParameters.beta_eq]
  dsimp only [D]
  ring

theorem sampling_public (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty) (n : ℕ) :
    let d := publicData n (Fintype.card U)
    let β := EstimatorParameters.beta n
    (Covers.Rejection.poolLaw d.rowCap d.samples).prob
        {rows | ¬ Covers.Rejection.Successful b d.rowCap d.samples rows} ≤ β / 16 ∧
      (Covers.Rejection.poolLaw d.rowCap d.samples).prob
        {rows | ¬ Covers.Rejection.Calibrated b d.rowCap d.samples (accuracy d) rows} ≤ β / 2 := by
  dsimp only
  let d := publicData n (Fintype.card U)
  let β := EstimatorParameters.beta n
  let ξ := accuracy d
  have hβ : 0 < β := (EstimatorParameters.beta_bounds n).1
  have hβ1 : β ≤ 1 := (EstimatorParameters.beta_bounds n).2.1.trans (by norm_num)
  have hξ := accuracy_bounds n (Fintype.card U)
  have hξ₀ : 0 < ξ := hξ.1
  have hs : (1 : ℝ) ≤ d.samples := by exact_mod_cast samples_positive n (Fintype.card U)
  have hq := survival_public b hb n
  have hqscaled :
      (1 - Covers.Rejection.hitRate b) ^ d.rowCap * (16 * (d.samples : ℝ)) ≤ β * ξ :=
    (le_div_iff₀ (by positivity)).mp hq
  have hq₀ : 0 ≤ (1 - Covers.Rejection.hitRate b) ^ d.rowCap :=
    pow_nonneg (sub_nonneg.mpr (Covers.Rejection.hitRate_le_one b)) _
  have hqsmall : (1 - Covers.Rejection.hitRate b) ^ d.rowCap ≤ ξ / 8 := by
    have hβξ := mul_le_mul_of_nonneg_right hβ1 hξ.1.le
    nlinarith
  have hfailure := Covers.Rejection.pool_failure_le b hb d.rowCap d.samples
  have hξβ := mul_le_mul_of_nonneg_left hξ.2 hβ.le
  have hbudget := samples_budget n (Fintype.card U)
  have hcheb : 8 / ((ξ / 4) ^ 2 * (d.samples : ℝ)) ≤ β / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    change β * ((d.samples : ℝ) * ξ ^ 2) = 256 at hbudget
    nlinarith
  exact ⟨hfailure.trans (by nlinarith),
    (Covers.Rejection.calibration_failure b hb d.rowCap d.samples
      (samples_positive n _) ξ hξ.1 hξ.2 hqsmall).trans hcheb⟩

theorem capError_public (b : U → Bool) (hb : (Covers.Rejection.retained b).Nonempty) (n : ℕ) :
    let d := publicData n (Fintype.card U)
    Mean.capError b d.rowCap d.samples d.totalCap ≤ (9 / 16 : ℝ) * EstimatorParameters.beta n := by
  dsimp only [Mean.capError]
  have hp := proposals_public b hb n
  have hs := (sampling_public b hb n).1
  linarith

end SteinerUpperBound.BandEstimator

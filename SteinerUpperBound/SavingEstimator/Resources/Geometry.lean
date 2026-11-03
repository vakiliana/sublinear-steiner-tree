module

public import SteinerUpperBound.SavingEstimator.Resources.Point
public import SteinerUpperBound.SavingEstimator.RankBudget
public import SteinerUpperBound.SavingEstimator.Tuning
public import SteinerUpperBound.SavingEstimator.Work
public import SteinerUpperBound.LargeCoverProgram.PoolResidual

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram EstimatorParameters
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical BigOperators

variable {n k : ℕ} {Q : Type}

theorem terminal_count_le (terminals : Vector (Fin n) (k + 1)) (hnd : terminals.toList.Nodup) :
    k + 1 ≤ n := by
  have hh := Finset.card_le_univ terminals.toList.toFinset
  rw [List.toFinset_card_of_nodup hnd, Vector.length_toList, Fintype.card_fin] at hh
  exact hh

theorem retained_count_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    (Covers.Rejection.retained (fun u => bits (cfg.key (cfg.terminals.get u)))).card =
      (PortGraph.retained I bits cfg).card :=
  (LargeCoverProgram.retainedIndex_count bits cfg).symm.trans
    (LargeCoverProgram.retainedIndex_card I bits cfg hT hnd)

theorem retained_le_count (bits : Q → Bool) (query : Fin (k + 1) → Q) :
    (Covers.Rejection.retained (fun u => bits (query u))).card ≤ k + 1 := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ (Covers.Rejection.retained fun u => bits (query u))

theorem calibrated_incidence (n count g : ℕ) (gm gp : ℚ) (hg : 0 < g) (hgn : g ≤ n)
    (hcal : (1 - xiSaving n) * g ≤ (gm : ℝ))
    (hupper : (gp : ℝ) ≤ (1 + xiSaving n) * g)
    (hbranch : 100 * (t n : ℚ) / epsQ n < gp) :
    50 * (t n : ℝ) / eps n < g ∧
      LargeCoverProgram.rowCapacity n (closed n count) gm = incidenceBudget n gm ∧
      LargeCoverProgram.rowCapacity n (closed n count) gm ^ 2 ≤ 50 * (n + 1) ∧
      (LargeCoverProgram.rowCapacity n (closed n count) gm : ℝ) ≤ 4 * n / t n + 1 ∧
      (LargeCoverProgram.rowCapacity n (closed n count) gm : ℝ) ≤
        100 * n / (eps n * (gm : ℝ)) + 1 := by
  have hn : 0 < n := lt_of_lt_of_le hg hgn
  have hxi : xiSaving n ≤ (1 : ℝ) / 100 := by
    rw [(score_scalar_equations n).2.1]
    have hh := (score_ranges n).2.1
    linarith
  have hnum := LargeCoverProgram.calibrated_large_budget n g (closed n count) gm gp
    hn hg (t_pos n) (score_ranges n).1 hxi hcal hupper hbranch
  have hhalf : (g : ℝ) / 2 ≤ (gm : ℝ) := by
    have hm := mul_nonneg (show 0 ≤ (1 / 2 : ℝ) - xiSaving n by linarith) (Nat.cast_nonneg g)
    nlinarith
  have hi := incidenceBudget_large_real n g gm hgn hnum.1 hhalf
  have hrow : LargeCoverProgram.rowCapacity n (closed n count) gm = incidenceBudget n gm := by
    calc
      _ = SavingScores.incidenceBudget n (eps n) gm := hnum.2.2.1
      _ = _ := by rw [hi.2.1]; rfl
  have hceil : (incidenceBudget n gm : ℝ) ≤ 100 * n / (eps n * (gm : ℝ)) + 1 := by
    rw [hi.2.1]
    exact (Nat.ceil_lt_add_one (by positivity [(score_ranges n).1, hnum.2.1])).le
  exact ⟨hnum.1, hrow, by rw [hrow]; exact hi.2.2.2, by rw [hrow]; exact hi.2.2.1,
    by rw [hrow]; exact hceil⟩

theorem calibrated_accessFacts (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (gm gp : ℚ)
    (hcal : (1 - xiSaving n) *
      (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).card ≤ (gm : ℝ))
    (hupper : (gp : ℝ) ≤ (1 + xiSaving n) *
      (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).card)
    (hbranch : 100 * (t n : ℚ) / epsQ n < gp)
    (selected : LargeCoverProgram.Selection (Fin n))
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value)
    (hpool : LargeCoverProgram.PoolGood I.weight bits (closed n (k + 1)) cfg.terminals cfg.key cfg.scale
      (some (selected, cfg.covered))) :
    AccessFacts (b := LargeCoverProgram.rowCapacity n (closed n (k + 1)) gm) (B := B n)
      I bits cfg (t n) (eps n) (xiSaving n) gm := by
  have hcount := retained_count_eq I bits cfg hT hnd
  have hg : 0 < (PortGraph.retained I bits cfg).card := by rw [← hcount]; exact Finset.card_pos.mpr hb
  have hgn : (PortGraph.retained I bits cfg).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (PortGraph.retained I bits cfg)
  have hcal' : (1 - xiSaving n) * (PortGraph.retained I bits cfg).card ≤ (gm : ℝ) := by
    rwa [← hcount]
  have hupper' : (gp : ℝ) ≤ (1 + xiSaving n) * (PortGraph.retained I bits cfg).card := by
    rwa [← hcount]
  have hi := calibrated_incidence n (k + 1) _ gm gp hg hgn hcal' hupper' hbranch
  refine ⟨hT, hnd, by exact_mod_cast t_pos n, (score_ranges n).1, (score_ranges n).2.1.trans (by norm_num),
    ?_, hg, hcal', hi.2.2.2.2, ?_, terminal_count_le cfg.terminals hnd, hi.2.2.1, hi.2.2.2.1, ?_⟩
  · rw [(score_scalar_equations n).2.1]
    have hh := (score_ranges n).2.1
    linarith
  · exact (integer_budget_equations n).1.ge
  · simpa only [closed] using
      LargeCoverProgram.poolGood_residual I bits (closed n (k + 1)) cfg hT hnd selected hD hpool

/-- The calibrated large branch makes the true ambient/terminal universe
large enough that the cubic original-counter exception survives all mean calls. -/
theorem large_rank_error_cube (n count g : ℕ) (hgn : g ≤ n) (hgk : g ≤ count)
    (hlarge : 50 * (t n : ℝ) / eps n < g) :
    (meanSamples n (xiSavingInv n) : ℝ) /
      (publicSize n count 1 (B n) : ℝ) ^ 3 ≤ beta n := by
  have ht : (0 : ℝ) < t n := by exact_mod_cast t_pos n
  have hB : (0 : ℝ) < B n := by exact_mod_cast (integer_budget_pos n).2.1
  have hbranch : 5 * (B n : ℝ) * t n < g := by
    rw [(integer_budget_equations n).1]
    convert hlarge using 1 <;> ring
  have hgnR : (g : ℝ) ≤ n := by exact_mod_cast hgn
  have hnt : (n : ℝ) < (t n : ℝ) ^ 2 := by exact_mod_cast n_lt_t_sq n
  have htB : 5 * (B n : ℝ) < t n := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt h) ht.le
    nlinarith
  have hgB : (B n : ℝ) ^ 2 ≤ g := by
    have hm := mul_le_mul_of_nonneg_left htB.le (show 0 ≤ 5 * (B n : ℝ) by positivity)
    nlinarith
  have hbgn : B n ^ 2 ≤ n := by exact_mod_cast hgB.trans hgnR
  have hbgk : B n ^ 2 ≤ count := by exact_mod_cast hgB.trans (show (g : ℝ) ≤ count by exact_mod_cast hgk)
  have hsize : B n ^ 5 ≤ publicSize n count 1 (B n) := by
    have hm := Nat.mul_le_mul_right (B n) (Nat.mul_le_mul hbgn hbgk)
    unfold publicSize
    simp only [Nat.one_mul]
    nlinarith
  have hB8 : 8 ≤ B n := by
    have hh := Nat.mul_le_mul_left 10 (Nat.succ_le_of_lt (integer_budget_pos n).1)
    exact (by decide : 8 ≤ 10).trans (by simpa only [B, Nat.mul_one] using hh)
  have hnum : 25600 ≤ B n ^ 7 :=
    (by norm_num : (25600 : ℕ) ≤ 8 ^ 7).trans (Nat.pow_le_pow_left hB8 7)
  have hsmall : betaDenom n * meanSamples n (xiSavingInv n) ≤ 25600 * B n ^ 8 := by
    have hm := Nat.mul_le_mul (betaDenom_le_cube n) (samples_power_bound n)
    convert hm using 1 <;> ring
  have hp : betaDenom n * meanSamples n (xiSavingInv n) ≤ publicSize n count 1 (B n) ^ 3 := by
    calc
      _ ≤ 25600 * B n ^ 8 := hsmall
      _ ≤ B n ^ 7 * B n ^ 8 := Nat.mul_le_mul_right _ hnum
      _ = (B n ^ 5) ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_left hsize 3
  have hN : (0 : ℝ) < publicSize n count 1 (B n) := by unfold publicSize; positivity
  have hD : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  rw [beta_eq]
  apply (div_le_div_iff₀ (pow_pos hN 3) hD).mpr
  simp only [one_mul]
  exact_mod_cast (show meanSamples n (xiSavingInv n) * betaDenom n ≤
    publicSize n count 1 (B n) ^ 3 by simpa only [Nat.mul_comm] using hp)

end SteinerUpperBound.SavingEstimator.Resources

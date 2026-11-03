module

public import SteinerUpperBound.SavingEstimator.Program
public import SteinerUpperBound.SavingEstimator.RankBudget
public import SteinerUpperBound.SavingEstimator.Tuning

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator

open SteinerLowerBound EstimatorParameters QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

noncomputable def saving (I : Instance (Fin n)) (bits : Q → Bool) (key : Fin n → Q) (a : ℝ) : ℝ :=
  Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8)

noncomputable def retainedCount (bits : Q → Bool) (terminals : Vector (Fin n) (k + 1))
    (key : Fin n → Q) : ℕ :=
  (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card

theorem fromParameters_bad_saving (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hroot : bits (key (terminals.get root)) = true) :
    Code.valueProbability I.weight bits
      (fromParameters terminals root key a (parameters n (k + 1)) c)
      (fun r => ¬ LargeCoverProgram.GoodSaving (saving I bits key a)
        (retainedCount bits terminals key) (eps n) r.value) ≤ 4 * beta n := by
  have hb : (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).Nonempty :=
    ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hroot⟩⟩
  have hn : 1 ≤ n := by have h := (terminals.get root).isLt; omega
  have heps : 0 < eps n := (score_ranges n).1
  have heps1 : eps n ≤ 1 := (score_ranges n).2.1.trans (by norm_num)
  have hxi : 0 < xiSaving n := (score_ranges n).2.2.1
  have hxi' : xiSaving n ≤ eps n / 100 := (score_scalar_equations n).2.1.le
  have hB : SavingScores.smallThreshold (eps n) ≤ B n := by
    simpa only [SavingScores.smallThreshold] using (actual_ceiling_budgets n).1.ge
  have hbudget : 1 ≤ beta n * ((meanSamples n (xiSavingInv n) : ℝ) * xiSaving n ^ 2) := by
    rw [mean_sample_budget]
    norm_num
  have hcalExp : Real.exp (-(samplerCap n (k + 1) (xiSavingInv n) : ℝ) / ((k : ℝ) + 1)) ≤ xiSaving n / 8 := by
    simpa only [Nat.cast_add, Nat.cast_one] using calibration_exp_small n (k + 1) (Nat.succ_pos _)
  have h := LargeCoverProgram.program_concrete_saving_confidence I bits (closed n (k + 1))
    terminals root key a hT hnd c hc hb heps heps1 hxi hxi' hB
    (beta n) (beta n) (t_pos n) (beta_bounds n).1 (beta_bounds n).2.2
    (reusable_budgets n).1 (reusable_budgets n).2 (mean_sample_positive n) hbudget
    (mean_sample_positive n) le_rfl hcalExp
  have hcal := calibration_error n (k + 1) (Nat.succ_pos _)
  push_cast at hcal
  have hpool := pool_cap_error (fun u => bits (key (terminals.get u))) hb n (k + 1)
    (Nat.succ_pos _) (Fintype.card_fin _)
  have hmean := mean_cap_error (fun u => bits (key (terminals.get u))) hb n (k + 1)
    (Nat.succ_pos _) (Fintype.card_fin _)
  have hrank := concrete_rank_error n (k + 1) hn (Nat.succ_le_succ (Nat.zero_le _))
  rw [fromParameters_valueProbability, configuration_public]
  change Code.valueProbability I.weight bits
    (LargeCoverProgram.program (closed n (k + 1)) terminals root key a
      (PortGraph.RuntimeAdapter.builder key a terminals (closed n (k + 1)).cutoff) c)
    (fun r => ¬ LargeCoverProgram.GoodSaving
      (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (eps n) r.value) ≤ _
  apply h.trans
  change
    ((meanSamples n (xiSavingInv n) : ℝ) *
      Real.exp (-(samplerCap n (k + 1) (xiSavingInv n) : ℝ) / (k + 1)) +
      8 / (((xiSaving n : ℝ) / 4) ^ 2 * meanSamples n (xiSavingInv n))) +
    (Mean.capError (fun u => bits (key (terminals.get u))) ((k + 1) * poolClock n) (NsPool n)
        (NsPool n * ((k + 1) * poolClock n)) + beta n +
      (Mean.capError (fun u => bits (key (terminals.get u))) (samplerCap n (k + 1) (xiSavingInv n))
          (meanSamples n (xiSavingInv n))
          (meanSamples n (xiSavingInv n) * samplerCap n (k + 1) (xiSavingInv n)) +
        meanSamples n (xiSavingInv n) * LargeCoverProgram.concreteVOError n (k + 1) (B n) + beta n)) ≤ _
  have hbeta := (beta_bounds n).1
  linarith

private theorem complement_probability {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop) :
    Code.valueProbability m bits p P + Code.valueProbability m bits p (fun r => ¬ P r) = 1 := by
  unfold Code.valueProbability
  rw [← Code.evaluate_add]
  calc
    _ = p.evaluate m bits (fun _ => 1) := by
      apply congrArg (p.evaluate m bits)
      funext o
      by_cases hp : P o.value <;> simp [hp]
    _ = 1 := Code.evaluate_const _ _ _ _

theorem fromParameters_saving_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hroot : bits (key (terminals.get root)) = true) :
    1 - 4 * beta n ≤ Code.valueProbability I.weight bits
      (fromParameters terminals root key a (parameters n (k + 1)) c)
      (fun r => LargeCoverProgram.GoodSaving (saving I bits key a)
        (retainedCount bits terminals key) (eps n) r.value) := by
  have h := fromParameters_bad_saving I bits terminals root key a hT hnd c hc hroot
  have he := complement_probability I.weight bits
    (fromParameters terminals root key a (parameters n (k + 1)) c)
    (fun r => LargeCoverProgram.GoodSaving (saving I bits key a)
      (retainedCount bits terminals key) (eps n) r.value)
  linarith

end SteinerUpperBound.SavingEstimator

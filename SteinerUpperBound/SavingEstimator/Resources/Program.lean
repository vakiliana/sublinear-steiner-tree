module

public import SteinerUpperBound.SavingEstimator.Resources.Budgets
public import SteinerUpperBound.SavingEstimator.Resources.Composition
public import SteinerUpperBound.LargeCoverProgram.SmallResources

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram EstimatorParameters
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical

variable {n k : ℕ} {Q : Type}

theorem afterCovered_clipped (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (gm gp : ℚ) (selected : LargeCoverProgram.Selection (Fin n)) (cache : Cache Q)
    (hc : Cache.Correct bits cache) (D : Vector Bool n)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (hcal : (1 - xiSaving n) * (Covers.Rejection.retained fun u => bits (key (terminals.get u))).card ≤ (gm : ℝ))
    (hupper : (gp : ℝ) ≤ (1 + xiSaving n) * (Covers.Rejection.retained fun u => bits (key (terminals.get u))).card)
    (hbranch : 100 * (t n : ℚ) / epsQ n < gp)
    (hD : D = (LocalAccess.coveredResult I.weight (5 * a / 8) selected.centers).value)
    (hpool : LargeCoverProgram.PoolGood I.weight bits (closed n (k + 1)) terminals key a (some (selected, D)))
    (T : ℝ) (hceiling : 0 ≤ T) :
    (LargeCoverProgram.afterCovered (closed n (k + 1)) terminals root key a
      (builder key a terminals (B n)) gm gp selected cache D).evaluate I.weight bits (clipped kind.counter T) ≤
      coveredBase kind n k + 2 * beta n * T := by
  let p := closed n (k + 1)
  let cfg : LocalAccess.SlotConfig Q n (k + 1) := ⟨key, a, terminals, D⟩
  let b := LargeCoverProgram.rowCapacity n p gm
  have facts := calibrated_accessFacts I bits cfg hT hnd hb gm gp hcal hupper hbranch selected hD hpool
  have hk := terminal_count_le terminals hnd
  have hbmax : b ≤ 4 * n + 2 := rowCapacity_le_max n (k + 1) gm
  have hbpos : 1 ≤ b := LargeCoverProgram.rowCapacity_pos n p gm
  have hm := concrete_mean_clipped kind I bits cfg (t n) (eps n) (xiSaving n) gm facts
    root p.meanRowCap p.meanSamples p.meanProposals cache hc hb (p.xi : ℝ) T hceiling
  have hpoint : (pointBase kind n (k + 1) b (B n) : ℝ) ≤ pointPublic kind n := by
    exact_mod_cast pointBase_le kind n (k + 1) b hk facts.square
  have hacc := accessBudget_le kind n (k + 1) b hk hbmax hbpos T hceiling
  have hmean := hm.trans (add_le_add (meanBase_le kind n k)
    (mul_le_mul_of_nonneg_left (add_le_add hpoint hacc) (Nat.cast_nonneg p.meanSamples)))
  have hgk := retained_le_count bits (fun u => key (terminals.get u))
  have hg : 0 < (Covers.Rejection.retained fun u => bits (key (terminals.get u))).card :=
    Finset.card_pos.mpr hb
  have hi := calibrated_incidence n (k + 1) _ gm gp hg (hgk.trans hk) hcal hupper hbranch
  have he := large_rank_error_cube n (k + 1) _ (hgk.trans hk) hgk hi.1
  have hrare : (p.meanSamples : ℝ) * (2 * T / (publicSize n (k + 1) 1 (B n) : ℝ) ^ 3) ≤
      2 * beta n * T := by
    dsimp only [p, closed]
    convert mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * T by positivity) using 1 <;> ring
  have hbody :
      32 * kind.counter.work +
        ((meanBase kind n k : ℝ) + p.meanSamples *
          ((pointPublic kind n : ℝ) + ((lazyFactor n : ℝ) * geometricPublic kind n +
            12 * kind.counter.work + 2 * T / (publicSize n (k + 1) 1 (B n) : ℝ) ^ 3))) ≤
        coveredBase kind n k + 2 * beta n * T := by
    calc
      _ = (coveredBase kind n k : ℝ) +
          p.meanSamples * (2 * T / (publicSize n (k + 1) 1 (B n) : ℝ) ^ 3) := by
        dsimp only [coveredBase, p]
        push_cast
        rw [workUnit_eq]
        ring
      _ ≤ _ := add_le_add (le_refl _) hrare
  have hafter (r : Mean.Result Q k p.meanSamples) :
      (LargeCoverProgram.afterMean p gm gp selected D r).evaluate I.weight bits (clipped kind.counter T) ≤
        kind.counter.work * (15 + 1 : ℕ) := by
    unfold LargeCoverProgram.afterMean
    exact clipped_tick_pure I.weight bits _ 15 kind.counter T hceiling
  let meanCode := Mean.program (fun u => key (terminals.get u)) root p.meanRowCap p.meanSamples
    p.meanProposals cache (p.xi : ℝ) (pointCallback cfg b (B n))
  have hbind := clipped_bind_const I.weight bits meanCode (LargeCoverProgram.afterMean p gm gp selected D)
    kind.counter T hceiling _ hafter
  have hout := clipped_tick I.weight bits (meanCode.bind (LargeCoverProgram.afterMean p gm gp selected D))
    15 kind.counter T
  have hcode := hout.trans (add_le_add (le_refl _) hbind)
  change (LargeCoverProgram.afterCovered p terminals root key a (builder key a terminals (B n))
    gm gp selected cache D).evaluate I.weight bits (clipped kind.counter T) ≤ _ at hcode
  have hcode' := hcode.trans (add_le_add (le_refl _) (add_le_add hmean (le_refl _)))
  norm_num only [Nat.cast_ofNat] at hcode'
  exact hcode'.trans (by convert hbody using 1 <;> ring)

theorem deletion_counter_le (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    (LargeCoverProgram.deletion (closed n (k + 1)) terminals root key a cache).evaluate I.weight bits
      kind.counter.value ≤ deletionBase kind n k := by
  exact counter_expect_of_runs I.weight bits _ kind _ _
    (fun o ho => by
      have hh := LargeCoverProgram.deletion_cache_resources I.weight bits (closed n (k + 1))
        terminals root key a cache hc o ho
      exact ⟨hh.2.1, hh.2.2.2.1⟩)

theorem large_clipped (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (gm gp : ℚ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (hcal : (1 - xiSaving n) * (Covers.Rejection.retained fun u => bits (key (terminals.get u))).card ≤ (gm : ℝ))
    (hupper : (gp : ℝ) ≤ (1 + xiSaving n) * (Covers.Rejection.retained fun u => bits (key (terminals.get u))).card)
    (hbranch : 100 * (t n : ℚ) / epsQ n < gp) (T : ℝ) (hceiling : 0 ≤ T) :
    (LargeCoverProgram.large (closed n (k + 1)) terminals root key a (builder key a terminals (B n))
      gm gp cache).evaluate I.weight bits (clipped kind.counter T) ≤
      largeBase kind n k + (49 / 16 : ℝ) * beta n * T := by
  let p := closed n (k + 1)
  let deleted := LargeCoverProgram.deletion p terminals root key a cache
  let next (r : LargeCoverProgram.Deletion Q n) : Code (Sym2 (Fin n)) Q (LargeCoverProgram.Answer Q n) :=
    .tick 3 (match r.value with
      | none => .pure (LargeCoverProgram.abort r.cache gm gp false)
      | some (selected, D) =>
        LargeCoverProgram.afterCovered p terminals root key a (builder key a terminals (B n))
          gm gp selected r.cache D)
  have hp := LargeCoverProgram.deletion_pool_failure I.weight bits p terminals root key a cache hc hb
    (beta n) (t_pos n) (beta_bounds n).1 (beta_bounds n).2.2 (reusable_budgets n).1 (reusable_budgets n).2
  have hcap := pool_cap_error (fun u => bits (key (terminals.get u))) hb n (k + 1)
    (by omega) (Fintype.card_fin _)
  have hbad : Code.valueProbability I.weight bits deleted
      (fun r => ¬ LargeCoverProgram.PoolGood I.weight bits p terminals key a r.value) ≤
        (17 / 16 : ℝ) * beta n := by
    have hprob : Code.valueProbability I.weight bits deleted
        (fun r => ¬ LargeCoverProgram.PoolGood I.weight bits p terminals key a r.value) ≤
        Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals + beta n := by
      rw [LargeCoverProgram.valueProbability_eq_probability]
      exact hp
    have hh := hprob.trans (add_le_add hcap (le_refl (beta n)))
    exact hh.trans (by ring_nf; exact le_refl _)
  have hk (o : Outcome (LargeCoverProgram.Deletion Q n)) (ho : Runs I.weight bits deleted o)
      (hpool : LargeCoverProgram.PoolGood I.weight bits p terminals key a o.value.value) :
      (next o.value).evaluate I.weight bits (clipped kind.counter T) ≤
        ((4 * workUnit kind + coveredBase kind n k : ℕ) : ℝ) + (2 * beta n) * T := by
    cases hv : o.value.value with
    | none => simp [LargeCoverProgram.PoolGood, hv] at hpool
    | some val =>
      obtain ⟨selected, D⟩ := val
      have hr := LargeCoverProgram.deletion_cache_resources I.weight bits p terminals root key a cache hc o ho
      have hD := LargeCoverProgram.deletion_covered I.weight bits p terminals root key a cache o ho selected D hv
      have hcovered := afterCovered_clipped kind I bits terminals root key a hT hnd gm gp selected
        o.value.cache hr.1 D hb hcal hupper hbranch hD (by rwa [hv] at hpool) T hceiling
      have ht := clipped_tick I.weight bits
        (LargeCoverProgram.afterCovered p terminals root key a (builder key a terminals (B n))
          gm gp selected o.value.cache D) 3 kind.counter T
      have hh := ht.trans (add_le_add (le_refl _) hcovered)
      convert hh using 1 <;>
        simp only [next, hv, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, workUnit_eq] <;> ring
  have hh := clipped_bind_bad I.weight bits deleted next kind.counter T hceiling
    (fun r => LargeCoverProgram.PoolGood I.weight bits p terminals key a r.value)
    (deletionBase kind n k) ((4 * workUnit kind + coveredBase kind n k : ℕ) : ℝ)
    ((17 / 16 : ℝ) * beta n) (2 * beta n)
    (deletion_counter_le kind I bits terminals root key a cache hc) (Nat.cast_nonneg _)
    (by have := (beta_bounds n).1; positivity) hbad hk
  change (LargeCoverProgram.large p terminals root key a (builder key a terminals (B n))
    gm gp cache).evaluate I.weight bits (clipped kind.counter T) ≤ _ at hh
  convert hh using 1 <;> dsimp only [largeBase] <;> push_cast <;> ring

theorem small_clipped (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (gm gp : ℚ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hcal : ((Covers.Rejection.retained fun u => bits (key (terminals.get u))).card : ℝ) ≤ (gp : ℝ))
    (hbranch : gp ≤ 100 * (t n : ℚ) / epsQ n) (T : ℝ) :
    (LargeCoverProgram.small (closed n (k + 1)) terminals key a gm gp cache).evaluate I.weight bits
      (clipped kind.counter T) ≤ smallBase kind n k := by
  let p := closed n (k + 1)
  have hret :
      (ComponentExplore.retained bits key terminals.toList.toFinset).card ≤ LargeCoverProgram.smallLimit p := by
    rw [← LargeCoverProgram.labelCount_eq_points I bits terminals key hT hnd]
    have hq : (gp : ℝ) ≤ ((100 * (t n : ℚ) / epsQ n : ℚ) : ℝ) := by exact_mod_cast hbranch
    have hceil : ((100 * (t n : ℚ) / epsQ n : ℚ) : ℝ) ≤ (LargeCoverProgram.smallLimit p : ℝ) := by
      dsimp only [p, LargeCoverProgram.smallLimit, closed]
      exact_mod_cast (Nat.le_ceil (100 * (t n : ℚ) / epsQ n))
    exact_mod_cast hcal.trans (hq.trans hceil)
  have he := counter_expect_of_runs I.weight bits
    (LargeCoverProgram.small p terminals key a gm gp cache) kind
    (LargeCoverProgram.smallWork n k p) (LargeCoverProgram.smallLimit p)
    (fun o ho => by
      have hh := LargeCoverProgram.small_resources I.weight bits p terminals key a gm gp cache hc hnd o ho
      exact ⟨hh.1, hh.2.trans hret⟩)
  exact (clipped_expect_le_counter I.weight bits _ kind.counter T).trans he

theorem afterCalibration_clipped (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (records : Sampler.Records Q k (closed n (k + 1)).calibrationSamples)
    (hc : Cache.Correct bits records.store.cache)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (hg : Sampler.GoodRecord (fun u => bits (key (terminals.get u)))
      (closed n (k + 1)).calibrationSamples ((closed n (k + 1)).xi : ℝ)
        (Sampler.Observation.ofRecords records)) (T : ℝ) (hceiling : 0 ≤ T) :
    (LargeCoverProgram.afterCalibration (closed n (k + 1)) terminals root key a
      (builder key a terminals (B n)) records).evaluate I.weight bits (clipped kind.counter T) ≤
      ((32 * workUnit kind + smallBase kind n k + largeBase kind n k : ℕ) : ℝ) +
        (49 / 16 : ℝ) * beta n * T := by
  let p := closed n (k + 1)
  have hv := LargeCoverProgram.calibration_values p bits terminals key records hg
  have hlabels : records.labels ≠ none := hg.1
  have hsuccessful : records.successful = true := hg.2.1
  unfold LargeCoverProgram.afterCalibration
  dsimp only
  cases hl : records.labels with
  | none => exact (hlabels hl).elim
  | some labels =>
    simp only [hl, hsuccessful, ite_true]
    split_ifs with hbranch
    · have hs := small_clipped kind I bits terminals key a hT hnd
        (LargeCoverProgram.lowerObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
        (LargeCoverProgram.upperObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
        records.store.cache hc
        hv.2.2.1 hbranch T
      have ht := clipped_tick I.weight bits
        (LargeCoverProgram.small p terminals key a
          (LargeCoverProgram.lowerObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
          (LargeCoverProgram.upperObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
          records.store.cache) 31 kind.counter T
      have hh := ht.trans (add_le_add (le_refl _) hs)
      have hb0 := (beta_bounds n).1
      have hnonneg : 0 ≤ (largeBase kind n k : ℝ) + (49 / 16 : ℝ) * beta n * T := by positivity
      push_cast at hh ⊢
      rw [workUnit_eq]
      linarith
    · have hs := large_clipped kind I bits terminals root key a hT hnd _ _ records.store.cache hc hb
        hv.1 hv.2.2.2 (lt_of_not_ge hbranch) T hceiling
      have ht := clipped_tick I.weight bits
        (LargeCoverProgram.large p terminals root key a (builder key a terminals (B n))
          (LargeCoverProgram.lowerObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
          (LargeCoverProgram.upperObserved (k + 1) p.calibrationSamples records.store.proposals p.xi)
          records.store.cache) 31 kind.counter T
      have hh := ht.trans (add_le_add (le_refl _) hs)
      have hnonneg : (0 : ℝ) ≤ smallBase kind n k := Nat.cast_nonneg _
      push_cast at hh ⊢
      rw [workUnit_eq]
      linarith

theorem frontend_clipped (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (T : ℝ) (hceiling : 0 ≤ T) :
    (LargeCoverProgram.program (closed n (k + 1)) terminals root key a
      (builder key a terminals (B n)) cache).evaluate I.weight bits (clipped kind.counter T) ≤
      frontendBase kind n k + 4 * beta n * T := by
  let p := closed n (k + 1)
  let sample : Code (Sym2 (Fin n)) Q (Sampler.Records Q k p.calibrationSamples) :=
    Sampler.program (fun u => key (terminals.get u)) root p.calibrationRowCap p.calibrationSamples
      p.calibrationProposals cache
  let Good (r : Sampler.Records Q k p.calibrationSamples) :=
    Sampler.GoodRecord (fun u => bits (key (terminals.get u))) p.calibrationSamples (p.xi : ℝ)
      (Sampler.Observation.ofRecords r)
  have hexp : Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) ≤ (p.xi : ℝ) / 8 := by
    simpa only [p, closed, Nat.cast_add, Nat.cast_one] using
      calibration_exp_small n (k + 1) (by omega)
  have he := LargeCoverProgram.sampler_calibration_failure I.weight bits
    (fun u => key (terminals.get u)) root p.calibrationRowCap p.calibrationSamples p.calibrationProposals
    cache hc hb (by rfl) (mean_sample_positive n) (p.xi : ℝ)
    (score_ranges n).2.2.1 (score_ranges n).2.2.2.1 hexp
  have hcalerror :
      (p.calibrationSamples : ℝ) * Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) +
        8 / (((p.xi : ℝ) / 4) ^ 2 * p.calibrationSamples) ≤ (9 / 16 : ℝ) * beta n := by
    simpa only [p, closed, Nat.cast_add, Nat.cast_one] using calibration_error n (k + 1) (by omega)
  have hbad : Code.valueProbability I.weight bits sample (fun r => ¬ Good r) ≤ (9 / 16 : ℝ) * beta n := by
    have hh := he.trans hcalerror
    convert hh using 1
    unfold Code.valueProbability
    apply congrArg (sample.evaluate I.weight bits)
    funext o
    by_cases h : Good o.value <;> simp only [Good] at h ⊢ <;> simp [h]
  have hk (o : Outcome (Sampler.Records Q k p.calibrationSamples)) (ho : Runs I.weight bits sample o)
      (hg : Good o.value) :
      (LargeCoverProgram.afterCalibration p terminals root key a (builder key a terminals (B n)) o.value).evaluate
        I.weight bits (clipped kind.counter T) ≤
      ((32 * workUnit kind + smallBase kind n k + largeBase kind n k : ℕ) : ℝ) +
        ((49 / 16 : ℝ) * beta n) * T := by
    have hcache := Mean.sampler_cache_correct I.weight bits _ root _ _ _ cache hc o ho
    exact afterCalibration_clipped kind I bits terminals root key a hT hnd o.value hcache hb hg T hceiling
  have hh := clipped_bind_bad I.weight bits sample
    (LargeCoverProgram.afterCalibration p terminals root key a (builder key a terminals (B n)))
    kind.counter T hceiling Good
    (samplerBudget kind p.calibrationProposals p.calibrationSamples)
    ((32 * workUnit kind + smallBase kind n k + largeBase kind n k : ℕ) : ℝ)
    ((9 / 16 : ℝ) * beta n) ((49 / 16 : ℝ) * beta n)
    (sampler_counter_le I.weight bits _ root _ _ _ cache kind) (Nat.cast_nonneg _)
    (by have := (beta_bounds n).1; positivity) hbad hk
  change (LargeCoverProgram.program p terminals root key a (builder key a terminals (B n)) cache).evaluate
    I.weight bits (clipped kind.counter T) ≤ _ at hh
  have he0 := (beta_bounds n).1.le
  have hnonneg := mul_nonneg he0 hceiling
  dsimp only [frontendBase]
  push_cast
  push_cast at hh
  nlinarith only [hh, hnonneg]

theorem raw_clipped (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (T : ℝ) (hceiling : 0 ≤ T) :
    (SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).evaluate I.weight bits
      (clipped kind.counter T) ≤ rawBase kind n k + 4 * beta n * T := by
  let p := parameters n (k + 1)
  let next (cfg : LargeCoverProgram.Parameters) :=
    Code.tick 11 (LargeCoverProgram.program cfg terminals root key a (builder key a terminals cfg.cutoff) cache)
  have hh := clipped_bind_full I.weight bits (configure n (k + 1) p) next kind.counter T hceiling
  dsimp only [Causal.expect] at hh
  rw [configure_evaluates, configure_evaluates] at hh
  simp only [Causal.Counter.value, Nat.cast_zero, mul_zero, add_zero] at hh
  dsimp only [p, next] at hh
  rw [configuration_public] at hh
  have ht := clipped_tick I.weight bits
    (LargeCoverProgram.program (closed n (k + 1)) terminals root key a (builder key a terminals (B n)) cache)
    11 kind.counter T
  have hf := frontend_clipped kind I bits terminals root key a hT hnd cache hc hb T hceiling
  have hnext := ht.trans (add_le_add (le_refl _) hf)
  have hcode := hh.trans (add_le_add (le_refl _) hnext)
  change (SavingEstimator.fromParameters terminals root key a p cache).evaluate I.weight bits
    (clipped kind.counter T) ≤ _ at hcode
  dsimp only [rawBase]
  push_cast at hcode ⊢
  rw [workUnit_eq]
  convert hcode using 1 <;> first | rfl | ring

end SteinerUpperBound.SavingEstimator.Resources

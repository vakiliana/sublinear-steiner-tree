module

public import SteinerUpperBound.LargeCoverProgram.Contract
public import SteinerUpperBound.LargeCoverProgram.Numeric
public import SteinerUpperBound.LargeCoverProgram.Sampling
public import SteinerUpperBound.LargeCoverProgram.Small
public import SteinerUpperBound.QueryProgram.Failure

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

attribute [local instance] copyDecidableEq

theorem bind_failure_runs {M Q R S : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) (P : R → Prop) (T : S → Prop)
    (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hk : ∀ o, Runs m bits p o → P o.value →
      Code.valueProbability m bits (next o.value) (fun r => ¬ T r) ≤ epsilon) :
    Code.valueProbability m bits (p.bind next) (fun r => ¬ T r) ≤
      Code.valueProbability m bits p (fun r => ¬ P r) + epsilon := by
  classical
  rw [Code.valueProbability_bind]
  apply (Mean.evaluate_mono_runs m bits p _
    (fun o => (if ¬ P o.value then 1 else 0) + epsilon) ?_).trans_eq
      (by
        rw [Code.evaluate_add, Code.evaluate_const]
        unfold Code.valueProbability
        congr 1
        apply congrArg (p.evaluate m bits)
        funext o
        by_cases h : P o.value <;> simp [h])
  intro o ho
  by_cases hp : P o.value
  · simpa only [hp, not_true_eq_false, ite_false, zero_add] using hk o ho hp
  · have hh := Code.valueProbability_le_one m bits (next o.value) (fun r => ¬ T r)
    simpa only [hp, not_false_eq_true, ite_true] using hh.trans (by linarith)

theorem valueProbability_tick {M Q R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (cost : ℕ) (p : Code M Q R) (P : R → Prop) :
    Code.valueProbability m bits (.tick cost p) P = Code.valueProbability m bits p P := rfl

theorem valueProbability_eq_probability {M Q R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop) :
    Code.valueProbability m bits p P = p.probability m bits {o | P o.value} := by
  unfold Code.valueProbability Code.probability
  apply congrArg (p.evaluate m bits)
  funext o
  by_cases h : P o.value <;> simp [h]

variable {Q : Type} {n k : ℕ}

theorem retainedIndex_count (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1)) :
    Nat.card (RetainedIndex bits cfg) =
      (Covers.Rejection.retained (fun u => bits (cfg.key (cfg.terminals.get u)))).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- This premise concerns ONLY the supplied Boolean VO code on genuine
canonical frames. Calibrated/pool-good prefixes may be required by a VO's own
real clocks; neither a score mean nor a saving bound is an input. -/
def LargeVORefinement (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (vo : VOBuilder Q n p.cutoff) (delta : ℝ) : Prop :=
  ∀ (gm : ℚ) (selected : Selection (Fin n)) (D : Vector Bool n),
    let cfg : LocalAccess.SlotConfig Q n (k + 1) := ⟨key, a, terminals, D⟩
    (1 - (p.xi : ℝ)) * Nat.card (RetainedIndex bits cfg) ≤ (gm : ℝ) →
    (gm : ℝ) ≤ Nat.card (RetainedIndex bits cfg) →
    50 * (p.t : ℝ) / (p.eps : ℝ) < Nat.card (RetainedIndex bits cfg) →
    selected.centers.length = selected.count → selected.count ≤ p.t →
    D = (LocalAccess.coveredResult I.weight (5 * a / 8) selected.centers).value →
    PoolGood I.weight bits p terminals key a (some (selected, D)) →
    ∃ mu : Law (Matching.Rank (PortGraph.Copy I bits cfg (rowCapacity n p gm) p.cutoff)),
      VOApproxRefinement I bits cfg (rowCapacity n p gm) p.cutoff
        (vo D (rowCapacity n p gm)) mu
        (matchedPart I bits cfg (PortGraph.liftedGraph I bits cfg (rowCapacity n p gm) p.cutoff)) delta

theorem large_saving_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (hT : terminals.toList.toFinset = I.terminals)
    (hnd : terminals.toList.Nodup) (vo : VOBuilder Q n p.cutoff) (gm gp : ℚ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (heps : 0 < (p.eps : ℝ)) (heps1 : (p.eps : ℝ) ≤ 1) (hxi : 0 < (p.xi : ℝ))
    (hxi' : (p.xi : ℝ) ≤ (p.eps : ℝ) / 100)
    (hB : SavingScores.smallThreshold (p.eps : ℝ) ≤ p.cutoff)
    (hcal : (1 - (p.xi : ℝ)) *
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card ≤ (gm : ℝ))
    (hcal1 : (gm : ℝ) ≤ (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card)
    (hupper : (gp : ℝ) ≤ (1 + (p.xi : ℝ)) *
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card)
    (hbranch : 100 * (p.t : ℚ) / p.eps < gp)
    (betaPool betaMean delta : ℝ) (hd : 0 ≤ delta) (hvo : LargeVORefinement I bits p terminals key a vo delta)
    (ht : 0 < p.t) (hbeta : 0 < betaPool) (hbeta' : betaPool < 1 / 4)
    (hL : ReusableSample.logBudget p.t betaPool ≤ p.Lbar)
    (hM : ReusableSample.rowBudget n p.t betaPool ≤ p.Mbar)
    (hs : 0 < p.meanSamples) (hbudget : 1 ≤ betaMean * ((p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2)) :
    Code.valueProbability I.weight bits (large p terminals root key a vo gm gp c)
      (fun r => ¬ GoodSaving
        (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
        (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value) ≤
      Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals +
        betaPool +
        (Mean.capError (fun u => bits (key (terminals.get u))) p.meanRowCap p.meanSamples p.meanProposals +
          p.meanSamples * delta + betaMean) := by
  have hg : 0 < (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card :=
    Finset.card_pos.mpr hb
  have hn : 0 < n := (Nat.zero_le (terminals.get root).val).trans_lt (terminals.get root).isLt
  have hnum := calibrated_large_budget n _ p gm gp hn hg ht heps
    (by linarith) hcal hupper hbranch
  have hbMean : 0 ≤ betaMean := by
    have hpos : 0 < (p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2 := by positivity
    by_contra hh
    have hn := mul_neg_of_neg_of_pos (lt_of_not_ge hh) hpos
    linarith
  let epsilon := Mean.capError (fun u => bits (key (terminals.get u)))
    p.meanRowCap p.meanSamples p.meanProposals + p.meanSamples * delta + betaMean
  have he : 0 ≤ epsilon := by
    dsimp [epsilon]
    have hh : 0 ≤ Mean.capError (fun u => bits (key (terminals.get u)))
        p.meanRowCap p.meanSamples p.meanProposals :=
      add_nonneg (Law.prob_nonneg _ _) (Law.prob_nonneg _ _)
    exact add_nonneg (add_nonneg hh (mul_nonneg (Nat.cast_nonneg _) hd)) hbMean
  have hp := deletion_pool_failure I.weight bits p terminals root key a c hc hb
    betaPool ht hbeta hbeta' hL hM
  have hk (o : Outcome (Deletion Q n))
      (ho : Runs I.weight bits (deletion p terminals root key a c) o)
      (hpool : PoolGood I.weight bits p terminals key a o.value.value) :
      Code.valueProbability I.weight bits
        (.tick 3 (match o.value.value with
          | none => .pure (abort o.value.cache gm gp false)
          | some (selected, D) => afterCovered p terminals root key a vo gm gp selected o.value.cache D))
        (fun r => ¬ GoodSaving
          (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
          (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value) ≤ epsilon := by
    cases hv : o.value.value with
    | none => simp [PoolGood, hv] at hpool
    | some val =>
      obtain ⟨selected, D⟩ := val
      have hr := deletion_cache_resources I.weight bits p terminals root key a c hc o ho
      have hshape := hr.2.2.2.2 selected D hv
      have hD := deletion_covered I.weight bits p terminals root key a c o ho selected D hv
      let cfg : LocalAccess.SlotConfig Q n (k + 1) := ⟨key, a, terminals, D⟩
      have hcount : Nat.card (RetainedIndex bits cfg) =
          (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card :=
        retainedIndex_count bits cfg
      have hcal' : (1 - (p.xi : ℝ)) * Nat.card (RetainedIndex bits cfg) ≤ (gm : ℝ) := by rwa [hcount]
      have hcal1' : (gm : ℝ) ≤ Nat.card (RetainedIndex bits cfg) := by rwa [hcount]
      have hbranch' : 50 * (p.t : ℝ) / (p.eps : ℝ) < Nat.card (RetainedIndex bits cfg) := by
        simpa only [hcount] using hnum.1
      obtain ⟨mu, hmu⟩ := hvo gm selected D hcal' hcal1' hbranch' hshape.2.1 hshape.1 hD
        (by rwa [hv] at hpool)
      have hh := afterCovered_saving_confidence I bits p cfg root hT hnd vo gm gp selected o.value.cache
        hr.1 hb hshape.2.1 hshape.1 hD heps heps1 hxi hxi' hB hbranch' hcal' hcal1'
        hnum.2.2.2 mu delta betaMean hd hmu hs hbudget
      rw [valueProbability_tick]
      rw [valueProbability_eq_probability]
      simpa only [hcount, cfg, PortGraph.retained, PortGraph.radius] using hh
  have hh := bind_failure_runs I.weight bits (deletion p terminals root key a c)
    (fun r => .tick 3 (match r.value with
      | none => .pure (abort r.cache gm gp false)
      | some (selected, D) => afterCovered p terminals root key a vo gm gp selected r.cache D))
    (fun r => PoolGood I.weight bits p terminals key a r.value)
    (fun r => GoodSaving
      (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value)
    epsilon he hk
  have hp' : Code.valueProbability I.weight bits (deletion p terminals root key a c)
      (fun r => ¬ PoolGood I.weight bits p terminals key a r.value) ≤
      Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals +
        betaPool := hp
  exact hh.trans (add_le_add hp' le_rfl)

theorem labelCount_eq_points (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup) :
    (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card =
      (ComponentExplore.retained bits key terminals.toList.toFinset).card := by
  let cfg : LocalAccess.SlotConfig Q n (k + 1) := ⟨key, 0, terminals, Vector.replicate n false⟩
  have hN : ComponentExplore.retained bits key terminals.toList.toFinset = PortGraph.retained I bits cfg := by
    ext v
    simp only [ComponentExplore.retained, PortGraph.retained, cfg, Finset.mem_filter, hT]
  calc
    _ = Nat.card (RetainedIndex bits cfg) := (retainedIndex_count bits cfg).symm
    _ = (PortGraph.retained I bits cfg).card := retainedIndex_card I bits cfg hT hnd
    _ = _ := congrArg Finset.card hN.symm

theorem small_saving_failure (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (gm gp : ℚ) (c : Cache Q) (hc : Cache.Correct bits c) (heps : 0 ≤ (p.eps : ℝ))
    (hcal : ((ComponentExplore.retained bits key terminals.toList.toFinset).card : ℝ) ≤ gp)
    (hbranch : gp ≤ 100 * (p.t : ℚ) / p.eps) :
    Code.valueProbability I.weight bits (small p terminals key a gm gp c)
      (fun r => ¬ GoodSaving
        (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
        (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value) = 0 := by
  have hh := small_contract I bits p terminals key a gm gp c hc hnd hcal hbranch
  have hN : ComponentExplore.retained bits key terminals.toList.toFinset =
      I.terminals.filter (fun v => bits (key v) = true) := by
    ext v
    simp only [ComponentExplore.retained, Finset.mem_filter, hT]
  obtain ⟨Z, hz, hz0, hzPhi, hzhalf⟩ := hh.2.1
  rw [hN] at hzPhi hzhalf
  have hg : GoodSaving
      (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ)
      (smallResult I.weight bits p terminals key a gm gp c).value.value := by
    refine ⟨Z, hz, hz0, hzPhi, ?_⟩
    linarith [mul_nonneg heps (show (0 : ℝ) ≤
      (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card by positivity)]
  unfold Code.valueProbability
  rw [small_evaluates I.weight bits]
  simp only [hg, not_true_eq_false, ite_false]

/-- End-to-end confidence of the ACTUAL calibration, branch, sampler, reusable
pool, D construction, point scores, empirical mean and clipped final scalar.
Every fresh-sampler estimate is uniform over correct incoming caches. Thus no
conditional-iid assertion is used after observing calibration or deletion. -/
theorem program_saving_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (hT : terminals.toList.toFinset = I.terminals)
    (hnd : terminals.toList.Nodup) (vo : VOBuilder Q n p.cutoff)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (heps : 0 < (p.eps : ℝ)) (heps1 : (p.eps : ℝ) ≤ 1) (hxi : 0 < (p.xi : ℝ))
    (hxi' : (p.xi : ℝ) ≤ (p.eps : ℝ) / 100)
    (hB : SavingScores.smallThreshold (p.eps : ℝ) ≤ p.cutoff)
    (betaPool betaMean delta : ℝ) (hd : 0 ≤ delta) (hvo : LargeVORefinement I bits p terminals key a vo delta)
    (ht : 0 < p.t) (hbeta : 0 < betaPool) (hbeta' : betaPool < 1 / 4)
    (hL : ReusableSample.logBudget p.t betaPool ≤ p.Lbar)
    (hM : ReusableSample.rowBudget n p.t betaPool ≤ p.Mbar)
    (hs : 0 < p.meanSamples) (hbudget : 1 ≤ betaMean * ((p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2))
    (hcalSamples : 0 < p.calibrationSamples)
    (hcalCap : p.calibrationSamples * p.calibrationRowCap ≤ p.calibrationProposals)
    (hcalExp : Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) ≤ (p.xi : ℝ) / 8) :
    Code.valueProbability I.weight bits (program p terminals root key a vo c)
      (fun r => ¬ GoodSaving
        (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
        (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value) ≤
      ((p.calibrationSamples : ℝ) * Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) +
        8 / (((p.xi : ℝ) / 4) ^ 2 * p.calibrationSamples)) +
      (Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals +
        betaPool +
        (Mean.capError (fun u => bits (key (terminals.get u))) p.meanRowCap p.meanSamples p.meanProposals +
          p.meanSamples * delta + betaMean)) := by
  classical
  let bu := fun u => bits (key (terminals.get u))
  let sample : Code (Sym2 (Fin n)) Q (Sampler.Records Q k p.calibrationSamples) :=
    Sampler.program (fun u => key (terminals.get u)) root p.calibrationRowCap p.calibrationSamples
      p.calibrationProposals c
  let Good := fun r : Sampler.Records Q k p.calibrationSamples =>
    Sampler.GoodRecord bu p.calibrationSamples (p.xi : ℝ) (Sampler.Observation.ofRecords r)
  let Target := fun r : Answer Q n => GoodSaving
    (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
    (Covers.Rejection.retained bu).card (p.eps : ℝ) r.value
  let epsilon := Mean.capError bu p.poolRowCap p.poolSamples p.poolProposals + betaPool +
    (Mean.capError bu p.meanRowCap p.meanSamples p.meanProposals + p.meanSamples * delta + betaMean)
  have hbMean : 0 ≤ betaMean := by
    by_contra hh
    have hpos : 0 < (p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2 := by positivity
    have hn := mul_neg_of_neg_of_pos (lt_of_not_ge hh) hpos
    linarith
  have he : 0 ≤ epsilon := by
    have hp : 0 ≤ Mean.capError bu p.poolRowCap p.poolSamples p.poolProposals :=
      add_nonneg (Law.prob_nonneg _ _) (Law.prob_nonneg _ _)
    have hm : 0 ≤ Mean.capError bu p.meanRowCap p.meanSamples p.meanProposals :=
      add_nonneg (Law.prob_nonneg _ _) (Law.prob_nonneg _ _)
    exact add_nonneg (add_nonneg hp hbeta.le)
      (add_nonneg (add_nonneg hm (mul_nonneg (Nat.cast_nonneg _) hd)) hbMean)
  have hcal := sampler_calibration_failure I.weight bits (fun u => key (terminals.get u)) root
    p.calibrationRowCap p.calibrationSamples p.calibrationProposals c hc hb hcalCap hcalSamples
    (p.xi : ℝ) hxi (by linarith) hcalExp
  have hp : Code.valueProbability I.weight bits sample (fun r => ¬ Good r) ≤
      (p.calibrationSamples : ℝ) * Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) +
        8 / (((p.xi : ℝ) / 4) ^ 2 * p.calibrationSamples) := by
    convert hcal using 1
    unfold Code.valueProbability
    apply congrArg (sample.evaluate I.weight bits)
    funext o
    by_cases h : Good o.value <;> simp only [Good, bu] at h ⊢ <;> simp [h]
  have hk (o : Outcome (Sampler.Records Q k p.calibrationSamples))
      (ho : Runs I.weight bits sample o) (hg : Good o.value) :
      Code.valueProbability I.weight bits (afterCalibration p terminals root key a vo o.value)
        (fun r => ¬ Target r) ≤ epsilon := by
    have hc' := Mean.sampler_cache_correct I.weight bits (fun u => key (terminals.get u)) root
      p.calibrationRowCap p.calibrationSamples p.calibrationProposals c hc o ho
    have hv := calibration_values p bits terminals key o.value hg
    have hlabels : o.value.labels ≠ none := hg.1
    have hsuccessful : o.value.successful = true := hg.2.1
    rw [afterCalibration, valueProbability_tick]
    dsimp only
    cases hl : o.value.labels with
    | none => exact (hlabels hl).elim
    | some labels =>
      simp only [hl, hsuccessful, ite_true]
      split_ifs with hbranch
      · have hv' : ((ComponentExplore.retained bits key terminals.toList.toFinset).card : ℝ) ≤
            upperObserved (k + 1) p.calibrationSamples o.value.store.proposals p.xi := by
          rw [← labelCount_eq_points I bits terminals key hT hnd]
          exact hv.2.2.1
        have hh := small_saving_failure I bits p terminals key a hT hnd
          (lowerObserved (k + 1) p.calibrationSamples o.value.store.proposals p.xi)
          (upperObserved (k + 1) p.calibrationSamples o.value.store.proposals p.xi) o.value.store.cache hc'
          heps.le hv' hbranch
        calc
          _ = 0 := by simpa only [Target, bu] using hh
          _ ≤ _ := he
      · have hh := large_saving_confidence I bits p terminals root key a hT hnd vo _ _
          o.value.store.cache hc' hb heps heps1 hxi hxi' hB hv.1 hv.2.1 hv.2.2.2
          (lt_of_not_ge hbranch) betaPool betaMean delta hd hvo ht hbeta hbeta' hL hM hs hbudget
        exact hh
  exact (bind_failure_runs I.weight bits sample (afterCalibration p terminals root key a vo)
    Good Target epsilon he hk).trans (add_le_add hp le_rfl)

end SteinerUpperBound.LargeCoverProgram

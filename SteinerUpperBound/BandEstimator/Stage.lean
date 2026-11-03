module

public import SteinerUpperBound.BandEstimator.Program
public import SteinerUpperBound.BandEstimator.Confidence

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n k : ℕ}

noncomputable def stageOutcome (g : Grid) (d : Data) (i : Index g)
    (r : Outcome (Mean.Result Q k d.samples)) : Outcome (Option ℝ × Cache Q) :=
  ⟨finish d (g.scale i.val) r.value, r.work + 2 * i.val + 31,
    r.metricQueries, r.retentionQueries, r.positiveReplies⟩

theorem stage_runs (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (d : Data) (i : Index g) (c : Cache Q)
    (o : Outcome (Option ℝ × Cache Q)) (ho : Runs w b (stage g label key root terminals d i c) o) :
    ∃ r, Runs w b (meanProgram label (key i) root terminals d (g.scale i.val) c) r ∧
      o = stageOutcome g d i r := by
  rw [stage] at ho
  cases ho with
  | tick ho =>
    obtain ⟨s, t, hs, ht, rfl⟩ := Mean.runs_bind_inv w b (scaleProgram g i.val) _ _ ho
    have he := scale_runs w b g i.val s hs
    subst s
    obtain ⟨r, z, hr, hz, rfl⟩ := Mean.runs_bind_inv w b
      (meanProgram label (key i) root terminals d (g.scale i.val) c) _ _ ht
    cases hz with
    | tick hz =>
      cases hz
      refine ⟨r, hr, ?_⟩
      simp only [scaleResult, stageOutcome, Outcome.add, Outcome.combine, Outcome.pure]
      congr 1 <;> omega

theorem stage_value (w : Sym2 (Fin n) → ℝ) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (d : Data) (i : Index g) (c : Cache Q)
    (F : Option ℝ × Cache Q → ℝ) :
    (stage g label key root terminals d i c).evaluate w b (fun o => F o.value) =
      (meanProgram label (key i) root terminals d (g.scale i.val) c).evaluate w b
        (fun o => F (finish d (g.scale i.val) o.value)) := by
  simp only [stage, Code.evaluate, Outcome.add]
  rw [Mean.evaluate_bind_value, scale_evaluates, Mean.evaluate_bind_value]
  rfl

theorem mean_cache_correct (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (key : Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (a : ℝ) (ha : 0 ≤ a) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b (meanProgram label key root terminals d a c) o →
      Cache.Correct b o.value.cache :=
  Mean.program_cache_correct
    (BandEvaluation.callback_kernel I b label key a d.cutoff terminals
      (EstimatorParameters.deltaCoarse * a) EstimatorParameters.tau hlabels (band_parameters a ha).2.2)
    (fun u => key (label u)) root d.rowCap d.samples d.totalCap c hc (accuracy d)

theorem stage_cache_correct (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (i : Index g) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b (stage g label key root terminals d i c) o → Cache.Correct b o.value.2 := by
  intro o ho
  obtain ⟨r, hr, rfl⟩ := stage_runs I.weight b g label key root terminals d i c o ho
  exact mean_cache_correct I b label (key i) root terminals hlabels d (g.scale i.val)
    (g.scale_pos _).le c hc r hr

theorem publicData_card (n k : ℕ) :
    publicData n (Fintype.card (Fin (k + 1))) = publicData n (k + 1) :=
  congrArg (publicData n) (Fintype.card_fin (k + 1))

private theorem finish_good (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (d : Data) (i : Index g)
    (hb : (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty)
    (r : Mean.Result Q k d.samples) (hc : Cache.Correct b r.cache)
    (hl : Mean.CorrectLower
      ((Covers.Rejection.retained (fun u => b (key i (label u)))).card : ℝ)
      (BandEvaluation.jointMean I b label (key i) terminals hb (g.scale i.val)
        (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau d.cutoff)
      (accuracy d) r) :
    GoodStage I b g key terminals d i (finish d (g.scale i.val) r) := by
  obtain ⟨empirical, hv, hl₀, hl₁, hloss⟩ := hl
  have ha := g.scale_pos i.val
  have hg : (0 : ℝ) < (Covers.Rejection.retained (fun u => b (key i (label u)))).card := by
    exact_mod_cast Finset.card_pos.mpr hb
  have hm := BandEvaluation.jointMean_eq I b label hlabel (key i) terminals henum hb (g.scale i.val)
    (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau d.cutoff
  have hprod := (eq_div_iff (by positivity : 3 * g.scale i.val *
    ((Covers.Rejection.retained (fun u => b (key i (label u)))).card : ℝ) ≠ 0)).mp hm
  have hcard := BandEvaluation.retained_labels_card b label hlabel (key i) terminals henum
  have ha₃ : 0 ≤ 3 * g.scale i.val := by positivity
  have hu := mul_le_mul_of_nonneg_left hl₁ ha₃
  have hl' := mul_le_mul_of_nonneg_left hloss ha₃
  rw [hcard] at hprod hu hl'
  refine ⟨hc, BandEvaluation.estimate (g.scale i.val) r.lower empirical (accuracy d), ?_,
    mul_nonneg ha₃ hl₀, ?_, ?_⟩
  · simp only [finish, hv, Option.map_some]
  · unfold target BandEvaluation.estimate retained
    nlinarith
  · unfold target BandEvaluation.estimate retained
    nlinarith

theorem stage_failure_public (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (i : Index g) (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty) :
    (stage g label key root terminals (publicData n (k + 1)) i c).probability I.weight b
      {o | ¬ GoodStage I b g key terminals (publicData n (k + 1)) i o.value} ≤
        3 * EstimatorParameters.beta n := by
  let d := publicData n (k + 1)
  let a := g.scale i.val
  have hparams := band_parameters a (g.scale_pos _).le
  let score := fun u (_ : Unit) => BandEvaluation.pointScore I
    (BandEvaluation.retainedSet b (key i) terminals) a
    (EstimatorParameters.deltaCoarse * a) EstimatorParameters.tau d.cutoff (label u)
  have hs := BandEvaluation.callback_kernel I b label (key i) a d.cutoff terminals
    (EstimatorParameters.deltaCoarse * a) EstimatorParameters.tau
    (BandEvaluation.labels_in_terminals label terminals henum) hparams.2.2
  have h₀ (u : Fin (k + 1)) (z : Unit) : 0 ≤ score u z :=
    (BandEvaluation.pointScore_bounds I _ a _ _ d.cutoff (g.scale_pos _)
      hparams.1 hparams.2.1 hparams.2.2 (label u)).1
  have h₁ (u : Fin (k + 1)) (z : Unit) : score u z ≤ 1 :=
    (BandEvaluation.pointScore_bounds I _ a _ _ d.cutoff (g.scale_pos _)
      hparams.1 hparams.2.1 hparams.2.2 (label u)).2
  have hbudget := lowerCount_public hs (fun u => key i (label u)) root n c hc hb h₀ h₁
  rw [publicData_card] at hbudget
  let F : Option ℝ × Cache Q → ℝ := fun r =>
    if GoodStage I b g key terminals d i r then 0 else 1
  have he :
      (stage g label key root terminals d i c).probability I.weight b
          {o | ¬ GoodStage I b g key terminals d i o.value} =
        (stage g label key root terminals d i c).evaluate I.weight b (fun o => F o.value) := by
    unfold Code.probability
    apply congrArg ((stage g label key root terminals d i c).evaluate I.weight b)
    funext o
    by_cases hg : GoodStage I b g key terminals d i o.value <;> simp [F, hg]
  rw [he, stage_value]
  apply le_trans _ hbudget
  unfold Code.probability
  apply Mean.evaluate_mono_runs
  intro r hr
  simp only [Set.mem_ofPred_eq]
  by_cases hl : Mean.CorrectLower
      ((Covers.Rejection.retained (fun u => b (key i (label u)))).card : ℝ)
      (BandEvaluation.jointMean I b label (key i) terminals hb a
        (EstimatorParameters.deltaCoarse * a) EstimatorParameters.tau d.cutoff) (accuracy d) r.value
  · have hcache := mean_cache_correct I b label (key i) root terminals
      (BandEvaluation.labels_in_terminals label terminals henum) d a (g.scale_pos _).le c hc r hr
    have hg := finish_good I b g label hlabel key terminals henum d i hb r.value hcache hl
    simp only [F, hg, ↓reduceIte]
    split_ifs <;> norm_num
  · dsimp only [BandEvaluation.jointMean] at hl
    simp only [F]
    split_ifs <;> norm_num

theorem success_of_failure {M R : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (P : R → Prop) (δ : ℝ)
    (h : p.probability m b {o | ¬ P o.value} ≤ δ) :
    1 - δ ≤ Code.valueProbability m b p P := by
  have he : Code.valueProbability m b p P + p.probability m b {o | ¬ P o.value} = 1 := by
    unfold Code.valueProbability Code.probability
    rw [← Code.evaluate_add]
    calc
      _ = p.evaluate m b (fun _ => 1) := by
        apply congrArg (p.evaluate m b)
        funext o
        by_cases hp : P o.value <;> simp [hp]
      _ = 1 := Code.evaluate_const _ _ _ _
  linarith

theorem stage_success_public (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (i : Index g) (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty) :
    1 - 3 * EstimatorParameters.beta n ≤
      Code.valueProbability I.weight b (stage g label key root terminals (publicData n (k + 1)) i c)
        (GoodStage I b g key terminals (publicData n (k + 1)) i) :=
  success_of_failure _ _ _ _ _ (stage_failure_public I b g label hlabel key root terminals henum i c hc hb)

end SteinerUpperBound.BandEstimator

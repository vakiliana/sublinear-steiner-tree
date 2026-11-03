module

public import SteinerUpperBound.BandEvaluation.Statistics
public import SteinerUpperBound.BandEvaluation.FrontendResources
public import SteinerUpperBound.Covers.OracleProgramMean

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n k s : ℕ}

noncomputable def samplingProgram (label : Fin (k + 1) → Fin n) (key : Fin n → Q)
    (root : Fin (k + 1)) (rowCap samples proposalCap : ℕ) (c : Cache Q) (xi a : ℝ)
    (BQ : ℕ) (terminals : List (Fin n)) (rho tau : ℝ) :
    Code (Sym2 (Fin n)) Q (Mean.Result Q k samples) :=
  Mean.program (fun u => key (label u)) root rowCap samples proposalCap c xi
    (indexedCallback label key a BQ terminals rho tau)

noncomputable def jointMean (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (key : Fin n → Q) (terminals : List (Fin n))
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (a rho tau : ℝ) (BQ : ℕ) : ℝ :=
  (Mean.pointKernel (Covers.Rejection.uniformRetained (fun u => b (key (label u))) hb)
    (fun _ => Law.pure ())).expect
      (fun p => pointScore I (retainedSet b key terminals) a rho tau BQ (label p.1))

theorem jointMean_eq (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label) (key : Fin n → Q)
    (terminals : List (Fin n)) (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (a rho tau : ℝ) (BQ : ℕ) :
    jointMean I b label key terminals hb a rho tau BQ =
      smallBandSum I (retainedSet b key terminals) a rho tau BQ /
        (3 * a * (Covers.Rejection.retained (fun u => b (key (label u)))).card) := by
  unfold jointMean
  rw [Mean.pointKernel_expect]
  simp only [Law.expect_pure]
  exact uniform_retained_mean I b label hlabel key terminals henum hb a rho tau BQ

theorem jointMean_eq_trueMean (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label) (key : Fin n → Q)
    (terminals : List (Fin n)) (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (hN : (retainedSet b key terminals).Nonempty) (a rho tau : ℝ) (BQ : ℕ) :
    jointMean I b label key terminals hb a rho tau BQ =
      trueMean I (retainedSet b key terminals) hN a rho tau BQ := by
  have hj := jointMean_eq I b label hlabel key terminals henum hb a rho tau BQ
  rw [retained_labels_card b label hlabel key terminals henum] at hj
  exact hj.trans (uniform_component_mean I _ hN a rho tau BQ).symm

def CorrectBand (target a g xi : ℝ) (r : Mean.Result Q k s) : Prop :=
  ∃ empirical, r.value = some empirical ∧ 0 ≤ estimate a r.lower empirical xi ∧
    estimate a r.lower empirical xi ≤ target ∧
    target - estimate a r.lower empirical xi ≤ 9 * xi * a * g

private theorem correctBand_of_lower (target a g mean xi : ℝ) (r : Mean.Result Q k s)
    (ha : 0 ≤ a) (hmean : 3 * a * (g * mean) = target)
    (hl : Mean.CorrectLower g mean xi r) : CorrectBand target a g xi r := by
  obtain ⟨empirical, hv, hl0, hlu, hll⟩ := hl
  have ha3 : 0 ≤ 3 * a := by positivity
  have hu := mul_le_mul_of_nonneg_left hlu ha3
  have hlos := mul_le_mul_of_nonneg_left hll ha3
  refine ⟨empirical, hv, mul_nonneg ha3 hl0, ?_, ?_⟩ <;> unfold estimate <;> nlinarith

theorem sampling_clipped_budget (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label) (key : Fin n → Q)
    (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (c : Cache Q) (hc : Cache.Correct b c)
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (a rho tau : ℝ) (BQ : ℕ) (ha : 0 < a) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (hband : tau * a ≤ a - 2 * rho)
    (beta xi : ℝ) (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) (hxi : 0 < xi) (hxi1 : xi ≤ 1) :
    let samples := Covers.Rejection.calibrationSamples (beta / 2) xi
    let rowCap := Covers.Rejection.proposalRowCap (k + 1) samples (beta / 2) xi
    let proposalCap := Covers.Rejection.proposalBudget (k + 1) samples beta
    let N := retainedSet b key terminals
    (samplingProgram label key root rowCap samples proposalCap c xi a BQ terminals rho tau).probability I.weight b
      {o | ¬ CorrectBand (smallBandSum I N a rho tau BQ) a (N.card : ℝ) xi o.value} ≤ 3 * beta := by
  dsimp only
  let score := fun u (_ : Unit) => pointScore I (retainedSet b key terminals) a rho tau BQ (label u)
  have hs := callback_kernel I b label key a BQ terminals rho tau
    (labels_in_terminals label terminals henum) hband
  have h0 (u : Fin (k + 1)) (z : Unit) : 0 ≤ score u z :=
    (pointScore_bounds I _ a rho tau BQ ha hrho htau hband (label u)).1
  have h1 (u : Fin (k + 1)) (z : Unit) : score u z ≤ 1 :=
    (pointScore_bounds I _ a rho tau BQ ha hrho htau hband (label u)).2
  have hbudget := Mean.program_lowerCount_budget hs (fun u => key (label u)) root c hc hb
    beta xi hbeta hbeta1 hxi hxi1 h0 h1
  simp only [Fintype.card_fin] at hbudget
  have hg : (0 : ℝ) < (Covers.Rejection.retained (fun u => b (key (label u)))).card := by
    exact_mod_cast Finset.card_pos.mpr hb
  have hm := jointMean_eq I b label hlabel key terminals henum hb a rho tau BQ
  have hmean : 3 * a *
      (((Covers.Rejection.retained (fun u => b (key (label u)))).card : ℝ) *
        jointMean I b label key terminals hb a rho tau BQ) =
        smallBandSum I (retainedSet b key terminals) a rho tau BQ := by
    have hh := (eq_div_iff (by positivity : 3 * a *
      ((Covers.Rejection.retained (fun u => b (key (label u)))).card : ℝ) ≠ 0)).mp hm
    nlinarith
  apply le_trans _ hbudget
  unfold Code.probability
  apply Code.evaluate_mono
  intro o
  simp only [Set.mem_ofPred_eq]
  by_cases hl : Mean.CorrectLower
      (((Covers.Rejection.retained (fun u => b (key (label u)))).card : ℝ))
      (jointMean I b label key terminals hb a rho tau BQ) xi o.value
  · have hb := correctBand_of_lower _ a _ _ xi o.value ha.le hmean hl
    have hb' : CorrectBand (smallBandSum I (retainedSet b key terminals) a rho tau BQ) a
        ((retainedSet b key terminals).card : ℝ) xi o.value := by
      simpa only [retained_labels_card b label hlabel key terminals henum] using hb
    simp only [hb', not_true_eq_false, ↓reduceIte]
    split_ifs <;> norm_num
  · dsimp only [jointMean] at hl
    simp only [hl, not_false_eq_true, ↓reduceIte]
    split_ifs <;> norm_num

theorem sampling_compiled_resources (I : Instance (Fin n)) (b : Q → Bool)
    (label : Fin (k + 1) → Fin n) (key : Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabel : ∀ u, label u ∈ terminals)
    (a rho tau : ℝ) (BQ : ℕ) (hband : tau * a ≤ a - 2 * rho)
    (rowCap samples proposalCap : ℕ) (c : Cache Q) (hc : Cache.Correct b c) (xi : ℝ)
    (seed : ((samplingProgram label key root rowCap samples proposalCap c xi a BQ terminals rho tau).compile
      I.weight).Seed) :
    let o := (((samplingProgram label key root rowCap samples proposalCap c xi a BQ terminals rho tau).compile
      I.weight).tree seed).output b
    o.work ≤ 64 * (proposalCap + samples + 1) +
      (40000000000 * (n + terminals.length + 1) * (BQ + 2) ^ 12) * samples ∧
      o.positiveReplies ≤ (BQ + 2) * samples := by
  have hs := callback_kernel I b label key a BQ terminals rho tau hlabel hband
  exact Mean.program_compiled_worst hs
    (40000000000 * (n + terminals.length + 1) * (BQ + 2) ^ 12) (BQ + 1)
    (fun u c hc seed => (guarded_compiled_resources I.weight b key a BQ terminals rho tau
      (label u) c hc seed).2.2.1)
    (fun u c hc seed => (guarded_compiled_resources I.weight b key a BQ terminals rho tau
      (label u) c hc seed).2.2.2)
    (fun u => key (label u)) root rowCap samples proposalCap c hc xi seed

end SteinerUpperBound.BandEvaluation

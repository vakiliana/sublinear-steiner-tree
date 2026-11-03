module

public import SteinerUpperBound.BandEstimator.Multiscale
public import SteinerUpperBound.BandEstimator.Polynomial

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation
open scoped Classical

variable {Q : Type*} {n k : ℕ}

def WorldGood (b : Q → Bool) (g : Grid) (label : Fin (k + 1) → Fin n)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (L : ℝ) : Prop :=
  (∀ i, (Covers.Rejection.retained (fun u => b (key i (label u)))).Nonempty) ∧
    mass b g key terminals ≤ (EstimatorParameters.A n : ℝ) * L

theorem program_success_world (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (L : ℝ) (hL : 0 ≤ L)
    (hw : WorldGood b g label key terminals L) (c : Cache Q) (hc : Cache.Correct b c) :
    1 - 3 * EstimatorParameters.beta n * (g.intervals + 1) ≤
      Code.valueProbability I.weight b
        (program g label key root terminals (publicData n (k + 1)) c)
        (GoodOutput I b g key terminals (publicData n (k + 1)) L) :=
  program_success I b g label hlabel key root terminals henum hw.1 L hL hw.2 c hc

theorem program_success_budget (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (L : ℝ) (hL : 0 ≤ L)
    (hw : WorldGood b g label key terminals L)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c) :
    1 - (3 / 1000000 : ℝ) ≤
      Code.valueProbability I.weight b
        (program g label key root terminals (publicData n (k + 1)) c)
        (GoodOutput I b g key terminals (publicData n (k + 1)) L) := by
  have h := program_success_world I b g label hlabel key root terminals henum L hL hw c hc
  have hu := EstimatorParameters.beta_union n (g.intervals + 1) hheight
  push_cast at hu
  nlinarith

theorem fromParameters_success (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (L : ℝ) (hL : 0 ≤ L)
    (hw : WorldGood b g label key terminals L) (c : Cache Q) (hc : Cache.Correct b c) :
    1 - 3 * EstimatorParameters.beta n * (g.intervals + 1) ≤
      Code.valueProbability I.weight b
        (fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c)
        (GoodOutput I b g key terminals (publicData n (k + 1)) L) := by
  rw [fromParameters, valueProbability_tick, ofParameters_eq]
  exact program_success_world I b g label hlabel key root terminals henum L hL hw c hc

variable {Ω : Type*} [Fintype Ω]

theorem program_averaged_success (μ : Law Ω) (oracle : Ω → Q → Bool) (I : Instance (Fin n))
    (g : Grid) (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (L : ℝ) (hL : 0 ≤ L)
    (c : Cache Q) (hc : ∀ ω, 0 < μ.mass ω → Cache.Correct (oracle ω) c)
    (η : ℝ) (hworld : μ.prob {ω | ¬ WorldGood (oracle ω) g label key terminals L} ≤ η) :
    1 - 3 * EstimatorParameters.beta n * (g.intervals + 1) - η ≤
      μ.expect (fun ω => Code.valueProbability I.weight (oracle ω)
        (program g label key root terminals (publicData n (k + 1)) c)
        (GoodOutput I (oracle ω) g key terminals (publicData n (k + 1)) L)) := by
  let ε := 3 * EstimatorParameters.beta n * (g.intervals + 1)
  let F := fun ω => Code.valueProbability I.weight (oracle ω)
    (program g label key root terminals (publicData n (k + 1)) c)
    (GoodOutput I (oracle ω) g key terminals (publicData n (k + 1)) L)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity [(EstimatorParameters.beta_bounds n).1]
  have hp (ω : Ω) (hm : 0 < μ.mass ω) :
      (1 - ε) - (if WorldGood (oracle ω) g label key terminals L then 0 else 1) ≤ F ω := by
    by_cases hw : WorldGood (oracle ω) g label key terminals L
    · simpa only [hw, ite_true, sub_zero] using
        program_success_world I (oracle ω) g label hlabel key root terminals henum L hL hw c (hc ω hm)
    · have hF : 0 ≤ F ω := Code.valueProbability_nonneg _ _ _ _
      simp only [hw, ite_false]
      linarith
  have hi :
      μ.expect (fun ω => if WorldGood (oracle ω) g label key terminals L then (0 : ℝ) else 1) =
        μ.prob {ω | ¬ WorldGood (oracle ω) g label key terminals L} := by
    rw [Law.prob_eq_expect]
    apply congrArg μ.expect
    funext ω
    by_cases hw : WorldGood (oracle ω) g label key terminals L <;> simp [hw]
  have h := μ.expect_mono_support hp
  rw [Law.expect_sub, Law.expect_const, hi] at h
  linarith

theorem program_averaged_resources (μ : Law Ω) (oracle : Ω → Q → Bool) (I : Instance (Fin n))
    (g : Grid) (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : ∀ ω, 0 < μ.mass ω → Cache.Correct (oracle ω) c) :
    μ.expect (fun ω => (program g label key root terminals (publicData n (k + 1)) c).evaluate I.weight
        (oracle ω) (fun o => (o.work : ℝ))) ≤ workPolynomial n ∧
      μ.expect (fun ω => (program g label key root terminals (publicData n (k + 1)) c).evaluate I.weight
        (oracle ω) (fun o => (o.positiveReplies : ℝ))) ≤ positivePolynomial n := by
  constructor
  · apply le_trans _ (Law.expect_const μ ((workPolynomial n : ℕ) : ℝ)).le
    apply Law.expect_mono_support
    intro ω hm
    exact (program_public_expected I (oracle ω) g label hlabel key root terminals hnodup henum hheight
      c (hc ω hm)).1
  · apply le_trans _ (Law.expect_const μ ((positivePolynomial n : ℕ) : ℝ)).le
    apply Law.expect_mono_support
    intro ω hm
    exact (program_public_expected I (oracle ω) g label hlabel key root terminals hnodup henum hheight
      c (hc ω hm)).2

theorem fromParameters_averaged_success (μ : Law Ω) (oracle : Ω → Q → Bool) (I : Instance (Fin n))
    (g : Grid) (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (L : ℝ) (hL : 0 ≤ L)
    (c : Cache Q) (hc : ∀ ω, 0 < μ.mass ω → Cache.Correct (oracle ω) c)
    (η : ℝ) (hworld : μ.prob {ω | ¬ WorldGood (oracle ω) g label key terminals L} ≤ η) :
    1 - 3 * EstimatorParameters.beta n * (g.intervals + 1) - η ≤
      μ.expect (fun ω => Code.valueProbability I.weight (oracle ω)
        (fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c)
        (GoodOutput I (oracle ω) g key terminals (publicData n (k + 1)) L)) := by
  simpa only [fromParameters, valueProbability_tick, ofParameters_eq] using
    program_averaged_success μ oracle I g label hlabel key root terminals henum L hL c hc η hworld

theorem fromParameters_averaged_resources (μ : Law Ω) (oracle : Ω → Q → Bool) (I : Instance (Fin n))
    (g : Grid) (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : ∀ ω, 0 < μ.mass ω → Cache.Correct (oracle ω) c) :
    μ.expect (fun ω => (fromParameters g label key root terminals
        (EstimatorParameters.parameters n (k + 1)) c).evaluate I.weight
        (oracle ω) (fun o => (o.work : ℝ))) ≤ workPolynomial n ∧
      μ.expect (fun ω => (fromParameters g label key root terminals
        (EstimatorParameters.parameters n (k + 1)) c).evaluate I.weight
        (oracle ω) (fun o => (o.positiveReplies : ℝ))) ≤ positivePolynomial n := by
  constructor
  · apply le_trans _ (Law.expect_const μ ((workPolynomial n : ℕ) : ℝ)).le
    apply Law.expect_mono_support
    intro ω hm
    exact (fromParameters_expected I (oracle ω) g label hlabel key root terminals hnodup henum hheight
      c (hc ω hm)).1
  · apply le_trans _ (Law.expect_const μ ((positivePolynomial n : ℕ) : ℝ)).le
    apply Law.expect_mono_support
    intro ω hm
    exact (fromParameters_expected I (oracle ω) g label hlabel key root terminals hnodup henum hheight
      c (hc ω hm)).2

end SteinerUpperBound.BandEstimator

module

public import SteinerUpperBound.BandEstimator.Resources

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical

def core (n : ℕ) : ℕ := (EstimatorParameters.coreSizes n).sum + 1

theorem core_positive (n : ℕ) : 0 < core n := by unfold core; omega

theorem core_le (n x : ℕ) (hx : x ∈ EstimatorParameters.coreSizes n) : x ≤ core n :=
  (EstimatorParameters.member_le_sum _ _ hx).trans (Nat.le_succ _)

def workPolynomial (n : ℕ) : ℕ := 1000000000000 * (n + 1) * (core n + 2) ^ 14
def positivePolynomial (n : ℕ) : ℕ := (core n + 2) ^ 3

theorem public_budgets (n k length : ℕ) (g : Grid) (hk : k + 1 ≤ n) (hl : length ≤ n)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n) :
    stageWork g n length (publicData n (k + 1)) ≤
        200000000000 * (n + 1) * (core n + 2) ^ 13 ∧
      programWork g n length (publicData n (k + 1)) + 16 ≤ workPolynomial n ∧
      stagePositive (publicData n (k + 1)) ≤ (core n + 2) ^ 2 ∧
      programPositive g (publicData n (k + 1)) ≤ positivePolynomial n := by
  let d := publicData n (k + 1)
  let K := core n
  let S := (n + 1) * (K + 2) ^ 13
  have hK : 0 < K := core_positive n
  have hs : d.samples ≤ K :=
    core_le n _ (by simp [d, publicData, EstimatorParameters.coreSizes])
  have hb : d.cutoff ≤ K :=
    core_le n _ (by simp [d, publicData, EstimatorParameters.coreSizes])
  have hD : EstimatorParameters.betaDenom n ≤ K :=
    core_le n _ (by simp [EstimatorParameters.coreSizes])
  have hH : g.intervals + 1 ≤ K :=
    hheight.trans (core_le n _ (by simp [EstimatorParameters.coreSizes]))
  have hpow : K + 2 ≤ (K + 2) ^ 13 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by omega : 1 ≤ K + 2) (by norm_num : (1 : ℕ) ≤ 13))
  have hKS : K ≤ S := by
    apply (show K ≤ (K + 2) ^ 13 by omega).trans
    have hh := Nat.mul_le_mul_right ((K + 2) ^ 13) (show 1 ≤ n + 1 by omega)
    simpa only [Nat.one_mul] using hh
  have hS : 1 ≤ S := by
    have hh : 0 < S := by dsimp [S]; positivity
    omega
  have hcap : d.totalCap ≤ 32 * S := by
    calc
      _ = 16 * (k + 1) * (d.samples + EstimatorParameters.betaDenom n) := rfl
      _ ≤ 16 * (n + 1) * (K + K) := by gcongr; omega
      _ = 32 * ((n + 1) * K) := by ring
      _ ≤ 32 * S := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega : K ≤ (K + 2) ^ 13))
  have hoverhead : 64 * (d.totalCap + d.samples + 1) ≤ 2176 * S := by omega
  have hcallback :
      40000000000 * (n + length + 1) * (d.cutoff + 2) ^ 12 * d.samples ≤
        80000000000 * S := by
    calc
      _ ≤ 40000000000 * (2 * (n + 1)) * (K + 2) ^ 12 * (K + 2) := by gcongr <;> omega
      _ = _ := by dsimp [S]; ring
  have hmean : meanWork n length d ≤ 100000000000 * S := by
    dsimp only [meanWork]
    omega
  have hstage : stageWork g n length d ≤ 200000000000 * S := by
    dsimp only [stageWork]
    omega
  have hwork : programWork g n length d + 16 ≤ workPolynomial n := by
    have hcoef : stageWork g n length d + 8 ≤ 300000000000 * S := by omega
    calc
      _ = (stageWork g n length d + 8) * (g.intervals + 1) + 21 := by
        simp only [programWork]
      _ ≤ (300000000000 * S) * (K + 2) + 21 :=
        Nat.add_le_add_right (Nat.mul_le_mul hcoef (by omega)) _
      _ ≤ 1000000000000 * (S * (K + 2)) := by
        have hh : 1 ≤ S * (K + 2) := by
          have hp : 0 < S * (K + 2) := by positivity
          omega
        simp only [Nat.mul_assoc]
        omega
      _ = _ := by dsimp [S, K, workPolynomial]; ring
  have hpositive : stagePositive d ≤ (K + 2) ^ 2 := by
    dsimp only [stagePositive]
    calc
      _ ≤ (K + 2) * (K + 2) := by gcongr; omega
      _ = _ := by ring
  refine ⟨?_, hwork, hpositive, ?_⟩
  · simpa only [S, K, Nat.mul_assoc] using hstage
  · dsimp only [programPositive, positivePolynomial]
    calc
      _ ≤ (K + 2) ^ 2 * (K + 2) := Nat.mul_le_mul hpositive (by omega)
      _ = _ := by dsimp [K]; ring

variable {Q : Type*} {n k : ℕ}

theorem label_count (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label) : k + 1 ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective label hlabel

theorem stage_public_expected (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (i : Index g) (c : Cache Q) (hc : Cache.Correct b c) :
    (stage g label key root terminals (publicData n (k + 1)) i c).evaluate I.weight b
        (fun o => (o.work : ℝ)) ≤ 200000000000 * (n + 1 : ℝ) * ((core n + 2 : ℕ) : ℝ) ^ 13 ∧
      (stage g label key root terminals (publicData n (k + 1)) i c).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ ((core n + 2 : ℕ) : ℝ) ^ 2 := by
  have h := stage_expected I b g label key root terminals
    (BandEvaluation.labels_in_terminals label terminals henum) (publicData n (k + 1)) i c hc
  have hp := public_budgets n k terminals.length g (label_count label hlabel)
    (BandEvaluation.terminals_length terminals hnodup) hheight
  have hw : (stageWork g n terminals.length (publicData n (k + 1)) : ℝ) ≤
      200000000000 * (n + 1 : ℝ) * ((core n + 2 : ℕ) : ℝ) ^ 13 := by exact_mod_cast hp.1
  have hpos : (stagePositive (publicData n (k + 1)) : ℝ) ≤ ((core n + 2 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hp.2.2.1
  constructor <;> linarith [h.1, h.2]

theorem program_public_compiled_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c)
    (seed : ((program g label key root terminals (publicData n (k + 1)) c).compile I.weight).Seed) :
    let o := (((program g label key root terminals (publicData n (k + 1)) c).compile I.weight).tree seed).output b
    Cache.Correct b o.value.2 ∧ o.work ≤ workPolynomial n ∧ o.positiveReplies ≤ positivePolynomial n := by
  have h := program_compiled_resources I b g label key root terminals
    (BandEvaluation.labels_in_terminals label terminals henum) (publicData n (k + 1)) c hc seed
  have hp := public_budgets n k terminals.length g (label_count label hlabel)
    (BandEvaluation.terminals_length terminals hnodup) hheight
  exact ⟨h.1, h.2.1.trans (by omega), h.2.2.trans hp.2.2.2⟩

theorem fromParameters_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b
      (fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c) o →
      Cache.Correct b o.value.2 ∧ o.work ≤ workPolynomial n ∧ o.positiveReplies ≤ positivePolynomial n := by
  intro o ho
  rw [fromParameters, ofParameters_eq] at ho
  cases ho with
  | tick ho =>
    have h := program_resources I b g label key root terminals
      (BandEvaluation.labels_in_terminals label terminals henum) (publicData n (k + 1)) c hc _ ho
    have hp := public_budgets n k terminals.length g (label_count label hlabel)
      (BandEvaluation.terminals_length terminals hnodup) hheight
    refine ⟨h.1, ?_, ?_⟩
    · dsimp only [Outcome.add]
      omega
    · simpa only [Outcome.add, Nat.zero_add] using h.2.2.trans hp.2.2.2

theorem fromParameters_compiled_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c)
    (seed : ((fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c).compile
      I.weight).Seed) :
    let o := (((fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c).compile
      I.weight).tree seed).output b
    Cache.Correct b o.value.2 ∧ o.work ≤ workPolynomial n ∧ o.positiveReplies ≤ positivePolynomial n :=
  fromParameters_resources I b g label hlabel key root terminals hnodup henum hheight c hc _
    (runs_compile I.weight b _ seed)

theorem program_public_expected (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c) :
    (program g label key root terminals (publicData n (k + 1)) c).evaluate I.weight b
        (fun o => (o.work : ℝ)) ≤ workPolynomial n ∧
      (program g label key root terminals (publicData n (k + 1)) c).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ positivePolynomial n := by
  have h := program_expected I b g label key root terminals
    (BandEvaluation.labels_in_terminals label terminals henum) (publicData n (k + 1)) c hc
  have hp := public_budgets n k terminals.length g (label_count label hlabel)
    (BandEvaluation.terminals_length terminals hnodup) hheight
  have hw : (programWork g n terminals.length (publicData n (k + 1)) : ℝ) ≤ workPolynomial n := by
    exact_mod_cast (show programWork g n terminals.length (publicData n (k + 1)) ≤ workPolynomial n by omega)
  have hpos : (programPositive g (publicData n (k + 1)) : ℝ) ≤ positivePolynomial n := by
    exact_mod_cast hp.2.2.2
  constructor <;> linarith [h.1, h.2]

theorem fromParameters_expected (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (hlabel : Function.Injective label)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (hnodup : terminals.Nodup) (henum : FiniteMST.labels label = terminals.toFinset)
    (hheight : g.intervals + 1 ≤ EstimatorParameters.heightBudget n)
    (c : Cache Q) (hc : Cache.Correct b c) :
    (fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c).evaluate I.weight b
        (fun o => (o.work : ℝ)) ≤ workPolynomial n ∧
      (fromParameters g label key root terminals (EstimatorParameters.parameters n (k + 1)) c).evaluate I.weight b
        (fun o => (o.positiveReplies : ℝ)) ≤ positivePolynomial n := by
  have h := program_expected I b g label key root terminals
    (BandEvaluation.labels_in_terminals label terminals henum) (publicData n (k + 1)) c hc
  have hp := public_budgets n k terminals.length g (label_count label hlabel)
    (BandEvaluation.terminals_length terminals hnodup) hheight
  have hw : (programWork g n terminals.length (publicData n (k + 1)) : ℝ) + 16 ≤ workPolynomial n := by
    exact_mod_cast hp.2.1
  have hpos : (programPositive g (publicData n (k + 1)) : ℝ) ≤ positivePolynomial n := by
    exact_mod_cast hp.2.2.2
  rw [fromParameters, Mean.work_tick, ofParameters_eq, Mean.positive_tick]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith [h.1, h.2]

end SteinerUpperBound.BandEstimator

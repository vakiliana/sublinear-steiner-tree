module

public import SteinerUpperBound.Covers.OracleProgramSamplerGuarantees

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Sampler

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling

variable {V M Q : Type*} {k : ℕ}

theorem program_cap_evaluate (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (cache : Q → Option Bool) (F : Records Q k s → ℝ) :
    ((program query root C s B cache : Code M Q (Records Q k s)).cap
      (16 * (B + s + 1))).evaluate m b (fun o => o.value.elim 0 F) =
      (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
        (fun o => F o.value) := by
  rw [Code.cap_expect, ← Code.compile_expect, ← Code.compile_expect]
  unfold Compiled.expect
  apply congrArg ((program query root C s B cache : Code M Q (Records Q k s)).compile m).law.expect
  funext seed
  have hr := program_resources m b query root C s B cache seed
  have hw :
      ((((program query root C s B cache : Code M Q (Records Q k s)).compile m).tree seed).output b).work ≤
        16 * (B + s + 1) := by omega
  simp only [hw, ite_true]

theorem program_cap_total_evaluate (m : M → ℝ) (b : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (cache : Q → Option Bool) (F : Option (Records Q k s) → ℝ) :
    ((program query root C s B cache : Code M Q (Records Q k s)).cap
      (16 * (B + s + 1))).evaluate m b (fun o => F o.value) =
      (program query root C s B cache : Code M Q (Records Q k s)).evaluate m b
        (fun o => F (some o.value)) := by
  have hf :
      (fun o : Outcome (Option (Records Q k s)) => F o.value) =
        (fun o => F none + o.value.elim 0 (fun r => F (some r) - F none)) := by
    funext o
    cases o.value <;> simp
  rw [hf, Code.evaluate_add, Code.evaluate_const,
    program_cap_evaluate m b query root C s B cache]
  rw [← Code.evaluate_const m b (program query root C s B cache) (F none),
    ← Code.evaluate_add]
  apply congrArg ((program query root C s B cache : Code M Q (Records Q k s)).evaluate m b)
  funext o
  simp only [Code.evaluate_const]
  ring

theorem bits_cache_correct [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (cache : Q → Option Bool) (oracle : Q → Bool) (h : 0 < (bits cfg m cache).mass oracle) :
    Cache.Correct oracle cache :=
  Factory.cachedKernel_consistent cache
    (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials) oracle h

theorem oracle_nonempty [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (hroot : cache (query root) = some true) (oracle : Q → Bool)
    (h : 0 < (bits cfg m cache).mass oracle) :
    (Rejection.retained (fun y => oracle (query y))).Nonempty := by
  have hc := bits_cache_correct cfg m cache oracle h
  exact ⟨root, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc (query root) true hroot⟩⟩

/-- Analysis-only totalization. The empty case has zero mass when a designated
true cache entry is present. This law is never queried by runtime code. -/
noncomputable def oracleUniform (oracle : Q → Bool) (query : Fin (k + 1) → Q)
    (root : Fin (k + 1)) : Law (Fin (k + 1)) :=
  if h : (Rejection.retained (fun y => oracle (query y))).Nonempty then
    Rejection.uniformRetained (fun y => oracle (query y)) h else Law.pure root

theorem averaged_program_uniform [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (hroot : cache (query root) = some true)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    ∀ test : Option (Fin s → Fin (k + 1)) → Bool,
      |(bits cfg m cache).expect (fun oracle =>
          (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
            (fun o => if test o.value.labels = true then 1 else 0)) -
        (bits cfg m cache).expect (fun oracle =>
          (tape (oracleUniform oracle query root) s).prob {labels | test (some labels) = true})| ≤ β := by
  classical
  dsimp only
  intro test
  rw [← Law.expect_sub]
  apply ((bits cfg m cache).abs_expect_le _).trans
  apply le_trans _ (Law.expect_const (bits cfg m cache) β).le
  apply Law.expect_mono_support
  intro oracle hm
  have hc := bits_cache_correct cfg m cache oracle hm
  have hb := oracle_nonempty cfg m cache query root hroot oracle hm
  have h := program_uniform_budget m oracle query root cache hc hb β ξ hβ hβ1 hξ hξ1 test
  simpa only [oracleUniform, dif_pos hb] using h

theorem averaged_program_calibration [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (hroot : cache (query root) = some true)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    (bits cfg m cache).expect (fun oracle =>
      (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
        (fun o => if GoodRecord (fun y => oracle (query y)) s ξ (Observation.ofRecords o.value)
          then 0 else 1)) ≤ β := by
  apply le_trans _ (Law.expect_const (bits cfg m cache) β).le
  apply Law.expect_mono_support
  intro oracle hm
  exact program_calibration_budget m oracle query root cache
    (bits_cache_correct cfg m cache oracle hm)
    (oracle_nonempty cfg m cache query root hroot oracle hm) β ξ hβ hβ1 hξ hξ1

theorem factory_sampler_pending [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B W D : ℕ) :
    (factory cfg cache W D (program query root C s B cache)).probability m b
      {o | o.value.value = none} ≤ Real.exp ((s : ℝ) - (D : ℝ) / (2 * (k + 1))) := by
  have h := factory_pending_bound cfg m b cache W D (program query root C s B cache) (s : ℝ)
  have hz : (bits cfg m cache).expect (fun oracle =>
      (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
        (fun o => threshold (s : ℝ) o.positiveReplies)) = 0 := by
    have he : (fun oracle =>
        (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
          (fun o => threshold (s : ℝ) o.positiveReplies)) = (fun _ => (0 : ℝ)) := by
      funext oracle
      exact program_positive_tail_zero m oracle query root C s B cache
    rw [he, Law.expect_const]
  simpa only [hz, zero_add] using h

theorem factory_sampler_pending_budget [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B W D : ℕ) (ε : ℝ) (hε : 0 < ε)
    (hD : 2 * ((k + 1 : ℕ) : ℝ) * ((s : ℝ) + Real.log (1 / ε)) ≤ D) :
    (factory cfg cache W D (program query root C s B cache)).probability m b
      {o | o.value.value = none} ≤ ε :=
  (factory_sampler_pending cfg m b cache query root C s B W D).trans
    (factory_clock_exp_le k D s ε hε hD)

theorem factory_sampler_new_positive_zero [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (C s B W D : ℕ) :
    (factory cfg cache W D (program query root C s B cache)).evaluate m b
      (fun o => threshold (s : ℝ) o.value.state.newPositive) = 0 := by
  have h := factory_positive_tail_le cfg m b cache W D (program query root C s B cache) (s : ℝ)
  have hz : (bits cfg m cache).expect (fun oracle =>
      (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
        (fun o => threshold (s : ℝ) o.positiveReplies)) = 0 := by
    have he : (fun oracle =>
        (program query root C s B cache : Code (Sym2 V) Q (Records Q k s)).evaluate m oracle
          (fun o => threshold (s : ℝ) o.positiveReplies)) = (fun _ => (0 : ℝ)) := by
      funext oracle
      exact program_positive_tail_zero m oracle query root C s B cache
    rw [he, Law.expect_const]
  rw [hz] at h
  apply le_antisymm h
  apply Code.evaluate_nonneg
  intro o
  unfold threshold
  split_ifs <;> norm_num

/-- Actual metric-factory sampler coupling to iid uniform retained labels.
Both local rejection/proposal errors and the actual global factory clock error
are included. The two marginal calibration/label bounds are not conditioned on
each other. -/
theorem factory_sampler_uniform [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (hroot : cache (query root) = some true)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (D : ℕ) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    let W := 16 * (B + s + 1)
    ∀ test : Option (Fin s → Fin (k + 1)) → Bool,
      let frontTest := fun r : Option (Records Q k s) => r.elim false (fun r => test r.labels)
      |(factory cfg cache W D (program query root C s B cache)).evaluate m b
          (fun o => if o.value.value.map frontTest = some true then 1 else 0) -
        (bits cfg m cache).expect (fun oracle =>
          (tape (oracleUniform oracle query root) s).prob {labels | test (some labels) = true})| ≤
        β + Real.exp ((s : ℝ) - (D : ℝ) / (2 * (k + 1))) := by
  classical
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
  let W := 16 * (B + s + 1)
  let p : Code (Sym2 V) Q (Records Q k s) := program query root C s B cache
  intro test
  let frontTest := fun r : Option (Records Q k s) => r.elim false (fun r => test r.labels)
  have hc := factory_boolean_close cfg m b cache W D p frontTest
  have hcap (oracle : Q → Bool) :
      (p.cap W).evaluate m oracle (fun o => if frontTest o.value = true then (1 : ℝ) else 0) =
        p.evaluate m oracle (fun o => if test o.value.labels = true then 1 else 0) := by
    have hf : (fun o : Outcome (Option (Records Q k s)) => if frontTest o.value = true then (1 : ℝ) else 0) =
        (fun o => o.value.elim 0 (fun r => if test r.labels = true then 1 else 0)) := by
      funext o
      cases he : o.value with
      | none => simp [frontTest, he]
      | some r => cases ht : test r.labels <;> simp [frontTest, he, ht]
    rw [hf]
    exact program_cap_evaluate m oracle query root C s B cache _
  simp_rw [hcap] at hc
  have hu := averaged_program_uniform cfg m cache query root hroot β ξ hβ hβ1 hξ hξ1 test
  have hp := factory_sampler_pending cfg m b cache query root C s B W D
  have hpe :
      (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then (1 : ℝ) else 0) =
        (factory cfg cache W D p).probability m b {o | o.value.value = none} := by
    unfold Code.probability
    apply congrArg ((factory cfg cache W D p).evaluate m b)
    funext o
    by_cases h : o.value.value = none <;> simp [h]
  rw [hpe] at hc
  exact (abs_sub_le _ _ _).trans
    ((add_le_add (hc.trans hp) hu).trans_eq (add_comm _ _))

/-- Total label-law comparison for the actual metric-query sampler. Global,
frontend-work, and proposal aborts all produce `none`; arbitrary Boolean events,
including the abort event, satisfy the stated error bound. -/
theorem factory_sampler_uniform_output [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (query : Fin (k + 1) → Q) (root : Fin (k + 1))
    (hroot : cache (query root) = some true)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (D : ℕ) :
    let s := Rejection.calibrationSamples (β / 2) ξ
    let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
    let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
    let W := 16 * (B + s + 1)
    ∀ test : Option (Fin s → Fin (k + 1)) → Bool,
      |(factory cfg cache W D (program query root C s B cache)).evaluate m b
          (fun o => if test (o.value.value.join.bind (fun r => r.labels)) = true then 1 else 0) -
        (bits cfg m cache).expect (fun oracle =>
          (tape (oracleUniform oracle query root) s).prob {labels | test (some labels) = true})| ≤
        β + Real.exp ((s : ℝ) - (D : ℝ) / (2 * (k + 1))) := by
  classical
  dsimp only
  let s := Rejection.calibrationSamples (β / 2) ξ
  let C := Rejection.proposalRowCap (Fintype.card (Fin (k + 1))) s (β / 2) ξ
  let B := Rejection.proposalBudget (Fintype.card (Fin (k + 1))) s β
  let W := 16 * (B + s + 1)
  let p : Code (Sym2 V) Q (Records Q k s) := program query root C s B cache
  intro test
  have hc := factory_output_boolean_close cfg m b cache W D p
    (fun r => test (r.bind (fun r => r.labels)))
  have hcap (oracle : Q → Bool) :
      (p.cap W).evaluate m oracle
          (fun o => if test (o.value.bind (fun r => r.labels)) = true then (1 : ℝ) else 0) =
        p.evaluate m oracle (fun o => if test o.value.labels = true then 1 else 0) :=
    program_cap_total_evaluate m oracle query root C s B cache
      (fun r => if test (r.bind (fun r => r.labels)) = true then 1 else 0)
  simp_rw [hcap] at hc
  have hu := averaged_program_uniform cfg m cache query root hroot β ξ hβ hβ1 hξ hξ1 test
  have hp := factory_sampler_pending cfg m b cache query root C s B W D
  have hpe :
      (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then (1 : ℝ) else 0) =
        (factory cfg cache W D p).probability m b {o | o.value.value = none} := by
    unfold Code.probability
    apply congrArg ((factory cfg cache W D p).evaluate m b)
    funext o
    by_cases h : o.value.value = none <;> simp [h]
  rw [hpe] at hc
  exact (abs_sub_le _ _ _).trans
    ((add_le_add (hc.trans hp) hu).trans_eq (add_comm _ _))

end SteinerUpperBound.Covers.OracleProgram.Sampler

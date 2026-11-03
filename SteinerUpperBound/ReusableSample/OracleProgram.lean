module

public import SteinerUpperBound.ReusableSample.OracleProgramSemantics

@[expose] public section

/-!
# Causal oracle implementation of the reusable pool

`OracleProgram.program` takes only public center IDs, supplied sample IDs, a
radius, and integer parameters. It first reads the distance matrix by metric
queries, initializes a live bitmap by a charged loop, and runs the charged
record scans and repeated-squaring probability computation. Neither a metric
instance nor the retained universe is a runtime input.

`program_evaluate` identifies its output with the checked rational pool law.
`program_resources` is pathwise for every compiled finite seed, including
zero-probability branches. `iid_pool_success` supplies the probability theorem
when the externally supplied IDs are independent uniform retained points.
-/

namespace SteinerUpperBound.ReusableSample.OracleProgram

open SteinerLowerBound
open SteinerUpperBound.QueryProgram
open scoped BigOperators Classical

variable {V Q : Type*}

/-- No oracle, metric instance, or retained-universe enumeration is supplied to
this code. All matrix entries come from `Code.metric` replies in `readMatrix`. -/
noncomputable def program {n Ns : ℕ} (centers : Fin n → V) (X : Fin Ns → V)
    (r : ℝ) (t Lbar : ℕ) : Code (Sym2 V) Q (Fin n → Bool) :=
  .tick 3 ((readMatrix r X centers).bind fun B =>
    (fill Ns true).bind fun live => loop Lbar Ns t B t live)

def workBound (n Ns : ℕ) : ℕ :=
  n * (24 * Ns + 8 * Nat.log2 (Ns + 1) + 80) + 3 * Ns + 16

theorem workBound_le (n Ns : ℕ) :
    workBound n Ns ≤ 64 * (n + 1) * (Ns + 1) * (Nat.log2 (Ns + 1) + 2) := by
  let A := (Ns + 1) * (Nat.log2 (Ns + 1) + 2)
  have h₁ : 24 * Ns + 8 * Nat.log2 (Ns + 1) + 80 ≤ 64 * A := by
    dsimp [A]
    nlinarith [Nat.zero_le (Ns * Nat.log2 (Ns + 1))]
  have h₂ : 3 * Ns + 16 ≤ 64 * A := by
    dsimp [A]
    nlinarith [Nat.zero_le (Ns * Nat.log2 (Ns + 1))]
  have hh := Nat.mul_le_mul_left n h₁
  dsimp [workBound]
  calc
    _ ≤ n * (64 * A) + 64 * A := Nat.add_le_add hh h₂
    _ = _ := by dsimp [A]; ring

theorem program_good (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ) :
    Sure m b (program centers X r t Lbar)
      (Good (fun T => acceptances T ≤ t) (workBound n Ns) (n * Ns)) := by
  let B := observedMatrix m centers X r
  let after : (Fin n → Fin Ns → Bool) → Code (Sym2 V) Q (Fin n → Bool) :=
    fun B => (fill Ns true).bind fun live => loop Lbar Ns t B t live
  have ha : Sure m b (after B)
      (Good (fun T => acceptances T ≤ t) (3 * Ns + 1 + (n * perRow Ns + 3)) 0) :=
    good_bind_value m b (fill Ns true) (fun live => loop Lbar Ns t B t live)
      (fun _ => true) _ (3 * Ns + 1) 0 (n * perRow Ns + 3) 0
      (fill_good m b Ns true) (loop_good m b Lbar Ns t B t _)
  have hr := good_bind_value m b (readMatrix r X centers) after B
    (fun T => acceptances T ≤ t) (n * (8 * Ns + 5) + 1) (n * Ns)
    (3 * Ns + 1 + (n * perRow Ns + 3)) 0 (readMatrix_good m b r X centers) ha
  have hh := good_tick m b _ _ _ _ 3 hr
  simp only [Nat.add_zero] at hh
  exact good_mono m b _ hh (by dsimp [workBound, perRow]; nlinarith) (fun _ h => h)

/-- Worst-case counters for each actual compiled seed, not merely in
expectation or on a high-probability event. -/
theorem program_resources (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ)
    (s : ((program centers X r t Lbar : Code (Sym2 V) Q _).compile m).Seed) :
    let o := (((program centers X r t Lbar).compile m).tree s).output b
    acceptances o.value ≤ t ∧ o.work ≤ workBound n Ns ∧
      o.metricQueries = n * Ns ∧ o.retentionQueries = 0 ∧ o.positiveReplies = 0 := by
  exact (program_good m b centers X r t Lbar).compile m b _ _ s

theorem program_evaluate (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ)
    (F : (Fin n → Bool) → ℝ) :
    (program centers X r t Lbar).evaluate m b (fun o => F o.value) =
      (rationalMatrixMechanism Lbar Ns t (observedMatrix m centers X r)).expect F := by
  rw [program]
  simp only [Code.evaluate, Outcome.add]
  rw [evaluate_bind_good m b (readMatrix r X centers) _
    (observedMatrix m centers X r) (n * (8 * Ns + 5) + 1) (n * Ns)
    (readMatrix_good m b r X centers)]
  rw [evaluate_bind_good m b (fill Ns true) _ (fun _ => true)
    (3 * Ns + 1) 0 (fill_good m b Ns true)]
  rw [loop_evaluate, flagSet_true]
  rfl

noncomputable def outputLaw (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ) :
    Law (Fin n → Bool) :=
  let c := (program centers X r t Lbar : Code (Sym2 V) Q _).compile m
  c.law.map fun s => ((c.tree s).output b).value

theorem outputLaw_expect (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ)
    (F : (Fin n → Bool) → ℝ) :
    (outputLaw m b centers X r t Lbar).expect F =
      (program centers X r t Lbar).evaluate m b (fun o => F o.value) := by
  rw [outputLaw, Law.expect_map]
  exact Code.compile_expect m b (program centers X r t Lbar) (fun o => F o.value)

theorem outputLaw_probability (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ)
    (E : Set (Fin n → Bool)) :
    (outputLaw m b centers X r t Lbar).prob E =
      (program centers X r t Lbar).probability m b {o | o.value ∈ E} := by
  rw [Law.prob_eq_expect, outputLaw_expect]
  rfl

theorem outputLaw_eq (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar : ℕ) :
    outputLaw m b centers X r t Lbar =
      rationalMatrixMechanism Lbar Ns t (observedMatrix m centers X r) := by
  apply LawOperations.ext_prob
  intro E
  rw [Law.prob_eq_expect, outputLaw_expect]
  rw [program_evaluate m b centers X r t Lbar (fun T => if T ∈ E then 1 else 0),
    ← Law.prob_eq_expect]

/-- A cap at the explicit worst-case budget never removes an output path. -/
theorem capped_program_evaluate (m : Sym2 V → ℝ) (b : Q → Bool) {n Ns : ℕ}
    (centers : Fin n → V) (X : Fin Ns → V) (r : ℝ) (t Lbar budget : ℕ)
    (hbudget : workBound n Ns ≤ budget) (F : (Fin n → Bool) → ℝ) :
    ((program centers X r t Lbar).cap budget).evaluate m b
      (fun o => o.value.elim 0 F) =
        (rationalMatrixMechanism Lbar Ns t (observedMatrix m centers X r)).expect F := by
  rw [Code.cap_expect]
  calc
    _ = (program centers X r t Lbar).evaluate m b (fun o => F o.value) := by
      rw [← Code.compile_expect, ← Code.compile_expect]
      apply congrArg ((program centers X r t Lbar).compile m).law.expect
      funext s
      have hs := (program_resources m b centers X r t Lbar s).2.1.trans hbudget
      exact ite_eq_left hs
    _ = _ := program_evaluate m b centers X r t Lbar F

section UniformSamples

variable {U : Type*} [Fintype U] [Nonempty U]

attribute [local instance] dataFintype transcriptFintype

/-- Logical rows of the actual retained universe. This definition occurs only
in the specification and never in `program` or its input data. -/
noncomputable def rows {n : ℕ} (m : Sym2 V → ℝ) (centers : Fin n → V)
    (embed : U → V) (r : ℝ) : Fin n → Finset U :=
  fun j => Finset.univ.filter fun u => m (Sym2.mk (centers j) (embed u)) ≤ r

omit [Nonempty U] in
theorem observed_eq_membership {n Ns : ℕ} (m : Sym2 V → ℝ)
    (centers : Fin n → V) (embed : U → V) (X : Fin Ns → U) (r : ℝ) :
    observedMatrix m centers (fun i => embed (X i)) r =
      membershipMatrix (rows m centers embed r) X := by
  funext j i
  simp only [observedMatrix, membershipMatrix, rows, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem iid_outputLaw_eq_rationalRun {n Ns : ℕ} (m : Sym2 V → ℝ) (b : Q → Bool)
    (centers : Fin n → V) (embed : U → V) (r : ℝ) (t Lbar : ℕ) :
    ((Law.uniform U).iid (Fin Ns)).bind
      (fun X => outputLaw m b centers (fun i => embed (X i)) r t Lbar) =
      rationalRun Lbar Ns t (rows m centers embed r) := by
  unfold rationalRun
  congr 1
  funext X
  rw [outputLaw_eq, observed_eq_membership]

/-- Independent uniform retained samples may be supplied by an external checked
sampler. All randomness of the subsequent causal code is integrated here.
Calibration uses only integer doubling comparisons, not analytic primitives. -/
theorem iid_pool_success {n : ℕ} (m : Sym2 V → ℝ) (b : Q → Bool)
    (centers : Fin n → V) (embed : U → V) (r : ℝ)
    (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (k ℓ : ℕ)
    (hk : 512 * (t : ℝ) ≤ β * (2 : ℝ) ^ k)
    (hℓ : 128 * ((n : ℝ) + 1) * t ≤ β * (2 : ℝ) ^ ℓ) :
    1 - β ≤ ((Law.uniform U).iid (Fin (integerSamples t (k + 1) (ℓ + 1)))).expect
      (fun X => (program centers (fun i => embed (X i)) r t (k + 1)).probability m b
        {o | Specification (rows m centers embed r) t o.value}) := by
  have hh := (integer_reusable_sample_rational_of_doubling
    (rows m centers embed r) t ht β hβ hβ' k ℓ hk hℓ).1
  rw [← iid_outputLaw_eq_rationalRun m b centers embed r t (k + 1),
    Law.prob_bind] at hh
  simpa only [outputLaw_probability, Set.mem_ofPred_eq] using hh

end UniformSamples

end SteinerUpperBound.ReusableSample.OracleProgram

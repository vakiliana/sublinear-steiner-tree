module

public import SteinerUpperBound.QueryProgram.MetricOnly
public import SteinerUpperBound.Covers.OracleProgram

@[expose] public section

noncomputable section

namespace SteinerUpperBound.FactoryExecution

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {V Q R : Type*} {k : ℕ}

def program (cfg : Config V Q k) (cache : Cache Q) (W D : ℕ) (frontend : Code (Sym2 V) Q R) :
    Code (Sym2 V) Empty (Option R) :=
  ((factory cfg cache W D frontend).map (fun r => r.value.join)).metricOnly

theorem program_value (cfg : Config V Q k) (cache : Cache Q) (W D : ℕ)
    (frontend : Code (Sym2 V) Q R) (m : Sym2 V → ℝ) (F : Option R → ℝ) :
    (program cfg cache W D frontend).evaluate m Code.emptyBits (fun o => F o.value) =
      (factory cfg cache W D frontend).evaluate m (fun _ => false)
        (fun o => F o.value.value.join) := by
  rw [program, Code.metricOnly_value, Code.evaluate_map]
  rfl

theorem program_expected_work (cfg : Config V Q k) (cache : Cache Q) (W D : ℕ)
    (frontend : Code (Sym2 V) Q R) (m : Sym2 V → ℝ) :
    (program cfg cache W D frontend).evaluate m Code.emptyBits (fun o => (o.work : ℝ)) ≤
      (32 * (W + D + 1) : ℕ) := by
  have h := Code.metricOnly_expected_work m
    ((factory cfg cache W D frontend).map (fun r => r.value.join))
  rw [Code.evaluate_map] at h
  apply h.trans
  rw [← Code.compile_expect]
  apply (Law.expect_mono _ (fun seed => ?_)).trans_eq (Law.expect_const _ _)
  change (((((factory cfg cache W D frontend).compile m).tree seed).output
    (fun _ => false)).work : ℝ) ≤ ((32 * (W + D + 1) : ℕ) : ℝ)
  exact_mod_cast (factory_resources cfg m (fun _ => false) cache W D frontend seed).2.1

private theorem evaluate_div {M : Type*} (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (F : Outcome R → ℝ) (a : ℝ) :
    p.evaluate m b (fun o => F o / a) = p.evaluate m b F / a := by
  rw [← Code.compile_expect m b p (fun o => F o / a), ← Code.compile_expect m b p F]
  simp only [Compiled.expect, Law.expect, mul_div_assoc, Finset.sum_div]

private theorem expect_div {S : Type*} [Fintype S] (mu : Law S) (F : S → ℝ) (a : ℝ) :
    mu.expect (fun s => F s / a) = mu.expect F / a := by
  simp only [Law.expect, mul_div_assoc, Finset.sum_div]

theorem success_close [Fintype Q] (cfg : Config V Q k) (cache : Cache Q) (W D : ℕ)
    (frontend : Code (Sym2 V) Q R) (m : Sym2 V → ℝ) (P : R → Prop) :
    |Code.valueProbability m Code.emptyBits (program cfg cache W D frontend) (Code.SomeGood P) -
        (bits cfg m cache).expect (fun oracle =>
          Code.valueProbability m oracle (frontend.cap W) (Code.SomeGood P))| ≤
      (factory cfg cache W D frontend).probability m (fun _ => false)
        {o | o.value.value = none} := by
  have h := factory_output_boolean_close cfg m (fun _ => false) cache W D frontend
    (fun r => decide (Code.SomeGood P r))
  have hleft :
      (factory cfg cache W D frontend).evaluate m (fun _ => false)
        (fun o => if decide (Code.SomeGood P o.value.value.join) = true then (1 : ℝ) else 0) =
      Code.valueProbability m Code.emptyBits (program cfg cache W D frontend) (Code.SomeGood P) := by
    simpa only [Code.valueProbability, decide_eq_true_eq] using
      (program_value cfg cache W D frontend m (fun r => if Code.SomeGood P r then (1 : ℝ) else 0)).symm
  have hright :
      (bits cfg m cache).expect (fun oracle => (frontend.cap W).evaluate m oracle
        (fun o => if decide (Code.SomeGood P o.value) = true then (1 : ℝ) else 0)) =
      (bits cfg m cache).expect (fun oracle =>
        Code.valueProbability m oracle (frontend.cap W) (Code.SomeGood P)) := by
    simp only [Code.valueProbability, decide_eq_true_eq]
  rw [hleft, hright] at h
  simpa only [Code.probability, Set.mem_setOf_eq] using h

theorem success [Fintype Q] (cfg : Config V Q k) (cache : Cache Q) (W D : ℕ)
    (frontend : Code (Sym2 V) Q R) (m : Sym2 V → ℝ) (P : R → Prop)
    (lower ordinary positive cutoff : ℝ) (ha : 0 < cutoff)
    (hgood : lower ≤ (bits cfg m cache).expect (fun oracle =>
      Code.valueProbability m oracle frontend P))
    (hw : (bits cfg m cache).expect (fun oracle =>
      frontend.evaluate m oracle (fun o => (o.work : ℝ))) ≤ ordinary)
    (hp : (bits cfg m cache).expect (fun oracle =>
      frontend.evaluate m oracle (fun o => (o.positiveReplies : ℝ))) ≤ positive) :
    lower - ordinary / (W + 1 : ℕ) - positive / cutoff -
        Real.exp (cutoff - (D : ℝ) / (2 * (k + 1))) ≤
      Code.valueProbability m Code.emptyBits (program cfg cache W D frontend) (Code.SomeGood P) := by
  let mu := bits cfg m cache
  have hcap := mu.expect_mono (fun oracle => Code.cap_success m oracle frontend W P)
  rw [Law.expect_sub, expect_div] at hcap
  have hc := div_le_div_of_nonneg_right hw (show (0 : ℝ) ≤ (W + 1 : ℕ) by positivity)
  have tail (oracle : Q → Bool) :
      frontend.evaluate m oracle (fun o => threshold cutoff o.positiveReplies) ≤
        frontend.evaluate m oracle (fun o => (o.positiveReplies : ℝ)) / cutoff := by
    rw [← evaluate_div]
    apply Code.evaluate_mono
    intro o
    by_cases h : cutoff < (o.positiveReplies : ℝ)
    · simp only [threshold, h, ite_true]
      exact (le_div_iff₀ ha).mpr (by simpa only [one_mul] using h.le)
    · simp only [threshold, h, ite_false]
      exact div_nonneg (Nat.cast_nonneg _) ha.le
  have ht := mu.expect_mono tail
  rw [expect_div] at ht
  have ht' := div_le_div_of_nonneg_right hp ha.le
  have hpend := factory_pending_bound cfg m (fun _ => false) cache W D frontend cutoff
  have hclose := (abs_le.mp (success_close cfg cache W D frontend m P)).1
  linarith

end SteinerUpperBound.FactoryExecution

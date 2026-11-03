module

public import SteinerUpperBound.SavingEstimator.Resources.Point
public import SteinerUpperBound.QueryProgram.Failure

@[expose] public section

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram
open PortGraph.RuntimeAdapter.Averaged
open scoped Classical

variable {M Q A B : Type*}

theorem counter_expect_of_runs (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (kind : CounterKind) (work positive : ℕ)
    (h : ∀ o, Runs m bits p o → o.work ≤ work ∧ o.positiveReplies ≤ positive) :
    p.evaluate m bits kind.counter.value ≤
      (match kind with | .ordinary => work | .positive => positive : ℕ) := by
  cases kind
  · rw [ordinary_value]
    exact (Mean.evaluate_mono_runs m bits p _ (fun _ => (work : ℝ))
      (fun o ho => by exact_mod_cast (h o ho).1)).trans_eq (Code.evaluate_const m bits p _)
  · rw [positive_value]
    exact (Mean.evaluate_mono_runs m bits p _ (fun _ => (positive : ℝ))
      (fun o ho => by exact_mod_cast (h o ho).2)).trans_eq (Code.evaluate_const m bits p _)

/-- Bad prefixes pay at most the test ceiling.  The cheap continuation bound
is used only on the already observed good prefix, never on future draws. -/
theorem clipped_bind_bad (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (k : A → Code M Q B) (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T)
    (Good : A → Prop) (preBudget future δbad δfuture : ℝ)
    (hpre : p.evaluate m bits counter.value ≤ preBudget)
    (hfuture : 0 ≤ future) (hδ : 0 ≤ δfuture)
    (hbad : Code.valueProbability m bits p (fun a => ¬ Good a) ≤ δbad)
    (hk : ∀ o, Runs m bits p o → Good o.value →
      (k o.value).evaluate m bits (clipped counter T) ≤ future + δfuture * T) :
    (p.bind k).evaluate m bits (clipped counter T) ≤
      preBudget + future + (δbad + δfuture) * T := by
  have hp (o : Outcome A) (ho : Runs m bits p o) :
      (k o.value).evaluate m bits (clipped counter T) ≤
        future + δfuture * T + T * (if ¬ Good o.value then 1 else 0) := by
    by_cases hg : Good o.value
    · simpa only [hg, not_true_eq_false, ↓reduceIte, mul_zero, add_zero] using hk o ho hg
    · have hh := clipped_expect_le_ceiling m bits (k o.value) counter T
      simp only [hg, not_false_eq_true, ↓reduceIte, mul_one]
      nlinarith [mul_nonneg hδ hT]
  have hh := Mean.evaluate_mono_runs m bits p _ _ hp
  rw [Code.evaluate_add, Code.evaluate_const, eval_const_mul] at hh
  have hbad' : p.evaluate m bits (fun o => if ¬ Good o.value then 1 else 0) ≤ δbad := by
    unfold Code.valueProbability at hbad
    convert hbad using 1
    apply congrArg (p.evaluate m bits)
    funext o
    by_cases h : Good o.value <;> simp [h]
  have ht := mul_le_mul_of_nonneg_left hbad' hT
  have hc := (clipped_bind_full m bits p k counter T hT).trans
    (add_le_add hpre (hh.trans (add_le_add (le_refl _) ht)))
  nlinarith

theorem counter_bad_le_clipped (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (counter : Causal.Counter) (T : ℝ) (hT : 0 < T) :
    p.evaluate m bits (fun o => if ¬ counter.value o ≤ T then 1 else 0) ≤
      p.evaluate m bits (clipped counter T) / T := by
  have hp (o : Outcome A) :
      (if ¬ counter.value o ≤ T then (1 : ℝ) else 0) ≤ clipped counter T o / T := by
    by_cases h : counter.value o ≤ T
    · simp only [h, not_true_eq_false, ↓reduceIte]
      exact div_nonneg (clipped_nonneg counter T hT.le o) hT.le
    · have h' : T ≤ counter.value o := le_of_lt (lt_of_not_ge h)
      simp only [h, not_false_eq_true, ↓reduceIte, clipped, min_eq_right h', div_self hT.ne']
      exact le_refl _
  have hh := Code.evaluate_mono m bits p hp
  have he :
      p.evaluate m bits (fun o => clipped counter T o / T) =
        p.evaluate m bits (clipped counter T) / T := by
    simp only [div_eq_mul_inv, mul_comm _ T⁻¹, eval_const_mul]
  exact hh.trans_eq he

noncomputable def originalGood (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (work positive : ℕ) (seed : (p.compile m).Seed) : Prop :=
  Causal.counterGood m bits p CounterKind.ordinary.counter work seed ∧
    Causal.counterGood m bits p CounterKind.positive.counter positive seed

theorem originalGood_costs (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (work positive : ℕ) :
    (p.compile m).law.expect (fun seed => if originalGood m bits p work positive seed then
      Causal.counterSeed m bits p CounterKind.ordinary.counter seed else 0) ≤ work ∧
    (p.compile m).law.expect (fun seed => if originalGood m bits p work positive seed then
      Causal.counterSeed m bits p CounterKind.positive.counter seed else 0) ≤ positive := by
  constructor
  · have hh := (p.compile m).law.expect_mono (fun seed => show
        (if originalGood m bits p work positive seed then
          Causal.counterSeed m bits p CounterKind.ordinary.counter seed else 0) ≤ (work : ℝ) by
      split_ifs with h
      · exact h.1
      · exact Nat.cast_nonneg _)
    simpa only [Law.expect_const] using hh
  · have hh := (p.compile m).law.expect_mono (fun seed => show
        (if originalGood m bits p work positive seed then
          Causal.counterSeed m bits p CounterKind.positive.counter seed else 0) ≤ (positive : ℝ) by
      split_ifs with h
      · exact h.2
      · exact Nat.cast_nonneg _)
    simpa only [Law.expect_const] using hh

theorem originalGood_failure (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (work positive : ℕ) (δwork δpositive : ℝ)
    (hw : p.evaluate m bits (fun o => if ¬ CounterKind.ordinary.counter.value o ≤ work then 1 else 0) ≤ δwork)
    (hp : p.evaluate m bits (fun o => if ¬ CounterKind.positive.counter.value o ≤ positive then 1 else 0) ≤ δpositive) :
    (p.compile m).law.prob {seed | ¬ originalGood m bits p work positive seed} ≤ δwork + δpositive := by
  have hs : {seed | ¬ originalGood m bits p work positive seed} ⊆
      {seed | ¬ Causal.counterGood m bits p CounterKind.ordinary.counter work seed} ∪
        {seed | ¬ Causal.counterGood m bits p CounterKind.positive.counter positive seed} := by
    intro seed hseed
    by_cases h : Causal.counterGood m bits p CounterKind.ordinary.counter work seed
    · exact Or.inr (fun h' => hseed ⟨h, h'⟩)
    · exact Or.inl h
  have hh := ((p.compile m).law.prob_mono hs).trans ((p.compile m).law.prob_union_le _ _)
  rw [Causal.counterGood_failure, Causal.counterGood_failure] at hh
  exact hh.trans (add_le_add hw hp)

end SteinerUpperBound.SavingEstimator.Resources

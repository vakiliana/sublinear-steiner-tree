module

public import SteinerUpperBound.LargeCoverProgram.Support
public import SteinerUpperBound.Matching.Padded.CounterTruncation

@[expose] public section

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical

variable {M Q A B : Type*}

noncomputable def clipped (counter : Causal.Counter) (ceiling : ℝ) (o : Outcome A) : ℝ :=
  min (counter.value o) ceiling

theorem counter_combine (counter : Causal.Counter) (a : Outcome A) (b : Outcome B) :
    counter.value (a.combine b) = counter.value a + counter.value b := by
  dsimp only [Causal.Counter.value, Outcome.combine]
  push_cast
  ring

theorem counter_add_work (counter : Causal.Counter) (a : ℕ) (o : Outcome A) :
    counter.value (o.add a 0 0 0) = counter.work * a + counter.value o := by
  dsimp only [Causal.Counter.value, Outcome.add]
  push_cast
  ring

theorem clipped_nonneg (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling)
    (o : Outcome A) : 0 ≤ clipped counter ceiling o :=
  le_min (counter.value_nonneg o) hc

theorem clipped_le_counter (counter : Causal.Counter) (ceiling : ℝ) (o : Outcome A) :
    clipped counter ceiling o ≤ counter.value o := min_le_left _ _

theorem clipped_le_ceiling (counter : Causal.Counter) (ceiling : ℝ) (o : Outcome A) :
    clipped counter ceiling o ≤ ceiling := min_le_right _ _

theorem clipped_combine (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling)
    (a : Outcome A) (b : Outcome B) :
    clipped counter ceiling (a.combine b) ≤ clipped counter ceiling a + clipped counter ceiling b := by
  dsimp only [clipped]
  rw [counter_combine]
  by_cases ha : counter.value a ≤ ceiling
  · rw [min_eq_left ha]
    by_cases hb : counter.value b ≤ ceiling
    · rw [min_eq_left hb]
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge hb)]
      linarith [min_le_right (counter.value a + counter.value b) ceiling, counter.value_nonneg a]
  · rw [min_eq_right (le_of_not_ge ha)]
    have hm : 0 ≤ min (counter.value b) ceiling := le_min (counter.value_nonneg b) hc
    linarith [min_le_right (counter.value a + counter.value b) ceiling]

theorem eval_const_mul (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (r : ℝ) (f : Outcome A → ℝ) :
    p.evaluate m bits (fun o => r * f o) = r * p.evaluate m bits f := by
  rw [← Code.compile_expect, ← Code.compile_expect]
  exact Law.expect_const_mul _ _ _

theorem clipped_expect_nonneg (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    0 ≤ p.evaluate m bits (clipped counter ceiling) :=
  Code.evaluate_nonneg m bits p (fun o => clipped_nonneg counter ceiling hc o)

theorem clipped_expect_le_ceiling (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (counter : Causal.Counter) (ceiling : ℝ) :
    p.evaluate m bits (clipped counter ceiling) ≤ ceiling :=
  (Code.evaluate_mono m bits p (fun o => clipped_le_ceiling counter ceiling o)).trans_eq
    (Code.evaluate_const m bits p ceiling)

theorem clipped_expect_le_counter (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (counter : Causal.Counter) (ceiling : ℝ) :
    p.evaluate m bits (clipped counter ceiling) ≤ p.evaluate m bits counter.value :=
  Code.evaluate_mono m bits p (fun o => clipped_le_counter counter ceiling o)

theorem clipped_bind (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (k : A → Code M Q B) (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    (p.bind k).evaluate m bits (clipped counter ceiling) ≤
      p.evaluate m bits (clipped counter ceiling) +
        Causal.expect m bits p (fun a => (k a).evaluate m bits (clipped counter ceiling)) := by
  rw [Code.evaluate_bind]
  have hi (a : Outcome A) :
      (k a.value).evaluate m bits (fun b => clipped counter ceiling (a.combine b)) ≤
        clipped counter ceiling a + (k a.value).evaluate m bits (clipped counter ceiling) := by
    have hh := Code.evaluate_mono m bits (k a.value)
      (fun b => clipped_combine counter ceiling hc a b)
    simpa only [Code.evaluate_add, Code.evaluate_const] using hh
  have hh := Code.evaluate_mono m bits p hi
  simpa only [Code.evaluate_add, Causal.expect] using hh

theorem clipped_bind_full (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (k : A → Code M Q B) (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    (p.bind k).evaluate m bits (clipped counter ceiling) ≤
      p.evaluate m bits counter.value +
        Causal.expect m bits p (fun a => (k a).evaluate m bits (clipped counter ceiling)) :=
  (clipped_bind m bits p k counter ceiling hc).trans
    (add_le_add (clipped_expect_le_counter m bits p counter ceiling) (le_refl _))

private theorem min_add_le (x y T : ℝ) (hx : 0 ≤ x) :
    min (x + y) T ≤ x + min y T := by
  by_cases h : y ≤ T
  · rw [min_eq_left h]
    exact min_le_left _ _
  · rw [min_eq_right (le_of_not_ge h)]
    linarith [min_le_right (x + y) T]

theorem clipped_tick (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (n : ℕ) (counter : Causal.Counter) (ceiling : ℝ) :
    (Code.tick n p).evaluate m bits (clipped counter ceiling) ≤
      counter.work * (n + 1 : ℕ) + p.evaluate m bits (clipped counter ceiling) := by
  change p.evaluate m bits (fun o => clipped counter ceiling (o.add (n + 1) 0 0 0)) ≤ _
  have hh := Code.evaluate_mono m bits p (fun o => show
      clipped counter ceiling (o.add (n + 1) 0 0 0) ≤
        counter.work * (n + 1 : ℕ) + clipped counter ceiling o from by
    dsimp only [clipped]
    rw [counter_add_work]
    exact min_add_le _ _ _ (mul_nonneg counter.work_nonneg (Nat.cast_nonneg _)))
  simpa only [Code.evaluate_add, Code.evaluate_const] using hh

theorem clipped_pure (m : M → ℝ) (bits : Q → Bool) (a : A)
    (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    (Code.pure a : Code M Q A).evaluate m bits (clipped counter ceiling) = 0 := by
  simp only [Code.evaluate, clipped, Causal.Counter.value, Outcome.pure, Nat.cast_zero,
    mul_zero, add_zero, min_eq_left hc]

theorem clipped_bind_tick (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (f : A → B) (n : ℕ) (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    (p.bind (fun a => .tick n (.pure (f a)))).evaluate m bits (clipped counter ceiling) ≤
      p.evaluate m bits (clipped counter ceiling) + counter.work * (n + 1 : ℕ) := by
  have hh := clipped_bind m bits p (fun a => .tick n (.pure (f a))) counter ceiling hc
  have hi (a : A) :
      (Code.tick n (.pure (f a)) : Code M Q B).evaluate m bits (clipped counter ceiling) ≤
        counter.work * (n + 1 : ℕ) := by
    have ht := clipped_tick m bits (.pure (f a) : Code M Q B) n counter ceiling
    simpa only [clipped_pure m bits (f a) counter ceiling hc, add_zero] using ht
  have he := Code.evaluate_mono m bits p (fun o => hi o.value)
  rw [Code.evaluate_const] at he
  exact hh.trans (add_le_add (le_refl _) he)

theorem clipped_tick_pure (m : M → ℝ) (bits : Q → Bool) (a : A) (n : ℕ)
    (counter : Causal.Counter) (ceiling : ℝ) (hc : 0 ≤ ceiling) :
    (Code.tick n (.pure a) : Code M Q A).evaluate m bits (clipped counter ceiling) ≤
      counter.work * (n + 1 : ℕ) := by
  have hh := clipped_tick m bits (.pure a : Code M Q A) n counter ceiling
  simpa only [clipped_pure m bits a counter ceiling hc, add_zero] using hh

theorem clipped_bind_const (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (k : A → Code M Q B) (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T)
    (budget : ℝ) (hk : ∀ a, (k a).evaluate m bits (clipped counter T) ≤ budget) :
    (p.bind k).evaluate m bits (clipped counter T) ≤
      p.evaluate m bits (clipped counter T) + budget := by
  have hh := clipped_bind m bits p k counter T hT
  have ht := Code.evaluate_mono m bits p (fun o => hk o.value)
  rw [Code.evaluate_const] at ht
  exact hh.trans (add_le_add (le_refl _) ht)

theorem clipped_mask (m : M → ℝ) (bits : Q → Bool) (p : Code M Q A)
    (counter : Causal.Counter) (ceiling : ℝ) (Good : Outcome A → Prop) :
    p.evaluate m bits (clipped counter ceiling) ≤
      p.evaluate m bits (fun o => if Good o then counter.value o else 0) +
        ceiling * p.evaluate m bits (fun o => if Good o then 0 else 1) := by
  have hh := Code.evaluate_mono m bits p (fun o => show
      clipped counter ceiling o ≤ (if Good o then counter.value o else 0) +
        ceiling * (if Good o then 0 else 1) from by
    by_cases h : Good o
    · simpa only [h, ↓reduceIte, mul_zero, add_zero] using clipped_le_counter counter ceiling o
    · simpa only [h, ↓reduceIte, mul_one, zero_add] using clipped_le_ceiling counter ceiling o)
  simpa only [Code.evaluate_add, eval_const_mul] using hh

end SteinerUpperBound.SavingEstimator.Resources

module

public import SteinerUpperBound.SavingEstimator.Resources.Envelope
public import SteinerUpperBound.LargeCoverProgram.MeanResources

@[expose] public section

set_option maxHeartbeats 1600000

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram
open scoped Classical BigOperators
open Covers.FiniteSampling

variable {M Q U : Type*}

theorem scores_clipped_step (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U) (s : ℕ) (labels : Fin (s + 1) → U) (c : Cache Q)
    (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T) :
    (Mean.scores callback (s + 1) labels c).evaluate m bits (clipped counter T) ≤
      6 * counter.work + (callback (labels 0) c).evaluate m bits (clipped counter T) +
        Causal.expect m bits (callback (labels 0) c) (fun head =>
          (Mean.scores callback s (Fin.tail labels) head.2).evaluate m bits (clipped counter T)) := by
  let next (head : ℝ × Cache Q) :=
    (Mean.scores callback s (Fin.tail labels) head.2).bind (fun tail =>
      .tick 2 (.pure (head.1 + tail.1, tail.2)))
  have hi (head : ℝ × Cache Q) :
      (next head).evaluate m bits (clipped counter T) ≤
        (Mean.scores callback s (Fin.tail labels) head.2).evaluate m bits (clipped counter T) +
          3 * counter.work := by
    have hh := clipped_bind_tick m bits (Mean.scores callback s (Fin.tail labels) head.2)
      (fun tail => (head.1 + tail.1, tail.2)) 2 counter T hT
    convert hh using 1 <;> norm_num <;> ring
  have he := Code.evaluate_mono m bits (callback (labels 0) c) (fun o => hi o.value)
  rw [Code.evaluate_add, Code.evaluate_const] at he
  have hb := clipped_bind m bits (callback (labels 0) c) next counter T hT
  have ho := clipped_tick m bits ((callback (labels 0) c).bind next) 2 counter T
  have hh := ho.trans (add_le_add (le_refl _)
    (hb.trans (add_le_add (le_refl _) he)))
  change (Mean.scores callback (s + 1) labels c).evaluate m bits (clipped counter T) ≤ _ at hh
  dsimp only [Causal.expect]
  norm_num only [Nat.cast_ofNat] at hh
  linarith

theorem scores_clipped_cache (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q U)
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T)
    (price : U → ℝ)
    (hprice : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (clipped counter T) ≤ price u)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct bits c) :
    (Mean.scores callback s labels c).evaluate m bits (clipped counter T) ≤
      counter.work * (6 * s + 2 : ℕ) + ∑ j, price (labels j) := by
  induction s generalizing c with
  | zero =>
    have hh := clipped_tick m bits (.pure ((0 : ℝ), c) : Code M Q (ℝ × Cache Q)) 1 counter T
    simpa only [Mean.scores, clipped_pure m bits ((0 : ℝ), c) counter T hT,
      Nat.mul_zero, Nat.zero_add, Finset.univ_eq_empty, Finset.sum_empty, add_zero] using hh
  | succ s ih =>
    have ht := LargeCoverProgram.Support.expect_mono m bits (callback (labels 0) c)
      (fun reply => Cache.Correct bits reply.2) (hcb _ c hc)
      (fun reply => (Mean.scores callback s (Fin.tail labels) reply.2).evaluate m bits (clipped counter T))
      (fun _ => counter.work * (6 * s + 2 : ℕ) + ∑ j, price (Fin.tail labels j))
      (fun reply hr => ih (Fin.tail labels) reply.2 hr)
    simp only [Causal.expect, Code.evaluate_const] at ht
    have hh := (scores_clipped_step m bits callback s labels c counter T hT).trans
      (add_le_add (add_le_add (le_refl _) (hprice (labels 0) c hc)) ht)
    rw [Fin.sum_univ_succ]
    simp only [Causal.expect, Fin.tail_def] at hh
    push_cast
    push_cast at hh
    linarith

theorem afterSample_clipped {k s : ℕ} (m : M → ℝ) (bits : Q → Bool) (xi : ℝ)
    (callback : Mean.Callback M Q (Fin (k + 1))) (r : Sampler.Records Q k s)
    (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T) :
    (Mean.afterSample xi callback r).evaluate m bits (clipped counter T) ≤
      40 * counter.work + (Mean.selected (Sampler.Observation.ofRecords r)).elim 0
        (fun labels => (Mean.scores callback s labels r.store.cache).evaluate m bits (clipped counter T)) := by
  have hn (value : Mean.Result Q k s) :
      (Code.tick 7 (.tick 31 (.pure value)) : Code M Q _).evaluate m bits (clipped counter T) ≤
        40 * counter.work := by
    have hh := clipped_expect_le_counter m bits
      (Code.tick 7 (.tick 31 (.pure value)) : Code M Q _) counter T
    norm_num only [Code.evaluate, Causal.Counter.value, Outcome.add, Outcome.pure,
      Nat.cast_zero, Nat.cast_ofNat, mul_zero, add_zero] at hh
    convert hh using 1 <;> first | rfl | ring
  cases hl : r.labels with
  | none =>
    simpa only [Mean.afterSample, Mean.selected, Sampler.Observation.ofRecords, hl,
      ite_self, Option.elim_none, add_zero] using hn (Mean.finish xi r none r.store.cache)
  | some labels =>
    cases hs : r.successful
    · simpa only [Mean.afterSample, Mean.selected, Sampler.Observation.ofRecords, hl, hs,
        Bool.false_eq_true, ite_false, Option.elim_none, add_zero] using hn (Mean.finish xi r none r.store.cache)
    · have hb := clipped_bind_tick m bits (Mean.scores callback s labels r.store.cache)
        (fun z => Mean.finish xi r (some (z.1 / s)) z.2) 31 counter T hT
      have ho := clipped_tick m bits
        ((Mean.scores callback s labels r.store.cache).bind (fun z =>
          .tick 31 (.pure (Mean.finish xi r (some (z.1 / s)) z.2)))) 7 counter T
      have hh := ho.trans (add_le_add (le_refl _) hb)
      norm_num only [Nat.cast_ofNat] at hh
      have hres :
          (Code.tick 7 ((Mean.scores callback s labels r.store.cache).bind (fun z =>
            .tick 31 (.pure (Mean.finish xi r (some (z.1 / s)) z.2))))).evaluate m bits (clipped counter T) ≤
          40 * counter.work + (Mean.scores callback s labels r.store.cache).evaluate m bits (clipped counter T) := by
        linarith
      simpa only [Mean.afterSample, Mean.selected, Sampler.Observation.ofRecords, hl, hs,
        ite_true, Option.elim_some] using hres

theorem mean_clipped_cache {k : ℕ} (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1)))
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T)
    (price : Fin (k + 1) → ℝ) (hprice0 : ∀ u, 0 ≤ price u)
    (hprice : ∀ u c, Cache.Correct bits c →
      (callback u c).evaluate m bits (clipped counter T) ≤ price u)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (query u)).Nonempty) (xi : ℝ) :
    (Mean.program query root C s B c xi callback).evaluate m bits (clipped counter T) ≤
      (Sampler.program query root C s B c : Code M Q _).evaluate m bits counter.value +
        (6 * s + 42 : ℕ) * counter.work +
        s * (Covers.Rejection.uniformRetained (fun u => bits (query u)) hb).expect price := by
  let sample : Code M Q (Sampler.Records Q k s) := Sampler.program query root C s B c
  let mu := Covers.Rejection.uniformRetained (fun u => bits (query u)) hb
  let W : (Fin s → Fin (k + 1)) → ℝ :=
    fun labels => counter.work * (6 * s + 2 : ℕ) + ∑ j, price (labels j)
  have hW0 : ∀ labels, 0 ≤ W labels := by
    intro labels
    dsimp only [W]
    exact add_nonneg (mul_nonneg counter.work_nonneg (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => hprice0 _)
  have hselected :
      sample.evaluate m bits (fun o => (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 W) ≤
        counter.work * (6 * s + 2 : ℕ) + s * mu.expect price := by
    rw [Mean.sampler_selected_expect m bits query root C s B c hc (fun v => v.elim 0 W)]
    exact (Mean.cappedAccepted_expect_le _ hb root C s B W hW0).trans_eq (by
      dsimp only [W]
      rw [Law.expect_add, Law.expect_const, Mean.tape_sum_expect])
  have ha (r : Sampler.Records Q k s) (hr : Cache.Correct bits r.store.cache) :
      (Mean.afterSample xi callback r).evaluate m bits (clipped counter T) ≤
        40 * counter.work + (Mean.selected (Sampler.Observation.ofRecords r)).elim 0 W := by
    apply (afterSample_clipped m bits xi callback r counter T hT).trans
    apply add_le_add (le_refl _)
    cases he : Mean.selected (Sampler.Observation.ofRecords r) with
    | none => exact le_refl _
    | some labels => exact scores_clipped_cache m bits callback hcb counter T hT price hprice s labels _ hr
  have he := Mean.evaluate_mono_runs m bits sample
    (fun o => (Mean.afterSample xi callback o.value).evaluate m bits (clipped counter T))
    (fun o => 40 * counter.work + (Mean.selected (Sampler.Observation.ofRecords o.value)).elim 0 W)
    (fun o ho => ha o.value (Mean.sampler_cache_correct m bits query root C s B c hc o ho))
  rw [Code.evaluate_add, Code.evaluate_const] at he
  have hh := (clipped_bind_full m bits sample (Mean.afterSample xi callback) counter T hT).trans
    (add_le_add (le_refl _) (he.trans (add_le_add (le_refl _) hselected)))
  change (Mean.program query root C s B c xi callback).evaluate m bits (clipped counter T) ≤ _ at hh
  push_cast at hh ⊢
  linarith

/-- Incoming caches may depend on the complete sampled tape and prior calls.
The family bound controls their correct-cache supremum envelope. -/
theorem mean_family_clipped {k : ℕ} (m : M → ℝ) (bits : Q → Bool)
    (callback : Mean.Callback M Q (Fin (k + 1)))
    (hcb : ∀ u c, Cache.Correct bits c →
      Causal.Ensures m bits (callback u c) (fun reply => Cache.Correct bits reply.2))
    (counter : Causal.Counter) (T : ℝ) (hT : 0 ≤ T)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (query u)).Nonempty) (xi budget : ℝ)
    (hfamily : ∀ caches : Fin (k + 1) → Cache Q, (∀ u, Cache.Correct bits (caches u)) →
      (Covers.Rejection.uniformRetained (fun u => bits (query u)) hb).expect
        (fun u => (callback u (caches u)).evaluate m bits (clipped counter T)) ≤ budget) :
    (Mean.program query root C s B c xi callback).evaluate m bits (clipped counter T) ≤
      (Sampler.program query root C s B c : Code M Q _).evaluate m bits counter.value +
        (6 * s + 42 : ℕ) * counter.work + s * budget := by
  let f (u : Fin (k + 1)) (cache : Cache Q) :=
    (callback u cache).evaluate m bits (clipped counter T)
  let price := envelope (Cache.Correct bits) f
  have hup : ∀ u cache, Cache.Correct bits cache → f u cache ≤ T :=
    fun u cache _ => clipped_expect_le_ceiling m bits (callback u cache) counter T
  have hnonneg : ∀ u cache, Cache.Correct bits cache → 0 ≤ f u cache :=
    fun u cache _ => clipped_expect_nonneg m bits (callback u cache) counter T hT
  have hmean := envelope_expect_le
    (Covers.Rejection.uniformRetained (fun u => bits (query u)) hb)
    (Cache.Correct bits) f c hc T budget hup hfamily
  have hpoint : ∀ u cache, Cache.Correct bits cache →
      (callback u cache).evaluate m bits (clipped counter T) ≤ price u :=
    fun u cache hcache => le_envelope (Cache.Correct bits) f c hc T hup u cache hcache
  have hp0 : ∀ u, 0 ≤ price u :=
    envelope_nonneg (Cache.Correct bits) f c hc T hup hnonneg
  exact (mean_clipped_cache m bits callback hcb counter T hT price hp0 hpoint
    query root C s B c hc hb xi).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg _)))

end SteinerUpperBound.SavingEstimator.Resources

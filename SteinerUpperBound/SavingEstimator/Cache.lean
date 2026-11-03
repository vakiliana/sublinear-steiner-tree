module

public import SteinerUpperBound.SavingEstimator.Confidence

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator

open SteinerLowerBound EstimatorParameters QueryProgram Matching.Padded
open scoped Classical

variable {Q : Type} {n k : ℕ}

theorem fromParameters_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : PublicParameters) (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits (fromParameters terminals root key a p c)
      (fun r => Cache.Correct bits r.cache) := by
  apply LargeCoverProgram.Support.ensures_bind_evaluates I.weight bits (configure n (k + 1) p) _ _
    (configure_evaluates I.weight bits n (k + 1) p)
  apply LargeCoverProgram.Support.ensures_tick
  exact LargeCoverProgram.program_concrete_cache_ensures I bits (configuration n (k + 1) p)
    terminals root key a hT hnd c hc

theorem fromParameters_cache_failure_zero (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : PublicParameters) (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (fromParameters terminals root key a p c).evaluate I.weight bits
      (fun o => if Cache.Correct bits o.value.cache then 0 else 1) = 0 :=
  fromParameters_cache_ensures I bits terminals root key a p hT hnd c hc
    (fun r => if Cache.Correct bits r.cache then 0 else 1) (fun r hr => by simp [hr])

theorem fromParameters_cache_on_support (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : PublicParameters) (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (seed : ((fromParameters terminals root key a p c).compile I.weight).Seed)
    (hmass : 0 < ((fromParameters terminals root key a p c).compile I.weight).law.mass seed) :
    Cache.Correct bits
      ((((fromParameters terminals root key a p c).compile I.weight).tree seed).output bits).value.cache := by
  let code := fromParameters terminals root key a p c
  have hz := fromParameters_cache_failure_zero I bits terminals root key a p hT hnd c hc
  rw [← Code.compile_expect] at hz
  change (code.compile I.weight).law.expect
    (fun s => if Cache.Correct bits (((code.compile I.weight).tree s).output bits).value.cache then 0 else 1) = 0 at hz
  by_contra hn
  have hns : ¬ Cache.Correct bits (((code.compile I.weight).tree seed).output bits).value.cache := hn
  have hterm :
      (code.compile I.weight).law.mass seed *
        (if Cache.Correct bits (((code.compile I.weight).tree seed).output bits).value.cache then (0 : ℝ) else 1) ≤ 0 := by
    calc
      _ ≤ (code.compile I.weight).law.expect
          (fun s => if Cache.Correct bits (((code.compile I.weight).tree s).output bits).value.cache then 0 else 1) := by
        unfold Law.expect
        apply Finset.single_le_sum _ (Finset.mem_univ seed)
        intro s _
        apply mul_nonneg ((code.compile I.weight).law.nonneg s)
        split_ifs <;> norm_num
      _ = 0 := hz
  simp only [hns, ite_false, mul_one] at hterm
  exact (not_le_of_gt hmass) hterm

def GoodAnswer (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (r : LargeCoverProgram.Answer Q n) : Prop :=
  Cache.Correct bits r.cache ∧
    LargeCoverProgram.GoodSaving (saving I bits key a) (retainedCount bits terminals key) (eps n) r.value

private noncomputable def indicator {R : Type*} (P : R → Prop) (r : R) : ℝ :=
  if P r then 1 else 0

theorem fromParameters_good_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (c : Cache Q) (hc : Cache.Correct bits c)
    (hroot : bits (key (terminals.get root)) = true) :
    1 - 4 * beta n ≤ Code.valueProbability I.weight bits
      (fromParameters terminals root key a (parameters n (k + 1)) c)
      (GoodAnswer I bits terminals key a) := by
  let code := fromParameters terminals root key a (parameters n (k + 1)) c
  let S := fun r : LargeCoverProgram.Answer Q n =>
    LargeCoverProgram.GoodSaving (saving I bits key a) (retainedCount bits terminals key) (eps n) r.value
  have hcache := fromParameters_cache_ensures I bits terminals root key a (parameters n (k + 1)) hT hnd c hc
  have hz := hcache (fun r => indicator (GoodAnswer I bits terminals key a) r - indicator S r) (by
    intro r hr
    by_cases hs : S r <;> simp [indicator, GoodAnswer, hr, S] at hs ⊢)
  change code.evaluate I.weight bits (fun o =>
    indicator (GoodAnswer I bits terminals key a) o.value - indicator S o.value) = 0 at hz
  rw [Code.evaluate_sub] at hz
  change Code.valueProbability I.weight bits code (GoodAnswer I bits terminals key a) -
    Code.valueProbability I.weight bits code S = 0 at hz
  have hs := fromParameters_saving_confidence I bits terminals root key a hT hnd c hc hroot
  linarith

end SteinerUpperBound.SavingEstimator

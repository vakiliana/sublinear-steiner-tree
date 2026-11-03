module

public import SteinerUpperBound.SavingEstimator.Clocked.Program

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator.Clocked

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical

variable {Q : Type}

private noncomputable def bad {R : Type*} (P : R → Prop) (r : R) : ℝ :=
  if P r then 0 else 1

private theorem bad_nonneg {R : Type*} (P : R → Prop) (r : R) : 0 ≤ bad P r := by
  unfold bad
  split_ifs <;> norm_num

private theorem support_of_zero_bad {Ω : Type*} [Fintype Ω] (μ : Law Ω) (P : Ω → Prop)
    (hz : μ.expect (bad P) = 0) (s : Ω) (hs : 0 < μ.mass s) : P s := by
  by_contra hn
  have hterm : μ.mass s * bad P s ≤ 0 := by
    calc
      _ ≤ μ.expect (bad P) := by
        unfold Law.expect
        exact Finset.single_le_sum (fun t _ => mul_nonneg (μ.nonneg t) (bad_nonneg P t))
          (Finset.mem_univ s)
      _ = 0 := hz
  simp only [bad, hn, ite_false, mul_one] at hterm
  exact (not_le_of_gt hs) hterm

private theorem neg_probability {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop) :
    Code.valueProbability m bits p (fun r => ¬ P r) =
      p.evaluate m bits (fun o => bad P o.value) := by
  unfold Code.valueProbability
  apply congrArg (p.evaluate m bits)
  funext o
  by_cases hp : P o.value <;> simp [bad, hp]

private theorem ensures_of_zero_bad {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop)
    (hz : Code.valueProbability m bits p (fun r => ¬ P r) = 0) : Causal.Ensures m bits p P := by
  rw [neg_probability, ← Code.compile_expect] at hz
  change (p.compile m).law.expect
    (bad (fun s => P ((((p.compile m).tree s).output bits).value))) = 0 at hz
  intro F hF
  unfold Causal.expect
  rw [← Code.compile_expect]
  unfold Compiled.expect Law.expect
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : (p.compile m).law.mass s = 0
  · simp only [hs, zero_mul]
  · have hm : 0 < (p.compile m).law.mass s :=
      lt_of_le_of_ne ((p.compile m).law.nonneg s) (Ne.symm hs)
    have hp := support_of_zero_bad (p.compile m).law _ hz s hm
    simp only [hF _ hp, mul_zero]

def SafeNested {R : Type*} (P : R → Prop) : Option (Option R) → Prop
  | none => True
  | some none => True
  | some (some r) => P r

private theorem clock_ensures {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop) (hP : Causal.Ensures m bits p P)
    (bd : EstimatorClocks.Budget) :
    Causal.Ensures m bits (EstimatorClocks.clocked bd p) (SafeNested P) := by
  have hz : p.evaluate m bits (fun o => bad P o.value) = 0 :=
    hP (bad P) (fun r hr => by simp [bad, hr])
  have he : (fun r => ¬ SafeNested P r) = Code.SomeGood (Code.SomeGood (fun r => ¬ P r)) := by
    funext r
    apply propext
    cases r with
    | none => simp [SafeNested, Code.SomeGood]
    | some r => cases r <;> simp [SafeNested, Code.SomeGood]
  apply ensures_of_zero_bad
  apply le_antisymm _ (Code.valueProbability_nonneg _ _ _ _)
  rw [he, EstimatorClocks.clocked, Code.clock_success_eq]
  calc
    _ ≤ p.evaluate m bits (fun o => bad P o.value) := by
      apply Code.evaluate_mono
      intro o
      by_cases hp : P o.value <;>
        by_cases hd : o.positiveReplies ≤ bd.disclosureBudget <;>
        by_cases hw : (Code.disclosureTax o).work ≤ bd.workBudget <;> simp [bad, hp, hd, hw]
    _ = 0 := hz

variable {n k : ℕ}

def CacheSafe (bits : Q → Bool) : Option (ℝ × Cache Q) → Prop
  | none => True
  | some r => Cache.Correct bits r.2

theorem flatten_cache (bits : Q → Bool) (r : Option (Option (LargeCoverProgram.Answer Q n)))
    (hr : SafeNested (fun answer => Cache.Correct bits answer.cache) r) :
    CacheSafe bits (flatten r) := by
  cases r with
  | none => trivial
  | some r =>
    cases r with
    | none => trivial
    | some answer =>
      cases hv : answer.value <;> simp only [flatten, Option.join_some, Option.bind_some, hv,
        Option.map_none, Option.map_some, CacheSafe]; trivial

theorem fromParameters_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Causal.Ensures I.weight bits (fromParameters terminals root key a p AW AP cache) (CacheSafe bits) := by
  apply LargeCoverProgram.Support.ensures_bind_evaluates I.weight bits
    (EstimatorClocks.fromParametersProgram p AW AP) _ _ (setup_evaluates I.weight bits p AW AP)
  unfold afterBudget
  apply LargeCoverProgram.Support.ensures_bind I.weight bits _ _
    (SafeNested (fun answer => Cache.Correct bits answer.cache)) _
    (clock_ensures I.weight bits _ _ (SavingEstimator.fromParameters_cache_ensures I bits
      terminals root key a p hT hnd cache hc) (budget p AW AP))
  intro r hr
  apply LargeCoverProgram.Support.ensures_tick
  exact LargeCoverProgram.Support.ensures_pure I.weight bits _ _ (flatten_cache bits r hr)

theorem fromParameters_cache_failure_zero (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (p : EstimatorParameters.PublicParameters) (AW AP : ℕ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Code.valueProbability I.weight bits (fromParameters terminals root key a p AW AP cache)
      (fun r => ¬ CacheSafe bits r) = 0 := by
  rw [neg_probability]
  exact fromParameters_cache_ensures I bits terminals root key a p AW AP hT hnd cache hc
    (bad (CacheSafe bits)) (fun r hr => by simp [bad, hr])

end SteinerUpperBound.SavingEstimator.Clocked

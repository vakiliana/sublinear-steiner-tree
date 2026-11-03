module

public import SteinerUpperBound.SavingEstimator.Clocked.Program

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.SavingEstimator.Clocked

open SteinerLowerBound EstimatorParameters QueryProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

def GoodReply (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (r : Option (ℝ × Cache Q)) : Prop :=
  ∃ Z c, r = some (Z, c) ∧ Cache.Correct bits c ∧ 0 ≤ Z ∧ Z ≤ saving I bits key a ∧
    saving I bits key a / 2 - eps n * retainedCount bits terminals key ≤ Z

theorem flatten_good (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (r : Option (Option (LargeCoverProgram.Answer Q n)))
    (h : Code.SomeGood (Code.SomeGood (GoodAnswer I bits terminals key a)) r) :
    GoodReply I bits terminals key a (flatten r) := by
  obtain ⟨inner, rfl, answer, rfl, hc, Z, hv, h₀, h₁, hl⟩ := h
  refine ⟨Z, answer.cache, ?_, hc, h₀, h₁, hl⟩
  simp only [flatten, Option.join_some, Option.bind_some, hv, Option.map_some]

private theorem value_mono {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P T : R → Prop) (h : ∀ r, P r → T r) :
    Code.valueProbability m bits p P ≤ Code.valueProbability m bits p T := by
  unfold Code.valueProbability
  apply Code.evaluate_mono
  intro o
  by_cases hp : P o.value
  · simp [hp, h o.value hp]
  · by_cases ht : T o.value <;> simp [hp, ht]

private theorem seed_probability {M R : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (P : R → Prop) :
    (p.compile m).law.prob {s | P ((((p.compile m).tree s).output bits).value)} =
      Code.valueProbability m bits p P := by
  unfold Code.valueProbability
  rw [← Code.compile_expect, Law.prob_eq_expect]
  rfl

private noncomputable def truncated {Ω : Type*} (P : Ω → Prop) (f : Ω → ℝ) (s : Ω) : ℝ :=
  if P s then f s else 0

private theorem restrict_expectation {Ω : Type*} [Fintype Ω] (μ : Law Ω)
    (G A : Ω → Prop) (f : Ω → ℝ) (hf : ∀ s, 0 ≤ f s) :
    μ.expect (truncated (fun s => G s ∧ A s) f) ≤ μ.expect (truncated G f) := by
  apply Law.expect_mono
  intro s
  by_cases hg : G s <;> by_cases ha : A s <;> simp only [truncated, hg, ha, and_self, false_and,
    and_false, ite_true, ite_false] <;> first | exact le_rfl | exact hf s

theorem fromParameters_success (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (AW AP : ℕ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hroot : bits (key (terminals.get root)) = true)
    (Good : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).Seed → Prop) (δ : ℝ)
    (hbad : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.prob {s | ¬ Good s} ≤ δ)
    (hwork : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.expect (fun s => if Good s then
        (((((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
          I.weight).tree s).output bits).work : ℝ) else 0) ≤ AW)
    (hpositive : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.expect (fun s => if Good s then
        (((((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
          I.weight).tree s).output bits).positiveReplies : ℝ) else 0) ≤ AP) :
    let bd := EstimatorClocks.stage n AW AP
    1 - 4 * beta n - δ - 4 * (AW : ℝ) / (bd.workBudget + 1 : ℕ) -
        (AP : ℝ) / (bd.disclosureBudget + 1 : ℕ) ≤
      Code.valueProbability I.weight bits
        (fromParameters terminals root key a (parameters n (k + 1)) AW AP cache)
        (GoodReply I bits terminals key a) := by
  dsimp only
  let raw := SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache
  let compiled := raw.compile I.weight
  let Accurate := fun s : compiled.Seed =>
    GoodAnswer I bits terminals key a ((compiled.tree s).output bits).value
  let G := fun s : compiled.Seed => Good s ∧ Accurate s
  have hacc : compiled.law.prob {s | ¬ Accurate s} ≤ 4 * beta n := by
    have hs := SavingEstimator.fromParameters_good_confidence I bits terminals root key a hT hnd cache hc hroot
    have he := compiled.law.prob_compl {s | Accurate s}
    have hp : compiled.law.prob {s | Accurate s} =
        Code.valueProbability I.weight bits raw (GoodAnswer I bits terminals key a) :=
      seed_probability I.weight bits raw _
    change compiled.law.prob {s | ¬ Accurate s} = 1 - compiled.law.prob {s | Accurate s} at he
    rw [hp] at he
    linarith
  have hGbad : compiled.law.prob {s | ¬ G s} ≤ δ + 4 * beta n := by
    have he : {s | ¬ G s} = {s | ¬ Good s} ∪ {s | ¬ Accurate s} := by
      ext s
      change (¬ (Good s ∧ Accurate s)) ↔ (¬ Good s ∨ ¬ Accurate s)
      exact not_and_or
    rw [he]
    exact (Law.prob_union_le _ _ _).trans (add_le_add hbad hacc)
  have hwG : compiled.law.expect (truncated G
      (fun s => (((compiled.tree s).output bits).work : ℝ))) ≤ AW := by
    have h := restrict_expectation compiled.law Good Accurate
      (fun s => (((compiled.tree s).output bits).work : ℝ)) (fun _ => Nat.cast_nonneg _)
    exact h.trans hwork
  have hpG : compiled.law.expect (truncated G
      (fun s => (((compiled.tree s).output bits).positiveReplies : ℝ))) ≤ AP := by
    have h := restrict_expectation compiled.law Good Accurate
      (fun s => (((compiled.tree s).output bits).positiveReplies : ℝ)) (fun _ => Nat.cast_nonneg _)
    exact h.trans hpositive
  have hclock := Code.clock_success_of_good I.weight bits raw
    (EstimatorClocks.stage n AW AP).workBudget (EstimatorClocks.stage n AW AP).disclosureBudget
    (GoodAnswer I bits terminals key a) G (δ + 4 * beta n) AW AP hGbad
    (fun s hs => hs.2) hwG hpG
  have hm := value_mono I.weight bits (EstimatorClocks.clocked (EstimatorClocks.stage n AW AP) raw)
    (Code.SomeGood (Code.SomeGood (GoodAnswer I bits terminals key a)))
    (fun r => GoodReply I bits terminals key a (flatten r))
    (flatten_good I bits terminals key a)
  rw [fromParameters_valueProbability, budget_public]
  change _ ≤ Code.valueProbability I.weight bits
    (EstimatorClocks.clocked (EstimatorClocks.stage n AW AP) raw)
    (fun r => GoodReply I bits terminals key a (flatten r))
  calc
    _ = 1 - (δ + 4 * beta n) - 4 * (AW : ℝ) / ((EstimatorClocks.stage n AW AP).workBudget + 1 : ℕ) -
        (AP : ℝ) / ((EstimatorClocks.stage n AW AP).disclosureBudget + 1 : ℕ) := by ring
    _ ≤ _ := hclock
    _ ≤ _ := hm

theorem fromParameters_success_byHeight (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (AW AP : ℕ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hroot : bits (key (terminals.get root)) = true)
    (Good : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).Seed → Prop) (δ : ℝ)
    (hbad : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.prob {s | ¬ Good s} ≤ δ)
    (hwork : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.expect (fun s => if Good s then
        (((((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
          I.weight).tree s).output bits).work : ℝ) else 0) ≤ AW)
    (hpositive : ((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
      I.weight).law.expect (fun s => if Good s then
        (((((SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).compile
          I.weight).tree s).output bits).positiveReplies : ℝ) else 0) ≤ AP) :
    1 - 4 * beta n - δ - 5 / (EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1)) ≤
      Code.valueProbability I.weight bits
        (fromParameters terminals root key a (parameters n (k + 1)) AW AP cache)
        (GoodReply I bits terminals key a) := by
  have h := fromParameters_success I bits terminals root key a hT hnd AW AP cache hc hroot Good δ
    hbad hwork hpositive
  have hl := EstimatorClocks.byHeight_loss (heightBudget n) AW AP
  dsimp only [EstimatorClocks.stage] at h
  change _ ≤ Code.valueProbability I.weight bits
    (fromParameters terminals root key a (parameters n (k + 1)) AW AP cache)
    (GoodReply I bits terminals key a)
  change _ + _ ≤ _ at hl
  linarith

end SteinerUpperBound.SavingEstimator.Clocked

module

public import SteinerUpperBound.EstimatorClocks.Selection

@[expose] public section

namespace SteinerUpperBound.EstimatorClocks

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q R : Type*}

theorem byHeight_success_of_good (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (height workAccount positiveAccount : ℕ) (P : R → Prop)
    (Good : (p.compile m).Seed → Prop) (delta : ℝ)
    (hbad : (p.compile m).law.prob {s | ¬ Good s} ≤ delta)
    (hsound : ∀ s, Good s → P ((((p.compile m).tree s).output bits).value))
    (hwork : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).work : ℝ) else 0) ≤ workAccount)
    (hpositive : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).positiveReplies : ℝ) else 0) ≤ positiveAccount) :
    1 - delta - 5 / (amplification * ((height : ℝ) + 1)) ≤
      Code.valueProbability m bits (clocked (byHeight height workAccount positiveAccount) p)
        (Code.SomeGood (Code.SomeGood P)) := by
  have h := Code.clock_success_of_good m bits p
    (byHeight height workAccount positiveAccount).workBudget
    (byHeight height workAccount positiveAccount).disclosureBudget
    P Good delta workAccount positiveAccount hbad hsound hwork hpositive
  have hl := byHeight_loss height workAccount positiveAccount
  change _ ≤ Code.valueProbability m bits
    ((p.disclosureCap (byHeight height workAccount positiveAccount).disclosureBudget).cap
      (byHeight height workAccount positiveAccount).workBudget) _
  linarith

theorem stage_success_of_good (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (n workAccount positiveAccount : ℕ) (P : R → Prop)
    (Good : (p.compile m).Seed → Prop)
    (hbad : (p.compile m).law.prob {s | ¬ Good s} ≤ EstimatorParameters.beta n)
    (hsound : ∀ s, Good s → P ((((p.compile m).tree s).output bits).value))
    (hwork : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).work : ℝ) else 0) ≤ workAccount)
    (hpositive : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).positiveReplies : ℝ) else 0) ≤ positiveAccount) :
    1 - stageLoss n ≤ Code.valueProbability m bits (clocked (stage n workAccount positiveAccount) p)
      (Code.SomeGood (Code.SomeGood P)) := by
  have h := byHeight_success_of_good m bits p (EstimatorParameters.heightBudget n)
    workAccount positiveAccount P Good (EstimatorParameters.beta n) hbad hsound hwork hpositive
  simpa only [stage, stageLoss, sub_add_eq_sub_sub] using h

theorem finite_stage_losses {J : Type*} (n : ℕ) (s : Finset J) (loss : J → ℝ)
    (hc : s.card ≤ EstimatorParameters.heightBudget n)
    (hl : ∀ j ∈ s, loss j ≤ stageLoss n) :
    ∑ j ∈ s, loss j ≤ 51 / 1000000 := by
  calc
    _ ≤ ∑ _j ∈ s, stageLoss n := Finset.sum_le_sum hl
    _ = (s.card : ℝ) * stageLoss n := by simp
    _ ≤ _ := summed_stage_loss n s.card hc

theorem clocked_expected_resources (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (budget : Budget) :
    (clocked budget p).evaluate m bits (fun o => (o.work : ℝ)) ≤ budget.workBudget ∧
      (clocked budget p).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ budget.disclosureBudget + 1 :=
  Code.clock_expected_resources m bits p budget.workBudget budget.disclosureBudget

theorem factory_success_of_good (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (k workAccount positiveAccount : ℕ) (hk : 0 < k) (P : R → Prop)
    (Good : (p.compile m).Seed → Prop) (delta : ℝ)
    (hbad : (p.compile m).law.prob {s | ¬ Good s} ≤ delta)
    (hsound : ∀ s, Good s → P ((((p.compile m).tree s).output bits).value))
    (hwork : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).work : ℝ) else 0) ≤ workAccount)
    (hpositive : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).positiveReplies : ℝ) else 0) ≤ positiveAccount) :
    1 - delta - 1 / 20000 ≤
      Code.valueProbability m bits (clocked (factory k workAccount positiveAccount).clock p)
        (Code.SomeGood (Code.SomeGood P)) := by
  have h := Code.clock_success_of_good m bits p
    (factory k workAccount positiveAccount).clock.workBudget
    (factory k workAccount positiveAccount).clock.disclosureBudget
    P Good delta workAccount positiveAccount hbad hsound hwork hpositive
  have hr := factory_ratios k workAccount positiveAccount
  have hden : (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) ≤
      (((factory k workAccount positiveAccount).clock.disclosureBudget + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_right (factory_disclosure_ge_threshold k workAccount positiveAccount hk) 1
  have hdp : (0 : ℝ) < (((factory k workAccount positiveAccount).clock.disclosureBudget + 1 : ℕ) : ℝ) := by
    positivity
  have hap : (0 : ℝ) < (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) := by
    positivity
  have hp : (positiveAccount : ℝ) /
      (((factory k workAccount positiveAccount).clock.disclosureBudget + 1 : ℕ) : ℝ) ≤
      (positiveAccount : ℝ) / (((factory k workAccount positiveAccount).positiveThreshold + 1 : ℕ) : ℝ) :=
    (div_le_div_iff₀ hdp hap).mpr
      (mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg positiveAccount))
  change _ ≤ Code.valueProbability m bits
    ((p.disclosureCap (factory k workAccount positiveAccount).clock.disclosureBudget).cap
      (factory k workAccount positiveAccount).clock.workBudget) _
  linarith

end SteinerUpperBound.EstimatorClocks

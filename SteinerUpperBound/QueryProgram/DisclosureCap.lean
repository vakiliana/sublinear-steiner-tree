module

public import SteinerUpperBound.QueryProgram.Failure

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q R : Type*}

def disclosureCap (budget : ℕ) : Code M Q R → Code M Q (Option R)
  | .pure r => .pure (some r)
  | .metric q next => .metric q (fun a => (next a).disclosureCap budget)
  | .retained q next => .tick 2 (.retained q (fun
      | true => match budget with
        | 0 => .pure none
        | d + 1 => (next true).disclosureCap d
      | false => (next false).disclosureCap budget))
  | .uniform n next => .uniform n (fun a => (next a).disclosureCap budget)
  | .coin rate next => .coin rate (fun a => (next a).disclosureCap budget)
  | .tick n next => .tick n (next.disclosureCap budget)

def disclosureTax (o : Outcome R) : Outcome R :=
  ⟨o.value, o.work + 3 * o.retentionQueries, o.metricQueries, o.retentionQueries, o.positiveReplies⟩

noncomputable def onSome (F : Outcome R → ℝ) (o : Outcome (Option R)) : ℝ :=
  o.value.elim 0 (fun r => F ⟨r, o.work, o.metricQueries, o.retentionQueries, o.positiveReplies⟩)

theorem onSome_add (F : Outcome R → ℝ) (o : Outcome (Option R)) (w m q z : ℕ) :
    onSome F (o.add w m q z) = onSome (fun a => F (a.add w m q z)) o := by
  cases o with
  | mk value work metric retention positive => cases value <;> rfl

theorem disclosureTax_add (o : Outcome R) (w m q z : ℕ) :
    disclosureTax (o.add w m q z) = (disclosureTax o).add (w + 3 * q) m q z := by
  cases o
  simp only [disclosureTax, Outcome.add]
  congr 1 <;> omega

theorem add_add (o : Outcome R) (w m q z w' m' q' z' : ℕ) :
    (o.add w m q z).add w' m' q' z' = o.add (w' + w) (m' + m) (q' + q) (z' + z) := by
  cases o
  simp only [Outcome.add, Nat.add_assoc]

theorem disclosureCap_expect (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) (F : Outcome R → ℝ) :
    (p.disclosureCap budget).evaluate m bits (onSome F) =
      p.evaluate m bits (fun o => if o.positiveReplies ≤ budget then F (disclosureTax o) else 0) := by
  induction p generalizing budget F with
  | pure r => simp [disclosureCap, evaluate, onSome, Outcome.pure, disclosureTax]
  | metric q next ih =>
      simp only [disclosureCap, evaluate]
      simp_rw [onSome_add, disclosureTax_add]
      simpa only [Outcome.add, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
        ih (m q) budget (fun a => F (a.add 1 1 0 0))
  | retained q next ih =>
      cases hb : bits q with
      | false =>
          simp only [disclosureCap, evaluate, hb, Bool.false_eq_true, ite_false]
          simp_rw [add_add, onSome_add, disclosureTax_add]
          simpa only [Outcome.add, Nat.zero_add, Nat.mul_one, Nat.add_zero, Nat.reduceAdd] using
            ih false budget (fun a => F (a.add 4 0 1 0))
      | true =>
          cases budget with
          | zero =>
              simp [disclosureCap, evaluate, hb, onSome, Outcome.add, Outcome.pure, evaluate_const]
          | succ budget =>
              have ht (z : ℕ) : 1 + z ≤ budget + 1 ↔ z ≤ budget := by omega
              simp only [disclosureCap, evaluate, hb, ite_true]
              simp_rw [add_add, onSome_add, disclosureTax_add]
              simpa only [Outcome.add, ht, Nat.zero_add, Nat.mul_one, Nat.add_zero, Nat.reduceAdd] using
                ih true budget (fun a => F (a.add 4 0 1 1))
  | uniform n next ih =>
      simp only [disclosureCap, evaluate]
      apply congrArg (Law.uniform (Fin (n + 1))).expect
      funext a
      simp_rw [onSome_add, disclosureTax_add]
      simpa only [Outcome.add, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
        ih a budget (fun o => F (o.add 1 0 0 0))
  | coin rate next ih =>
      simp only [disclosureCap, evaluate]
      apply congrArg (CategoricalCoupling.bernoulli rate).expect
      funext a
      simp_rw [onSome_add, disclosureTax_add]
      simpa only [Outcome.add, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
        ih a budget (fun o => F (o.add 2 0 0 0))
  | tick n next ih =>
      simp only [disclosureCap, evaluate]
      simp_rw [onSome_add, disclosureTax_add]
      simpa only [Outcome.add, Nat.zero_add, Nat.mul_zero, Nat.add_zero] using
        ih budget (fun o => F (o.add (n + 1) 0 0 0))

theorem disclosureCap_positive (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) :
    ∀ s : ((p.disclosureCap budget).compile m).Seed,
      ((((p.disclosureCap budget).compile m).tree s).output bits).positiveReplies ≤ budget + 1 := by
  induction p generalizing budget with
  | pure r =>
      intro s
      exact Nat.zero_le _
  | metric q next ih =>
      intro s
      simpa only [disclosureCap, compile, Compiled.map, DecisionTree.output_map, Outcome.add,
        Nat.zero_add] using ih (m q) budget s
  | retained q next ih =>
      intro s
      cases hb : bits q with
      | false =>
          have h := ih false budget s.1
          simpa only [disclosureCap, compile, Compiled.map, DecisionTree.output_map,
            Compiled.query, DecisionTree.output, hb, Bool.false_eq_true, ite_false,
            Outcome.add, Nat.zero_add] using h
      | true =>
          cases budget with
          | zero =>
              simp only [disclosureCap, compile, Compiled.map, DecisionTree.output_map,
                Compiled.query, DecisionTree.output, hb, ite_true, Compiled.leaf,
                Outcome.add, Outcome.pure]
              omega
          | succ budget =>
              have h := ih true budget s.2
              simp only [disclosureCap, compile, Compiled.map, DecisionTree.output_map,
                Compiled.query, DecisionTree.output, hb, ite_true, Outcome.add, Nat.zero_add]
              omega
  | uniform n next ih =>
      intro s
      simpa only [disclosureCap, compile, Compiled.map, Compiled.choose, DecisionTree.output_map,
        Outcome.add, Nat.zero_add] using ih s.1 budget s.2
  | coin rate next ih =>
      intro s
      simpa only [disclosureCap, compile, Compiled.map, Compiled.choose, DecisionTree.output_map,
        Outcome.add, Nat.zero_add] using ih s.1 budget s.2
  | tick n next ih =>
      intro s
      simpa only [disclosureCap, compile, Compiled.map, DecisionTree.output_map,
        Outcome.add, Nat.zero_add] using ih budget s

theorem disclosureCap_expected_positive (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (budget : ℕ) :
    (p.disclosureCap budget).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ budget + 1 := by
  rw [← compile_expect]
  apply (Law.expect_mono _ (fun s => ?_)).trans_eq (Law.expect_const _ _)
  change (((((p.disclosureCap budget).compile m).tree s).output bits).positiveReplies : ℝ) ≤
    (budget : ℝ) + 1
  exact_mod_cast disclosureCap_positive m bits p budget s

theorem clock_success_eq (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (workBudget disclosureBudget : ℕ) (P : R → Prop) :
    valueProbability m bits ((p.disclosureCap disclosureBudget).cap workBudget)
        (SomeGood (SomeGood P)) =
      p.evaluate m bits (fun o => if o.positiveReplies ≤ disclosureBudget then
        if (disclosureTax o).work ≤ workBudget then (if P o.value then 1 else 0) else 0 else 0) := by
  have he :
      (fun o : Outcome (Option R) =>
        if o.work ≤ workBudget then (if SomeGood P o.value then (1 : ℝ) else 0) else 0) =
      onSome (fun o => if o.work ≤ workBudget then (if P o.value then 1 else 0) else 0) := by
    funext o
    cases h : o.value <;> simp [onSome, h, SomeGood]
  rw [cap_success_eq, he, disclosureCap_expect]
  rfl

theorem cap_expected_work (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R) (budget : ℕ) :
    (p.cap budget).evaluate m bits (fun o => (o.work : ℝ)) ≤ budget := by
  rw [← compile_expect]
  apply (Law.expect_mono _ (fun s => ?_)).trans_eq (Law.expect_const _ _)
  change (((((p.cap budget).compile m).tree s).output bits).work : ℝ) ≤ (budget : ℝ)
  exact_mod_cast cap_work m bits p budget s

theorem clock_expected_resources (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (workBudget disclosureBudget : ℕ) :
    ((p.disclosureCap disclosureBudget).cap workBudget).evaluate m bits
        (fun o => (o.work : ℝ)) ≤ workBudget ∧
      ((p.disclosureCap disclosureBudget).cap workBudget).evaluate m bits
        (fun o => (o.positiveReplies : ℝ)) ≤ disclosureBudget + 1 := by
  constructor
  · exact cap_expected_work m bits _ _
  · exact (cap_positive_mono m bits _ _ (fun z => (z : ℝ))
      (fun _ _ h => Nat.cast_le.mpr h)).trans
      (disclosureCap_expected_positive m bits p disclosureBudget)

theorem disclosureTax_truncated_work (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (Good : (p.compile m).Seed → Prop) :
    (p.compile m).law.expect (fun s =>
        if Good s then ((disclosureTax (((p.compile m).tree s).output bits)).work : ℝ) else 0) ≤
      4 * (p.compile m).law.expect (fun s =>
        if Good s then ((((p.compile m).tree s).output bits).work : ℝ) else 0) := by
  rw [← Law.expect_const_mul]
  apply Law.expect_mono
  intro s
  by_cases hg : Good s
  · simp only [hg, ite_true]
    have h := accounted m bits p s
    have hn : (disclosureTax (((p.compile m).tree s).output bits)).work ≤
        4 * (((p.compile m).tree s).output bits).work := by
      dsimp only [disclosureTax]
      omega
    exact_mod_cast hn
  · simp only [hg, ite_false, mul_zero, le_refl]

theorem clock_success_of_good (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (workBudget disclosureBudget : ℕ) (P : R → Prop)
    (Good : (p.compile m).Seed → Prop) (delta workAccount disclosureAccount : ℝ)
    (hbad : (p.compile m).law.prob {s | ¬ Good s} ≤ delta)
    (hsound : ∀ s, Good s → P ((((p.compile m).tree s).output bits).value))
    (hwork : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).work : ℝ) else 0) ≤ workAccount)
    (hpositive : (p.compile m).law.expect (fun s =>
      if Good s then ((((p.compile m).tree s).output bits).positiveReplies : ℝ) else 0) ≤
        disclosureAccount) :
    1 - delta - 4 * workAccount / (workBudget + 1 : ℕ) -
        disclosureAccount / (disclosureBudget + 1 : ℕ) ≤
      valueProbability m bits ((p.disclosureCap disclosureBudget).cap workBudget)
        (SomeGood (SomeGood P)) := by
  let c := p.compile m
  let taxed := fun s : c.Seed =>
    if Good s then ((disclosureTax ((c.tree s).output bits)).work : ℝ) else 0
  let positive := fun s : c.Seed =>
    if Good s then ((((c.tree s).output bits).positiveReplies : ℕ) : ℝ) else 0
  let success := fun s : c.Seed =>
    if ((c.tree s).output bits).positiveReplies ≤ disclosureBudget then
      if (disclosureTax ((c.tree s).output bits)).work ≤ workBudget then
        (if P (((c.tree s).output bits).value) then (1 : ℝ) else 0) else 0 else 0
  have hwp : (0 : ℝ) < ((workBudget + 1 : ℕ) : ℝ) := by positivity
  have hdp : (0 : ℝ) < ((disclosureBudget + 1 : ℕ) : ℝ) := by positivity
  have ht := (disclosureTax_truncated_work m bits p Good).trans
    (mul_le_mul_of_nonneg_left hwork (by norm_num : (0 : ℝ) ≤ 4))
  have point (s : c.Seed) :
      (if Good s then (1 : ℝ) else 0) - taxed s / (workBudget + 1 : ℕ) -
          positive s / (disclosureBudget + 1 : ℕ) ≤ success s := by
    have hw0 : 0 ≤ taxed s / (workBudget + 1 : ℕ) := by
      apply div_nonneg _ hwp.le
      dsimp only [taxed]
      split_ifs <;> positivity
    have hd0 : 0 ≤ positive s / (disclosureBudget + 1 : ℕ) := by
      apply div_nonneg _ hdp.le
      dsimp only [positive]
      split_ifs <;> positivity
    by_cases hg : Good s
    · have hp : P (((c.tree s).output bits).value) := hsound s hg
      by_cases hd : ((c.tree s).output bits).positiveReplies ≤ disclosureBudget
      · by_cases hw : (disclosureTax ((c.tree s).output bits)).work ≤ workBudget
        · simp only [success, hd, hw, hp, hg, ite_true]
          linarith
        · have hn : ((workBudget + 1 : ℕ) : ℝ) ≤
              ((disclosureTax ((c.tree s).output bits)).work : ℝ) := by exact_mod_cast (by omega)
          have h1 : 1 ≤ taxed s / (workBudget + 1 : ℕ) := by
            rw [le_div_iff₀ hwp]
            simpa only [taxed, hg, ite_true, one_mul] using hn
          simp only [success, hd, hw, hg, ite_true, ite_false]
          linarith
      · have hn : ((disclosureBudget + 1 : ℕ) : ℝ) ≤
            (((c.tree s).output bits).positiveReplies : ℝ) := by exact_mod_cast (by omega)
        have h1 : 1 ≤ positive s / (disclosureBudget + 1 : ℕ) := by
          rw [le_div_iff₀ hdp]
          simpa only [positive, hg, ite_true, one_mul] using hn
        simp only [success, hd, hg, ite_true, ite_false]
        linarith
    · have hs : 0 ≤ success s := by
        dsimp only [success]
        split_ifs <;> norm_num
      simp only [hg, ite_false]
      linarith
  have he := c.law.expect_mono point
  have div_expect (f : c.Seed → ℝ) (a : ℝ) :
      c.law.expect (fun s => f s / a) = c.law.expect f / a := by
    simp only [Law.expect, Finset.sum_div, mul_div_assoc]
  rw [Law.expect_sub, Law.expect_sub, div_expect, div_expect] at he
  have hgprob : 1 - delta ≤ c.law.expect (fun s => if Good s then (1 : ℝ) else 0) := by
    have hc := c.law.prob_compl {s | Good s}
    have hge : c.law.prob {s | Good s} =
        c.law.expect (fun s => if Good s then (1 : ℝ) else 0) := Law.prob_eq_expect _ _
    rw [hge] at hc
    change c.law.prob {s | ¬ Good s} =
      1 - c.law.expect (fun s => if Good s then (1 : ℝ) else 0) at hc
    linarith
  have ht' : c.law.expect taxed / (workBudget + 1 : ℕ) ≤
      (4 * workAccount) / (workBudget + 1 : ℕ) :=
    div_le_div_of_nonneg_right ht hwp.le
  have hp' : c.law.expect positive / (disclosureBudget + 1 : ℕ) ≤
      disclosureAccount / (disclosureBudget + 1 : ℕ) :=
    div_le_div_of_nonneg_right hpositive hdp.le
  have hs : c.law.expect success =
      valueProbability m bits ((p.disclosureCap disclosureBudget).cap workBudget)
        (SomeGood (SomeGood P)) := by
    rw [clock_success_eq, ← compile_expect]
    rfl
  rw [hs] at he
  linarith

end SteinerUpperBound.QueryProgram.Code

module

public import SteinerUpperBound.Matching.Padded.Measured

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Causal

open SteinerLowerBound
open scoped Classical BigOperators

variable {M T A B D C : Type*}

def EnsuresOutcome (m : M → ℝ) (b : T → Bool) (p : Code M T A) (P : Outcome A → Prop) : Prop :=
  ∀ f : Outcome A → ℝ, (∀ o, P o → f o = 0) → p.evaluate m b f = 0

theorem ensuresOutcome_of_evaluates (m : M → ℝ) (b : T → Bool) (p : Code M T A)
    (o : Outcome A) (h : p.Evaluates m b o) (P : Outcome A → Prop) (ho : P o) :
    EnsuresOutcome m b p P := by
  intro f hf
  exact (h f).trans (hf o ho)

theorem ensuresOutcome_le (m : M → ℝ) (b : T → Bool) (p : Code M T A)
    (P : Outcome A → Prop) (h : EnsuresOutcome m b p P) (f : Outcome A → ℝ)
    (budget : ℝ) (hf : ∀ o, P o → f o ≤ budget) : p.evaluate m b f ≤ budget := by
  let g : Outcome A → ℝ := fun o => max (f o - budget) 0
  have hg : p.evaluate m b g = 0 :=
    h g (fun o ho => max_eq_right (sub_nonpos.mpr (hf o ho)))
  have hm := p.evaluate_mono m b (fun o => show f o ≤ budget + g o by
    have hh := le_max_left (f o - budget) 0
    dsimp only [g]
    linarith)
  rw [SteinerUpperBound.QueryProgram.Code.evaluate_add,
    SteinerUpperBound.QueryProgram.Code.evaluate_const, hg, add_zero] at hm
  exact hm

theorem Counter.value_add (c : Counter) (o : Outcome A) (w m q z : ℕ) :
    c.value (o.add w m q z) =
      c.work * w + c.metric * m + c.retained * q + c.positive * z + c.value o := by
  simp only [Counter.value, SteinerUpperBound.QueryProgram.Outcome.add, Nat.cast_add]
  ring

theorem Counter.value_combine (c : Counter) (o : Outcome A) (o' : Outcome B) :
    c.value (SteinerUpperBound.QueryProgram.Outcome.combine o o') = c.value o + c.value o' := by
  simp only [Counter.value, SteinerUpperBound.QueryProgram.Outcome.combine, Nat.cast_add]
  ring

def Dominates (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (p : Program C A) (code : Code M T B) (R : A → B → Prop) : Prop :=
  ∀ (f : A → ℝ → ℝ) (g : Outcome B → ℝ),
    (∀ (leaf : p.Outcomes) o, R (p.output leaf) o.value →
      counter.value o ≤ p.cost charge rate leaf →
        g o ≤ f (p.output leaf) (p.cost charge rate leaf)) →
      code.evaluate m b g ≤ p.measured charge rate f

namespace Dominates

theorem ret (m : M → ℝ) (b : T → Bool) (counter : Counter) (charge : C → ℝ) (rate : ℝ)
    (a : A) (value : B) (R : A → B → Prop) (h : R a value) :
    Dominates m b counter charge rate (.ret a) (.pure value) R := by
  intro f g hfg
  rw [Program.measured_ret]
  exact hfg PUnit.unit (.pure value) h (by simp [Counter.value, SteinerUpperBound.QueryProgram.Outcome.pure,
    Program.cost])

theorem spend (m : M → ℝ) (b : T → Bool) (counter : Counter) (charge : C → ℝ) (rate : ℝ)
    (c : C) (n : ℕ) (p : Program C A) (code : Code M T B) (R : A → B → Prop)
    (hcost : counter.work * n ≤ charge c) (h : Dominates m b counter charge rate p code R) :
    Dominates m b counter charge rate (.tick c p) (Causal.spend n code) R := by
  intro f g hfg
  rw [evaluate_spend, Program.measured_tick]
  apply h
  intro leaf o hr hc
  apply hfg leaf (o.add n 0 0 0) hr
  rw [Counter.value_add]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  change counter.work * n + counter.value o ≤ charge c + p.cost charge rate leaf
  linarith

theorem bind (m : M → ℝ) (b : T → Bool) (counter : Counter) (charge : C → ℝ) (rate : ℝ)
    (p : Program C A) (code : Code M T B) (k : A → Program C D) {B' : Type*}
    (next : B → Code M T B') (R : A → B → Prop) (S : D → B' → Prop)
    (hp : Dominates m b counter charge rate p code R)
    (hk : ∀ a value, R a value → Dominates m b counter charge rate (k a) (next value) S) :
    Dominates m b counter charge rate (p.bind k) (code.bind next) S := by
  intro f g hfg
  rw [SteinerUpperBound.QueryProgram.Code.evaluate_bind, Program.measured_bind]
  apply hp
  intro leaf o hr hc
  apply hk (p.output leaf) o.value hr
  intro nextLeaf rest hs hrest
  have hh := hfg (Program.bindLeaf p k leaf nextLeaf)
    (SteinerUpperBound.QueryProgram.Outcome.combine o rest)
    (by simpa only [Program.bindLeaf_output, SteinerUpperBound.QueryProgram.Outcome.combine] using hs)
    (by
      rw [Counter.value_combine, Program.bindLeaf_cost]
      exact add_le_add hc hrest)
  simpa only [Program.bindLeaf_output, Program.bindLeaf_cost] using hh

theorem primitive (m : M → ℝ) (b : T → Bool) (counter : Counter) (charge : C → ℝ) (rate : ℝ)
    (c : C) (a : A) (code : Code M T B) (R : A → B → Prop)
    (h : EnsuresOutcome m b code (fun o => R a o.value ∧ counter.value o ≤ charge c)) :
    Dominates m b counter charge rate (.tick c (.ret a)) code R := by
  intro f g hfg
  simp only [Program.measured_tick, Program.measured_ret, add_zero]
  apply ensuresOutcome_le m b code _ h g _
  intro o ho
  have hh := hfg PUnit.unit o ho.1 (by simpa only [Program.cost, add_zero] using ho.2)
  simpa only [Program.output, Program.cost, add_zero] using hh

theorem uniform (m : M → ℝ) (b : T → Bool) (counter : Counter) (charge : C → ℝ) (rate : ℝ)
    (n : ℕ) (next : Fin (n + 1) → Program C A) (code : Fin (n + 1) → Code M T B)
    (R : A → B → Prop) (hrate : counter.work ≤ rate)
    (hnext : ∀ i, Dominates m b counter charge rate (next i) (code i) R) :
    Dominates m b counter charge rate (.draw (n + 1) (Nat.succ_pos _) next) (.uniform n code) R := by
  intro f g hfg
  rw [Program.measured_draw]
  simp only [SteinerUpperBound.QueryProgram.Code.evaluate, Law.expect, Law.uniform, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply hnext i
  intro leaf o hr hc
  apply hfg ⟨i, leaf⟩ (o.add 1 0 0 0) hr
  rw [Counter.value_add]
  simp only [Nat.cast_zero, Nat.cast_one, mul_zero, mul_one, add_zero]
  change counter.work + counter.value o ≤ rate + (next i).cost charge rate leaf
  linarith

theorem strengthen_model (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (p : Program C A) (code : Code M T B) (R : A → B → Prop)
    (P : A → Prop) (h : Dominates m b counter charge rate p code R) (hp : p.Supported P) :
    Dominates m b counter charge rate p code (fun a value => R a value ∧ P a) := by
  intro f g hfg
  apply h
  intro leaf o hr hc
  exact hfg leaf o ⟨hr, hp leaf⟩ hc

end Dominates

end SteinerUpperBound.Matching.Padded.Causal

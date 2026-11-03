module

public import SteinerUpperBound.QueryProgram.Basic

@[expose] public section

namespace SteinerUpperBound.QueryProgram

open SteinerLowerBound
open scoped Classical BigOperators

namespace Seeds

noncomputable def product {A B : Type} [Fintype A] [Fintype B]
    (mu : Law A) (nu : Law B) : Law (A × B) where
  mass s := mu.mass s.1 * nu.mass s.2
  nonneg s := mul_nonneg (mu.nonneg _) (nu.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, nu.total, mul_one, mu.total]

theorem expect_product {A B : Type} [Fintype A] [Fintype B]
    (mu : Law A) (nu : Law B) (F : A × B → ℝ) :
    (product mu nu).expect F = mu.expect (fun a => nu.expect (fun b => F (a, b))) := by
  simp only [Law.expect, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

noncomputable def dependent {A : Type} {S : A → Type} [Fintype A] [∀ a, Fintype (S a)]
    (mu : Law A) (nu : ∀ a, Law (S a)) : Law (Sigma S) where
  mass s := mu.mass s.1 * (nu s.1).mass s.2
  nonneg s := mul_nonneg (mu.nonneg _) ((nu s.1).nonneg _)
  total := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum]
    have hs (a : A) : (∑ i, (nu a).mass i) = 1 := (nu a).total
    simp_rw [hs]
    simpa only [mul_one] using mu.total

theorem expect_dependent {A : Type} {S : A → Type} [Fintype A] [∀ a, Fintype (S a)]
    (mu : Law A) (nu : ∀ a, Law (S a)) (F : Sigma S → ℝ) :
    (dependent mu nu).expect F = mu.expect (fun a => (nu a).expect (fun s => F ⟨a, s⟩)) := by
  simp only [Law.expect, dependent, Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

end Seeds

structure Compiled (Q R : Type*) where
  Seed : Type
  finite : Fintype Seed
  law : @Law Seed finite
  tree : Seed → DecisionTree Q Bool R

namespace Compiled

variable {Q R S : Type*}

@[reducible]
instance seedFintype (c : Compiled Q R) : Fintype c.Seed := c.finite

noncomputable abbrev leaf (r : R) : Compiled Q R where
  Seed := Unit
  finite := inferInstance
  law := Law.pure ()
  tree := fun _ => .leaf r

abbrev map (f : R → S) (c : Compiled Q R) : Compiled Q S where
  Seed := c.Seed
  finite := c.finite
  law := c.law
  tree := fun s => (c.tree s).map f

noncomputable abbrev query (q : Q) (c₀ c₁ : Compiled Q R) : Compiled Q R where
  Seed := c₀.Seed × c₁.Seed
  finite := inferInstance
  law := Seeds.product c₀.law c₁.law
  tree := fun s => .query q (fun b => if b then c₁.tree s.2 else c₀.tree s.1)

noncomputable abbrev choose {A : Type} [Fintype A] (mu : Law A)
    (c : A → Compiled Q R) : Compiled Q R where
  Seed := (a : A) × (c a).Seed
  finite := inferInstance
  law := Seeds.dependent mu (fun a => (c a).law)
  tree := fun s => (c s.1).tree s.2

noncomputable def expect (c : Compiled Q R) (b : Q → Bool) (F : R → ℝ) : ℝ :=
  c.law.expect (fun s => F ((c.tree s).output b))

@[simp]
theorem expect_leaf (r : R) (b : Q → Bool) (F : R → ℝ) :
    (leaf r : Compiled Q R).expect b F = F r := by
  change (Law.pure ()).expect (fun _ => F r) = F r
  exact Law.expect_const _ _

@[simp]
theorem expect_map (f : R → S) (c : Compiled Q R) (b : Q → Bool) (F : S → ℝ) :
    (c.map f).expect b F = c.expect b (fun r => F (f r)) := by
  simp only [expect, map, DecisionTree.output_map]

@[simp]
theorem expect_query (q : Q) (c₀ c₁ : Compiled Q R) (b : Q → Bool) (F : R → ℝ) :
    (query q c₀ c₁).expect b F = if b q then c₁.expect b F else c₀.expect b F := by
  cases hb : b q <;>
    simp only [expect, query, DecisionTree.output, hb, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    rw [Seeds.expect_product]
    simp only [Law.expect_const]

@[simp]
theorem expect_choose {A : Type} [Fintype A] (mu : Law A)
    (c : A → Compiled Q R) (b : Q → Bool) (F : R → ℝ) :
    (choose mu c).expect b F = mu.expect (fun a => (c a).expect b F) := by
  exact Seeds.expect_dependent mu (fun a => (c a).law)
    (fun s => F (((c s.1).tree s.2).output b))

end Compiled

namespace Code

variable {M Q R : Type*}

noncomputable def compile (m : M → ℝ) : Code M Q R → Compiled Q (Outcome R)
  | .pure r => .leaf (.pure r)
  | .metric q next => ((next (m q)).compile m).map (Outcome.add 1 1 0 0)
  | .retained q next =>
      Compiled.query q (((next false).compile m).map (Outcome.add 1 0 1 0))
        (((next true).compile m).map (Outcome.add 1 0 1 1))
  | .uniform n next =>
      (Compiled.choose (Law.uniform (Fin (n + 1))) (fun a => (next a).compile m)).map
        (Outcome.add 1 0 0 0)
  | .coin rate next =>
      (Compiled.choose (CategoricalCoupling.bernoulli rate) (fun a => (next a).compile m)).map
        (Outcome.add 2 0 0 0)
  | .tick n next => (next.compile m).map (Outcome.add (n + 1) 0 0 0)

theorem compile_expect (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (F : Outcome R → ℝ) :
    (p.compile m).expect b F = p.evaluate m b F := by
  induction p generalizing F with
  | pure r => simp only [compile, evaluate, Compiled.expect_leaf]
  | metric q next ih =>
      simpa only [compile, evaluate, Compiled.expect_map] using
        (ih (m q) (fun o => F (o.add 1 1 0 0)))
  | retained q next ih =>
      simp only [compile, evaluate, Compiled.expect_query]
      cases b q <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Compiled.expect_map] <;> apply ih
  | uniform n next ih =>
      simp only [compile, evaluate, Compiled.expect_map, Compiled.expect_choose]
      apply congrArg (Law.uniform (Fin (n + 1))).expect
      funext a
      exact ih a _
  | coin rate next ih =>
      simp only [compile, evaluate, Compiled.expect_map, Compiled.expect_choose]
      apply congrArg (CategoricalCoupling.bernoulli rate).expect
      funext a
      exact ih a _
  | tick n next ih =>
      simpa only [compile, evaluate, Compiled.expect_map] using
        (ih (fun o => F (o.add (n + 1) 0 0 0)))

theorem compile_probability (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (E : Set (Outcome R)) :
    (p.compile m).law.prob {s | ((p.compile m).tree s).output b ∈ E} =
      p.probability m b E := by
  rw [Law.prob_eq_expect]
  change (p.compile m).expect b (fun o => if o ∈ E then 1 else 0) = _
  exact compile_expect m b p _

theorem evaluate_const (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (c : ℝ) :
    p.evaluate m b (fun _ => c) = c := by
  rw [← compile_expect]
  exact Law.expect_const _ _

theorem evaluate_mono (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    {F G : Outcome R → ℝ} (h : ∀ o, F o ≤ G o) :
    p.evaluate m b F ≤ p.evaluate m b G := by
  rw [← compile_expect, ← compile_expect]
  exact (p.compile m).law.expect_mono (fun _ => h _)

theorem evaluate_nonneg (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    {F : Outcome R → ℝ} (h : ∀ o, 0 ≤ F o) :
    0 ≤ p.evaluate m b F := by
  rw [← compile_expect]
  exact (p.compile m).law.expect_nonneg (fun _ => h _)

theorem evaluate_add (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (F G : Outcome R → ℝ) :
    p.evaluate m b (fun o => F o + G o) = p.evaluate m b F + p.evaluate m b G := by
  rw [← compile_expect, ← compile_expect, ← compile_expect]
  exact Law.expect_add _ _ _

end Code

end SteinerUpperBound.QueryProgram

module

public import SteinerUpperBound.Matching.Padded.Basic

@[expose] public section

/-!
# Finite RAM sampling programs

Uniform integer draws are explicit nodes, not free distributional primitives.
`tick` records deterministic primitive operations. Every program has a finite
execution space even when its returned state type is infinite.
-/

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

inductive Program (C : Type*) (A : Type*) where
  | ret : A → Program C A
  | tick : C → Program C A → Program C A
  | draw (n : ℕ) (positive : 0 < n) : (Fin n → Program C A) → Program C A

namespace Program

variable {C A B : Type*}

def Outcomes : Program C A → Type
  | .ret _ => PUnit
  | .tick _ p => Outcomes p
  | .draw n _ next => (i : Fin n) × Outcomes (next i)

@[instance_reducible]
noncomputable def outcomeFintype : (p : Program C A) → Fintype p.Outcomes
  | .ret _ => by change Fintype PUnit; exact inferInstance
  | .tick _ p => outcomeFintype p
  | .draw n _ next => by
    change Fintype ((i : Fin n) × Outcomes (next i))
    letI : ∀ i, Fintype (Outcomes (next i)) := fun i => outcomeFintype (next i)
    exact inferInstance

noncomputable instance (p : Program C A) : Fintype p.Outcomes := outcomeFintype p

noncomputable def mass : (p : Program C A) → p.Outcomes → ℝ
  | .ret _, _ => 1
  | .tick _ p, x => mass p x
  | .draw n _ next, ⟨i, x⟩ => (n : ℝ)⁻¹ * mass (next i) x

theorem mass_nonneg (p : Program C A) (x : p.Outcomes) : 0 ≤ p.mass x := by
  induction p with
  | ret => exact zero_le_one
  | tick _ _ ih => exact ih x
  | draw n hn next ih =>
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (ih x.1 x.2)

theorem mass_total (p : Program C A) : ∑ x, p.mass x = 1 := by
  induction p with
  | ret a => simp [Outcomes, mass]
  | tick c p ih => exact ih
  | draw n hn next ih =>
    change (∑ x : (i : Fin n) × (next i).Outcomes,
      (n : ℝ)⁻¹ * (next x.1).mass x.2) = 1
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, ih]
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    simpa [mul_comm] using mul_inv_cancel₀ hnR

noncomputable def law (p : Program C A) : Law p.Outcomes where
  mass := p.mass
  nonneg := p.mass_nonneg
  total := p.mass_total

def output : (p : Program C A) → p.Outcomes → A
  | .ret a, _ => a
  | .tick _ p, x => p.output x
  | .draw _ _ next, ⟨i, x⟩ => (next i).output x

def operations : (p : Program C A) → p.Outcomes → ℕ
  | .ret _, _ => 0
  | .tick _ p, x => 1 + p.operations x
  | .draw _ _ next, ⟨i, x⟩ => 1 + (next i).operations x

def cost (charge : C → ℝ) (drawRate : ℝ) : (p : Program C A) → p.Outcomes → ℝ
  | .ret _, _ => 0
  | .tick c p, x => charge c + p.cost charge drawRate x
  | .draw _ _ next, ⟨i, x⟩ => drawRate + (next i).cost charge drawRate x

noncomputable def expect (p : Program C A) (f : A → ℝ) : ℝ :=
  p.law.expect (fun x => f (p.output x))

noncomputable def probability (p : Program C A) (P : A → Prop) : ℝ :=
  p.law.prob {x | P (p.output x)}

noncomputable def expectedCost (p : Program C A) (charge : C → ℝ) (drawRate : ℝ) : ℝ :=
  p.law.expect (p.cost charge drawRate)

@[simp] theorem expect_ret (a : A) (f : A → ℝ) :
    (Program.ret (C := C) a).expect f = f a := by
  simp [expect, law, Law.expect, mass, output, Outcomes]

@[simp] theorem expect_tick (c : C) (p : Program C A) (f : A → ℝ) :
    (Program.tick c p).expect f = p.expect f := rfl

theorem expect_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program C A) (f : A → ℝ) :
    (Program.draw n hn next).expect f = ∑ i : Fin n, (n : ℝ)⁻¹ * (next i).expect f := by
  unfold expect Law.expect law
  change (∑ x : (i : Fin n) × (next i).Outcomes,
    ((n : ℝ)⁻¹ * (next x.1).mass x.2) * f ((next x.1).output x.2)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

@[simp] theorem expect_const (p : Program C A) (r : ℝ) : p.expect (fun _ => r) = r :=
  Law.expect_const _ _

theorem expect_mono (p : Program C A) {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    p.expect f ≤ p.expect g :=
  p.law.expect_mono (fun x => h (p.output x))

theorem expect_add (p : Program C A) (f g : A → ℝ) :
    p.expect (fun a => f a + g a) = p.expect f + p.expect g :=
  Law.expect_add _ _ _

theorem expect_mul_const (p : Program C A) (f : A → ℝ) (r : ℝ) :
    p.expect (fun a => f a * r) = p.expect f * r :=
  Law.expect_mul_const _ _ _

theorem expect_const_mul (p : Program C A) (r : ℝ) (f : A → ℝ) :
    p.expect (fun a => r * f a) = r * p.expect f :=
  Law.expect_const_mul _ _ _

def bind : Program C A → (A → Program C B) → Program C B
  | .ret a, k => k a
  | .tick c p, k => .tick c (p.bind k)
  | .draw n hn next, k => .draw n hn (fun i => (next i).bind k)

theorem expect_bind (p : Program C A) (k : A → Program C B) (f : B → ℝ) :
    (p.bind k).expect f = p.expect (fun a => (k a).expect f) := by
  induction p with
  | ret => simp [bind]
  | tick c p ih => simpa [bind] using ih
  | draw n hn next ih =>
    simp only [bind, expect_draw]
    exact Finset.sum_congr rfl (fun i _ => by rw [ih i])

@[simp] theorem expectedCost_ret (a : A) (charge : C → ℝ) (r : ℝ) :
    (Program.ret (C := C) a).expectedCost charge r = 0 := by
  simp [expectedCost, law, Law.expect, cost, Outcomes, mass]

@[simp] theorem expectedCost_tick (c : C) (p : Program C A) (charge : C → ℝ) (r : ℝ) :
    (Program.tick c p).expectedCost charge r = charge c + p.expectedCost charge r := by
  change p.law.expect (fun x => charge c + p.cost charge r x) = _
  rw [Law.expect_add, Law.expect_const]
  rfl

theorem expectedCost_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program C A)
    (charge : C → ℝ) (r : ℝ) :
    (Program.draw n hn next).expectedCost charge r =
      r + ∑ i : Fin n, (n : ℝ)⁻¹ * (next i).expectedCost charge r := by
  have hr : (∑ i : Fin n, (n : ℝ)⁻¹ * r) = r := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hn), one_mul]
  unfold expectedCost Law.expect law
  change (∑ x : (i : Fin n) × (next i).Outcomes,
    ((n : ℝ)⁻¹ * (next x.1).mass x.2) *
      (r + (next x.1).cost charge r x.2)) = _
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ i : Fin n, ((n : ℝ)⁻¹ * r +
        (n : ℝ)⁻¹ * ∑ x, (next i).mass x * (next i).cost charge r x) := by
      apply Finset.sum_congr rfl
      intro i _
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, ← Finset.mul_sum, (next i).mass_total, mul_one]
      congr 1
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [Finset.sum_add_distrib, hr]

theorem expectedCost_bind (p : Program C A) (k : A → Program C B)
    (charge : C → ℝ) (r : ℝ) :
    (p.bind k).expectedCost charge r =
      p.expectedCost charge r + p.expect (fun a => (k a).expectedCost charge r) := by
  induction p with
  | ret => simp [bind]
  | tick c p ih => simp only [bind, expectedCost_tick, expect_tick, ih]; ring
  | draw n hn next ih =>
    simp only [bind, expectedCost_draw, expect_draw, ih]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring

theorem cost_nonneg (p : Program C A) (charge : C → ℝ) (r : ℝ)
    (hc : ∀ c, 0 ≤ charge c) (hr : 0 ≤ r) (x : p.Outcomes) :
    0 ≤ p.cost charge r x := by
  induction p with
  | ret => exact le_refl _
  | tick c p ih => exact add_nonneg (hc c) (ih x)
  | draw n hn next ih => exact add_nonneg hr (ih x.1 x.2)

theorem truncated_cost_le (p : Program C A) (charge : C → ℝ) (r : ℝ)
    (hc : ∀ c, 0 ≤ charge c) (hr : 0 ≤ r) (good : p.Outcomes → Prop) :
    p.law.expect (fun x => if good x then p.cost charge r x else 0) ≤
      p.expectedCost charge r := by
  apply Law.expect_mono
  intro x
  split_ifs
  · exact le_refl _
  · exact p.cost_nonneg charge r hc hr x

end Program

end SteinerUpperBound.Matching.Padded

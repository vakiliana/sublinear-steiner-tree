module

public import SteinerUpperBound.Matching.Padded.Arithmetic

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Program

open SteinerLowerBound
open scoped Classical BigOperators

variable {C A B : Type*}

def Supported (p : Program C A) (P : A → Prop) : Prop :=
  ∀ x : p.Outcomes, P (p.output x)

theorem supported_ret (a : A) (P : A → Prop) (h : P a) :
    (Program.ret (C := C) a).Supported P := fun _ => h

theorem supported_tick (c : C) (p : Program C A) (P : A → Prop) (h : p.Supported P) :
    (Program.tick c p).Supported P := h

theorem supported_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program C A) (P : A → Prop)
    (h : ∀ i, (next i).Supported P) : (Program.draw n hn next).Supported P :=
  fun x => h x.1 x.2

theorem supported_bind (p : Program C A) (k : A → Program C B) (P : A → Prop) (Q : B → Prop)
    (hp : p.Supported P) (hk : ∀ a, P a → (k a).Supported Q) :
    (p.bind k).Supported Q := by
  induction p with
  | ret a => exact hk a (hp PUnit.unit)
  | tick c p ih => exact ih hp
  | draw n hn next ih => exact fun x => ih x.1 (fun y => hp ⟨x.1, y⟩) x.2

def Bound (p : Program C A) (charge : C → ℝ) (drawRate : ℝ)
    (post : A → ℝ) (budget : ℝ) : Prop :=
  ∀ x : p.Outcomes, p.cost charge drawRate x + post (p.output x) ≤ budget

theorem bound_ret (a : A) (charge : C → ℝ) (r : ℝ) (post : A → ℝ) (b : ℝ)
    (h : post a ≤ b) : (Program.ret (C := C) a).Bound charge r post b := by
  intro x
  simpa only [cost, output, zero_add] using h

theorem bound_tick (c : C) (p : Program C A) (charge : C → ℝ) (r : ℝ)
    (post : A → ℝ) (b : ℝ) (h : p.Bound charge r post (b - charge c)) :
    (Program.tick c p).Bound charge r post b := by
  intro x
  have hx := h x
  change charge c + p.cost charge r x + post (p.output x) ≤ b
  linarith

theorem bound_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program C A)
    (charge : C → ℝ) (r : ℝ) (post : A → ℝ) (b : ℝ)
    (h : ∀ i, (next i).Bound charge r post (b - r)) :
    (Program.draw n hn next).Bound charge r post b := by
  intro x
  have hx := h x.1 x.2
  change r + (next x.1).cost charge r x.2 + post ((next x.1).output x.2) ≤ b
  linarith

theorem bound_bind (p : Program C A) (k : A → Program C B)
    (charge : C → ℝ) (r : ℝ) (nextBudget : A → ℝ) (post : B → ℝ) (b : ℝ)
    (hp : p.Bound charge r nextBudget b)
    (hk : ∀ a, (k a).Bound charge r post (nextBudget a)) :
    (p.bind k).Bound charge r post b := by
  induction p generalizing b with
  | ret a =>
    intro x
    have ha := hp PUnit.unit
    change 0 + nextBudget a ≤ b at ha
    exact (hk a x).trans (by linarith)
  | tick c p ih =>
    apply bound_tick
    apply ih
    intro x
    have hh := hp x
    change charge c + p.cost charge r x + nextBudget (p.output x) ≤ b at hh
    linarith
  | draw n hn next ih =>
    apply bound_draw
    intro i
    apply ih i
    intro x
    have hh := hp ⟨i, x⟩
    change r + (next i).cost charge r x + nextBudget ((next i).output x) ≤ b at hh
    linarith

theorem expected_bound (p : Program C A) (charge : C → ℝ) (r : ℝ)
    (post : A → ℝ) (b : ℝ) (h : p.Bound charge r post b) :
    p.expectedCost charge r + p.expect post ≤ b := by
  have hh := p.law.expect_mono h
  rw [Law.expect_add, Law.expect_const] at hh
  exact hh

end SteinerUpperBound.Matching.Padded.Program

module

public import SteinerUpperBound.Matching.Padded.CausalContract

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Program

open SteinerLowerBound
open scoped Classical BigOperators

variable {C A B : Type*}

noncomputable def measured (p : Program C A) (charge : C → ℝ) (rate : ℝ) (f : A → ℝ → ℝ) : ℝ :=
  p.law.expect (fun leaf => f (p.output leaf) (p.cost charge rate leaf))

theorem measured_ret (a : A) (charge : C → ℝ) (rate : ℝ) (f : A → ℝ → ℝ) :
    (Program.ret (C := C) a).measured charge rate f = f a 0 := by
  simp [measured, law, Law.expect, Outcomes, mass, output, cost]

theorem measured_tick (c : C) (p : Program C A) (charge : C → ℝ) (rate : ℝ) (f : A → ℝ → ℝ) :
    (Program.tick c p).measured charge rate f =
      p.measured charge rate (fun a n => f a (charge c + n)) := rfl

theorem measured_draw (n : ℕ) (hn : 0 < n) (next : Fin n → Program C A)
    (charge : C → ℝ) (rate : ℝ) (f : A → ℝ → ℝ) :
    (Program.draw n hn next).measured charge rate f =
      ∑ i : Fin n, (n : ℝ)⁻¹ * (next i).measured charge rate (fun a c => f a (rate + c)) := by
  unfold measured Law.expect law
  change (∑ x : (i : Fin n) × (next i).Outcomes,
    ((n : ℝ)⁻¹ * (next x.1).mass x.2) *
      f ((next x.1).output x.2) (rate + (next x.1).cost charge rate x.2)) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leaf _
  ring

theorem measured_bind (p : Program C A) (k : A → Program C B)
    (charge : C → ℝ) (rate : ℝ) (f : B → ℝ → ℝ) :
    (p.bind k).measured charge rate f =
      p.measured charge rate (fun a c =>
        (k a).measured charge rate (fun b d => f b (c + d))) := by
  induction p generalizing f with
  | ret a => simp only [bind, measured_ret, zero_add]
  | tick c p ih =>
    simp only [bind, measured_tick, ih]
    simp only [add_assoc]
  | draw n hn next ih =>
    simp only [bind, measured_draw, ih]
    simp only [add_assoc]

def bindLeaf : (p : Program C A) → (k : A → Program C B) →
    (leaf : p.Outcomes) → (k (p.output leaf)).Outcomes → (p.bind k).Outcomes
  | .ret _, _, _, next => next
  | .tick _ p, k, leaf, next => bindLeaf p k leaf next
  | .draw _ _ branches, k, ⟨i, leaf⟩, next => ⟨i, bindLeaf (branches i) k leaf next⟩

theorem bindLeaf_output (p : Program C A) (k : A → Program C B)
    (leaf : p.Outcomes) (next : (k (p.output leaf)).Outcomes) :
    (p.bind k).output (bindLeaf p k leaf next) = (k (p.output leaf)).output next := by
  induction p with
  | ret a => rfl
  | tick c p ih => exact ih leaf next
  | draw n hn branches ih =>
    obtain ⟨i, leaf⟩ := leaf
    exact ih i leaf next

theorem bindLeaf_cost (p : Program C A) (k : A → Program C B)
    (charge : C → ℝ) (rate : ℝ) (leaf : p.Outcomes) (next : (k (p.output leaf)).Outcomes) :
    (p.bind k).cost charge rate (bindLeaf p k leaf next) =
      p.cost charge rate leaf + (k (p.output leaf)).cost charge rate next := by
  induction p with
  | ret a => simp only [bindLeaf, bind, cost, output, zero_add]
  | tick c p ih =>
    change charge c + (p.bind k).cost charge rate (bindLeaf p k leaf next) = _
    rw [ih leaf next]
    change charge c + (_ + _) = (charge c + _) + _
    simp only [output]
    ring
  | draw n hn branches ih =>
    obtain ⟨i, leaf⟩ := leaf
    change rate + ((branches i).bind k).cost charge rate (bindLeaf (branches i) k leaf next) = _
    rw [ih i leaf next]
    change rate + (_ + _) = (rate + _) + _
    simp only [output]
    ring

end SteinerUpperBound.Matching.Padded.Program

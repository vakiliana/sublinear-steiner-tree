module

public import SteinerUpperBound.Matching.Padded.Domination
public import SteinerUpperBound.Matching.Padded.RawCausal

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Causal

open SteinerLowerBound
open scoped Classical

variable {C A B M T Index : Type*}

theorem evaluate_neg (m : M → ℝ) (b : T → Bool) (code : Code M T B) (f : Outcome B → ℝ) :
    code.evaluate m b (fun o => -f o) = -code.evaluate m b f := by
  have h := SteinerUpperBound.QueryProgram.Code.evaluate_add m b code f (fun o => -f o)
  have he : (fun o => f o + -f o) = fun _ => (0 : ℝ) := by funext o; ring
  rw [he, SteinerUpperBound.QueryProgram.Code.evaluate_const] at h
  linarith

theorem measured_neg (p : Program C A) (charge : C → ℝ) (rate : ℝ) (f : A → ℝ → ℝ) :
    p.measured charge rate (fun a n => -f a n) = -p.measured charge rate f := by
  simp [Program.measured, Law.expect, mul_neg, Finset.sum_neg_distrib]

theorem Dominates.value_law (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (p : Program C A) (code : Code M T B) (R : A → B → Prop)
    (h : Dominates m b counter charge rate p code R) (f : A → ℝ) (g : B → ℝ)
    (hfg : ∀ a value, R a value → f a = g value) :
    expect m b code g = p.expect f := by
  have hle := h (fun a _ => f a) (fun o => g o.value)
    (fun leaf o hr _ => le_of_eq (hfg _ _ hr).symm)
  have hge := h (fun a _ => -f a) (fun o => -g o.value)
    (fun leaf o hr _ => le_of_eq (congrArg Neg.neg (hfg _ _ hr)).symm)
  rw [evaluate_neg, measured_neg] at hge
  change expect m b code g ≤ p.expect f at hle
  change -expect m b code g ≤ -p.expect f at hge
  linarith

theorem Dominates.relate (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (p : Program C A) (code : Code M T B)
    (R S : A → B → Prop) (h : Dominates m b counter charge rate p code R)
    (hrs : ∀ a value, R a value → S a value) :
    Dominates m b counter charge rate p code S := by
  intro f g hfg
  apply h
  intro leaf o hr hc
  exact hfg leaf o (hrs _ _ hr) hc

theorem Dominates.counter_tail (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (p : Program C A) (code : Code M T B) (R : A → B → Prop)
    (h : Dominates m b counter charge rate p code R) (threshold : ℝ) :
    code.evaluate m b (fun o => if threshold ≤ counter.value o then 1 else 0) ≤
      p.measured charge rate (fun _ cost => if threshold ≤ cost then 1 else 0) := by
  classical
  apply h
  intro leaf o _ hc
  by_cases ho : threshold ≤ counter.value o
  · have hm := ho.trans hc
    simp only [ho, hm, ↓reduceIte, le_refl]
  · simp only [ho, ↓reduceIte]
    split_ifs <;> norm_num

theorem Dominates.forEach (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (charge : C → ℝ) (rate : ℝ) (step : Index → A → Program C A)
    (next : Index → B → Code M T B) (R : A → B → Prop) (xs : List Index)
    (hstep : ∀ i ∈ xs, ∀ a value, R a value →
      Dominates m b counter charge rate (step i a) (next i value) R)
    (a : A) (value : B) (hr : R a value) :
    Dominates m b counter charge rate (Program.forEach step xs a) (RawCausal.forEach next xs value) R := by
  induction xs generalizing a value with
  | nil => exact Dominates.ret m b counter charge rate a value R hr
  | cons i xs ih =>
    rw [Program.forEach, RawCausal.forEach]
    apply Dominates.bind m b counter charge rate (step i a) (next i value) _ _ R R
      (hstep i (by simp) a value hr)
    intro a' value' h'
    exact ih (fun j hj => hstep j (by simp [hj])) a' value' h'

end SteinerUpperBound.Matching.Padded.Causal

module

public import SteinerUpperBound.Covers.Product

@[expose] public section

namespace SteinerUpperBound.Covers.FiniteSampling

open SteinerLowerBound
open scoped Classical BigOperators

variable {U : Type*} [Fintype U]

theorem cons_eq_iff {n : ℕ} (x : U) (v : Fin n → U) (w : Fin (n + 1) → U) :
    Fin.cons x v = w ↔ x = w 0 ∧ v = Fin.tail w := by
  constructor
  · intro h
    subst w
    simp
  · rintro ⟨rfl, rfl⟩
    exact Fin.cons_self_tail w

theorem mass_withFintype {A : Type*} (i j : Fintype A) (μ : @Law A i) (a : A) :
    @Law.mass A j (LawOperations.withFintype i j μ) a = @Law.mass A i μ a := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

theorem expect_withFintype {A : Type*} (i j : Fintype A) (μ : @Law A i) (f : A → ℝ) :
    @Law.expect A j (LawOperations.withFintype i j μ) f = @Law.expect A i μ f := by
  have h : i = j := Subsingleton.elim _ _
  cases h
  rfl

theorem expect_product (μ : Law U) (f : U → ℝ) (n : ℕ) :
    (tape μ n).expect (fun w => ∏ j, f (w j)) = (μ.expect f) ^ n := by
  induction n with
  | zero => simp [tape]
  | succ n ih =>
    rw [expect_tape_succ]
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [Law.expect_const_mul, ih, Law.expect_mul_const]
    rw [pow_succ]
    ring

theorem prob_box (μ : Law U) (n : ℕ) (P : Fin n → U → Prop) :
    (tape μ n).prob {w | ∀ j, P j (w j)} = ∏ j, μ.prob {x | P j x} := by
  classical
  induction n with
  | zero => simp [tape, Law.prob_pure]
  | succ n ih =>
    rw [Law.prob_eq_expect, expect_tape_succ]
    calc
      _ = μ.expect (fun x => (if P 0 x then (1 : ℝ) else 0) *
          (tape μ n).prob {w | ∀ j, P j.succ (w j)}) := by
        apply congrArg μ.expect
        funext x
        rw [Law.prob_eq_expect, ← Law.expect_const_mul]
        apply congrArg (tape μ n).expect
        funext w
        by_cases hx : P 0 x <;> by_cases hw : ∀ j, P j.succ (w j) <;>
          simp [Set.mem_ofPred_eq, Fin.forall_fin_succ, hx, hw]
      _ = _ := by
        rw [ih (fun j => P j.succ), Law.expect_mul_const, Fin.prod_univ_succ]
        congr 1
        exact (Law.prob_eq_expect μ {x | P 0 x}).symm

theorem prob_all (μ : Law U) (P : U → Prop) (n : ℕ) :
    (tape μ n).prob {w | ∀ j, P (w j)} = (μ.prob {x | P x}) ^ n := by
  rw [prob_box]
  simp

theorem tape_mass (μ : Law U) (n : ℕ) (w : Fin n → U) :
    (tape μ n).mass w = ∏ j, μ.mass (w j) := by
  have he : ({w} : Set (Fin n → U)) = {v | ∀ j, v j = w j} := by
    ext v
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
  rw [← CategoricalCoupling.probability_atom, he, prob_box μ n (fun j x => x = w j)]
  apply Finset.prod_congr rfl
  intro j _
  exact CategoricalCoupling.probability_atom μ (w j)

theorem tape_eq_iid (μ : Law U) (n : ℕ) :
    tape μ n = LawOperations.withFintype _ inferInstance (μ.iid (Fin n)) := by
  apply LawOperations.ext_mass
  intro w
  rw [mass_withFintype]
  exact tape_mass μ n w

theorem centered_sum_mean (μ : Law U) (f : U → ℝ) (hf : μ.expect f = 0) (n : ℕ) :
    (tape μ n).expect (fun w => ∑ j, f (w j)) = 0 := by
  induction n with
  | zero => simp [tape]
  | succ n ih =>
    rw [expect_tape_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    simp_rw [Law.expect_add, Law.expect_const, ih]
    simpa using hf

theorem centered_sum_square (μ : Law U) (f : U → ℝ) (hf : μ.expect f = 0) (n : ℕ) :
    (tape μ n).expect (fun w => (∑ j, f (w j)) ^ 2) =
      (n : ℝ) * μ.expect (fun x => f x ^ 2) := by
  induction n with
  | zero => simp [tape]
  | succ n ih =>
    rw [expect_tape_succ]
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have he (x : U) :
        (tape μ n).expect (fun w => (f x + ∑ j, f (w j)) ^ 2) =
          f x ^ 2 + (n : ℝ) * μ.expect (fun y => f y ^ 2) := by
      have hfun (w : Fin n → U) :
          (f x + ∑ j, f (w j)) ^ 2 =
            f x ^ 2 + 2 * f x * (∑ j, f (w j)) + (∑ j, f (w j)) ^ 2 := by ring
      simp_rw [hfun, Law.expect_add, Law.expect_const, Law.expect_const_mul,
        centered_sum_mean μ f hf n, ih]
      ring
    simp_rw [he, Law.expect_add, Law.expect_const]
    push_cast
    ring

end SteinerUpperBound.Covers.FiniteSampling

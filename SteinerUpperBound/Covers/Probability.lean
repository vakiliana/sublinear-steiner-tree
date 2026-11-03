module

public import SteinerUpperBound.Covers.Independent

@[expose] public section

namespace SteinerUpperBound.Covers

open SteinerLowerBound
open scoped Classical BigOperators

namespace FiniteSampling

variable {U A : Type*} [Fintype U] [Fintype A]

theorem map_const (μ : Law U) (a : A) : μ.map (fun _ => a) = Law.pure a := by
  classical
  apply LawOperations.ext_mass
  intro z
  by_cases h : a = z <;> simp [Law.map, Law.pure, h, eq_comm, μ.total]

/-- A fixed finite tape of fresh, identically distributed draws. -/
noncomputable def tape (μ : Law U) : (n : ℕ) → Law (Fin n → U)
  | 0 => Law.pure Fin.elim0
  | n + 1 => μ.bind (fun x => (tape μ n).map (fun w => Fin.cons x w))

theorem expect_tape_succ (μ : Law U) (n : ℕ) (f : (Fin (n + 1) → U) → ℝ) :
    (tape μ (n + 1)).expect f =
      μ.expect (fun x => (tape μ n).expect (fun w => f (Fin.cons x w))) := by
  simp only [tape, Law.expect_bind, Law.expect_map]

theorem map_tape_succ (μ : Law U) (n : ℕ) (f : (Fin (n + 1) → U) → A) :
    (tape μ (n + 1)).map f =
      μ.bind (fun x => (tape μ n).map (fun w => f (Fin.cons x w))) := by
  rw [tape, LawOperations.map_bind]
  congr 1
  funext x
  exact LawOperations.map_comp _ _ _

theorem uniform_expect (U : Type*) [Fintype U] [Nonempty U] (f : U → ℝ) :
    (Law.uniform U).expect f = (∑ x, f x) / Fintype.card U := by
  simp only [Law.expect, Law.uniform, ← Finset.mul_sum]
  ring

theorem uniform_prob (U : Type*) [Fintype U] [Nonempty U] (S : Finset U) :
    (Law.uniform U).prob (S : Set U) = (S.card : ℝ) / Fintype.card U := by
  classical
  rw [Law.prob_eq_expect, uniform_expect]
  congr 1
  simp only [Finset.mem_coe]
  simp_rw [← Finset.sum_filter]
  simp

theorem sum_three (S : Finset U) (x : U) (hx : x ∈ S) (a b c : ℝ) :
    (∑ y, if y = x then a else if y ∈ S then b else c) =
      a + ((S.card : ℝ) - 1) * b + ((Fintype.card U : ℝ) - S.card) * c := by
  classical
  have hp (y : U) :
      (if y = x then a else if y ∈ S then b else c) =
        c + (if y ∈ S then b - c else 0) + (if y = x then a - b else 0) := by
    by_cases hy : y = x
    · subst y
      simp [hx]
      <;> ring
    · by_cases hys : y ∈ S <;> simp [hy, hys] <;> ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : (∑ y : U, if y ∈ S then b - c else 0) = S.card * (b - c) := by
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun y => y ∈ S) = S := by ext y; simp
    rw [he]
    simp
    ring
  rw [hs]
  simp
  ring

theorem uniform_expect_ne [Nonempty U] (x : U) (d : ℝ) :
    (Law.uniform U).expect (fun y => if y = x then 0 else d) =
      (1 - 1 / Fintype.card U) * d := by
  rw [uniform_expect]
  have hs : (∑ y : U, if y = x then (0 : ℝ) else d) =
      ((Fintype.card U : ℝ) - 1) * d := by
    have ht := sum_three ({x} : Finset U) x (by simp) 0 d d
    simpa using ht
  rw [hs]
  have hk : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  <;> ring

theorem survival_exp {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (B : ℕ) :
    (1 - p) ^ B ≤ Real.exp (-(B : ℝ) * p) := by
  have hb : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using
    pow_le_pow_left₀ (sub_nonneg.mpr hp1) hb B

theorem bool_ext (μ ν : Law Bool) (h : μ.mass true = ν.mass true) : μ = ν := by
  apply LawOperations.ext_mass
  intro b
  cases b with
  | true => exact h
  | false =>
    have hμ : μ.mass true + μ.mass false = 1 := by simpa using μ.total
    have hν : ν.mass true + ν.mass false = 1 := by simpa using ν.total
    linarith

theorem bernoulli_zero :
    CategoricalCoupling.bernoulli (⟨0, by norm_num⟩ : Rate) = Law.pure false := by
  apply bool_ext
  simp [CategoricalCoupling.bernoulli, Law.pure]

end FiniteSampling

end SteinerUpperBound.Covers

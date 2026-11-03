module

public import SteinerUpperBound.Model

@[expose] public section

namespace SteinerUpperBound.SavingScores

open SteinerLowerBound
open scoped Classical BigOperators

variable {X A : Type*} [Fintype X]

noncomputable def fiber (part : X → A) (a : A) : Finset X :=
  Finset.univ.filter (fun x => part x = a)

noncomputable def partSize (part : X → A) (a : A) : ℕ := (fiber part a).card

theorem partSize_pos (part : X → A) (hsurj : Function.Surjective part) (a : A) :
    0 < partSize part a := by
  classical
  obtain ⟨x, hx⟩ := hsurj a
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

theorem reciprocal_bounds (part : X → A) (hsurj : Function.Surjective part) (a : A) :
    0 ≤ 1 / (partSize part a : ℝ) ∧ 1 / (partSize part a : ℝ) ≤ 1 := by
  have hp : (0 : ℝ) < partSize part a := by exact_mod_cast partSize_pos part hsurj a
  have h1 : (1 : ℝ) ≤ partSize part a := by
    exact_mod_cast partSize_pos part hsurj a
  exact ⟨div_nonneg (by norm_num) hp.le, (div_le_one hp).mpr h1⟩

noncomputable def initiationRate (part : X → A) (hsurj : Function.Surjective part)
    (a : A) : Rate := ⟨1 / (partSize part a : ℝ), reciprocal_bounds part hsurj a⟩

variable [Fintype A]

theorem sum_partSize (part : X → A) : ∑ a, partSize part a = Nat.card X := by
  classical
  have hh := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset A)) (f := part)
    (fun x _ => Finset.mem_univ (part x))
  simpa only [partSize, fiber, Finset.card_univ, Nat.card_eq_fintype_card] using hh.symm

theorem fiber_weighted_sum (part : X → A) (hsurj : Function.Surjective part) (w : A → ℝ) :
    (∑ x, w (part x) / (partSize part (part x) : ℝ)) = ∑ a, w a := by
  classical
  have hf (a : A) :
      (∑ x ∈ Finset.univ.filter (fun x => part x = a),
        w (part x) / (partSize part (part x) : ℝ)) = w a := by
    calc
      _ = ∑ _x ∈ Finset.univ.filter (fun x => part x = a),
          w a / (partSize part a : ℝ) :=
        Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])
      _ = (partSize part a : ℝ) * (w a / (partSize part a : ℝ)) := by
        simp only [Finset.sum_const, nsmul_eq_mul, partSize, fiber]
      _ = _ := by
        have hp : (partSize part a : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (partSize_pos part hsurj a))
        field_simp
  have hh := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset A)) (g := part)
    (fun x _ => Finset.mem_univ (part x))
    (fun x => w (part x) / (partSize part (part x) : ℝ))
  simpa only [hf] using hh.symm

omit [Fintype A] in
theorem uniform_expect [Nonempty X] (w : X → ℝ) :
    (Law.uniform X).expect w = (∑ x, w x) / (Nat.card X : ℝ) := by
  simp only [Law.expect, Law.uniform, div_eq_mul_inv, Nat.card_eq_fintype_card,
    ← Finset.sum_mul, mul_comm]

theorem uniform_part_mean [Nonempty X] (part : X → A)
    (hsurj : Function.Surjective part) (w : A → ℝ) :
    (Law.uniform X).expect (fun x => w (part x) / (partSize part (part x) : ℝ)) =
      (∑ a, w a) / (Nat.card X : ℝ) := by
  rw [uniform_expect, fiber_weighted_sum part hsurj w]

theorem large_parts_count (part : X → A) (large : Finset A) (B : ℕ)
    (hlarge : ∀ a ∈ large, B < partSize part a) :
    (B + 1) * large.card ≤ Nat.card X := by
  calc
    _ = ∑ _a ∈ large, (B + 1) := by simp [Nat.mul_comm]
    _ ≤ ∑ a ∈ large, partSize part a := Finset.sum_le_sum (fun a ha => hlarge a ha)
    _ ≤ ∑ a, partSize part a := Finset.sum_le_sum_of_subset (Finset.subset_univ large)
    _ = _ := sum_partSize part

theorem large_parts_div_bound (part : X → A) (large : Finset A) (B : ℕ)
    (hlarge : ∀ a ∈ large, B < partSize part a) :
    (large.card : ℝ) ≤ (Nat.card X : ℝ) / (B + 1) := by
  have hh : ((B : ℝ) + 1) * (large.card : ℝ) ≤ Nat.card X := by
    exact_mod_cast large_parts_count part large B hlarge
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < B + 1)).mpr (by nlinarith)

end SteinerUpperBound.SavingScores

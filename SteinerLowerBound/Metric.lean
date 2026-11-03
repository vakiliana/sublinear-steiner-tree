module

public import Mathlib

@[expose] public section

/-!
# The metric in Section 7

The point types are kept separate here. Relabeling them by a bijection does
not affect the metric axioms.
-/

namespace SteinerLowerBound

inductive Point (S G I C : Type*)
  | special : S → Point S G I C
  | ordinary : G → I → Point S G I C
  | center : C → Point S G I C
  deriving DecidableEq, Fintype

namespace Point

variable {S G I C : Type*}

def sameCluster : Point S G I C → Point S G I C → Prop
  | .ordinary a _, .ordinary b _ => a = b
  | _, _ => False

def unitAdjacent (nb : C → Set S) : Point S G I C → Point S G I C → Prop
  | .special u, .center c => u ∈ nb c
  | .center c, .special u => u ∈ nb c
  | _, _ => False

noncomputable def distance (ell : ℝ) (nb : C → Set S)
    (x y : Point S G I C) : ℝ := by
  classical
  exact if x = y then 0 else
    if sameCluster x y then ell else
    if unitAdjacent nb x y then 1 else 2

@[simp]
theorem distance_self (ell : ℝ) (nb : C → Set S) (x : Point S G I C) :
    distance ell nb x x = 0 := by
  classical
  simp [distance]

theorem distance_comm (ell : ℝ) (nb : C → Set S) (x y : Point S G I C) :
    distance ell nb x y = distance ell nb y x := by
  classical
  cases x <;> cases y <;>
    simp [distance, sameCluster, unitAdjacent, eq_comm] <;> rfl

theorem distance_nonneg {ell : ℝ} (hEll : 0 ≤ ell) (nb : C → Set S)
    (x y : Point S G I C) : 0 ≤ distance ell nb x y := by
  classical
  unfold distance
  split_ifs <;> positivity

theorem distance_le_two {ell : ℝ} (hEll : ell ≤ 2) (nb : C → Set S)
    (x y : Point S G I C) : distance ell nb x y ≤ 2 := by
  classical
  unfold distance
  split_ifs <;> linarith

theorem distance_eq_zero_iff {ell : ℝ} (hEll : 0 < ell) (nb : C → Set S)
    (x y : Point S G I C) : distance ell nb x y = 0 ↔ x = y := by
  classical
  unfold distance
  split_ifs <;> simp_all [ne_of_gt hEll]

theorem distance_triangle {ell : ℝ} (hEll0 : 0 ≤ ell) (hEll2 : ell ≤ 2)
    (nb : C → Set S) (x y z : Point S G I C) :
    distance ell nb x z ≤ distance ell nb x y + distance ell nb y z := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hyz : y = z
  · subst z
    simp
  by_cases hxz : x = z
  · subst z
    simpa using add_nonneg (distance_nonneg hEll0 nb x y)
      (distance_nonneg hEll0 nb y x)
  cases x <;> cases y <;> cases z <;>
    simp_all only [distance, sameCluster, unitAdjacent, ↓reduceIte,
      Point.special.injEq, Point.ordinary.injEq, Point.center.injEq,
      reduceCtorEq] <;>
    (try split_ifs at *) <;> (try simp_all) <;>
    (try split_ifs at *) <;> (try simp_all) <;> linarith

@[instance_reducible]
noncomputable def metricSpace {ell : ℝ} (hEll0 : 0 < ell) (hEll2 : ell ≤ 2)
    (nb : C → Set S) : MetricSpace (Point S G I C) where
  dist := distance ell nb
  dist_self := distance_self ell nb
  dist_comm := distance_comm ell nb
  dist_triangle := distance_triangle hEll0.le hEll2 nb
  eq_of_dist_eq_zero := (distance_eq_zero_iff hEll0 nb _ _).mp

theorem distance_values (ell : ℝ) (nb : C → Set S) (x y : Point S G I C)
    (hxy : x ≠ y) :
    distance ell nb x y = ell ∨ distance ell nb x y = 1 ∨ distance ell nb x y = 2 := by
  classical
  simp only [distance, ite_eq_right hxy]
  split_ifs <;> simp

def terminals : Set (Point S G I C)
  | .center _ => False
  | _ => True

def equivSum : Point S G I C ≃ S ⊕ (G × I) ⊕ C :=
    { toFun := fun
        | .special u => .inl u
        | .ordinary a i => .inr (.inl (a, i))
        | .center c => .inr (.inr c)
      invFun := fun
        | .inl u => .special u
        | .inr (.inl (a, i)) => .ordinary a i
        | .inr (.inr c) => .center c
      left_inv := by intro x; cases x <;> rfl
      right_inv := by rintro (u | (⟨a, i⟩ | c)) <;> rfl }

theorem sum_eq [Fintype S] [Fintype G] [Fintype I] [Fintype C]
    {M : Type*} [AddCommMonoid M] (f : Point S G I C → M) :
    (∑ p, f p) = (∑ u, f (.special u)) +
      (∑ a, ∑ i, f (.ordinary a i)) + ∑ c, f (.center c) := by
  classical
  calc
    _ = ∑ z : S ⊕ (G × I) ⊕ C, f (equivSum.symm z) :=
      Fintype.sum_equiv equivSum f _ (fun x => by simp)
    _ = _ := by simp [equivSum, Fintype.sum_sum_type, Fintype.sum_prod_type, add_assoc]

theorem card_points [Fintype S] [Fintype G] [Fintype I] [Fintype C] :
    Fintype.card (Point S G I C) =
      Fintype.card S + Fintype.card G * Fintype.card I + Fintype.card C := by
  rw [Fintype.card_congr (equivSum : Point S G I C ≃ S ⊕ (G × I) ⊕ C)]
  simp [Nat.add_assoc]

end Point

end SteinerLowerBound

module

public import SteinerUpperBound.Matching.Padded.CollectionCost
public import SteinerUpperBound.Matching.Padded.Ready

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open scoped Classical BigOperators

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) [Fintype V]

def sortingCredit (H : ℕ) (s : Cache S Q) : ℝ :=
  ∑ v, ((H : ℝ) - s.level v) * (s.known v).length

theorem sortingCredit_nonneg (H : ℕ) (s : Cache S Q) (hlevel : ∀ v, s.level v ≤ H) :
    0 ≤ sortingCredit S Q H s :=
  Finset.sum_nonneg fun v _ =>
    mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hlevel v)) (Nat.cast_nonneg _)

theorem assign_known_length (s : Cache S Q) (x : Entry S Q) (hx : EntryValid S Q x) (v : V) :
    ((assign S Q s x.source x.reverse x.edge x.rank).known v).length =
      (s.known v).length + (if v = x.source.1 then 1 else 0) +
        (if v = x.reverse.1 then 1 else 0) := by
  classical
  have hne := (S.test_incident hx).2.2
  by_cases hv : v = x.source.1
  · simp [assign, hv, hne]
  · by_cases hr : v = x.reverse.1
    · simp [assign, hr, hne.symm]
    · simp [assign, Function.update_of_ne hv, Function.update_of_ne hr, hv, hr]

theorem assign_knownValue (s : Cache S Q) (x : Entry S Q) (hx : EntryValid S Q x) (w : V → ℝ) :
    (∑ v, w v * (((assign S Q s x.source x.reverse x.edge x.rank).known v).length : ℝ)) =
      (∑ v, w v * ((s.known v).length : ℝ)) + w x.source.1 + w x.reverse.1 := by
  simp_rw [assign_known_length S Q s x hx]
  push_cast
  simp [mul_add, mul_ite, Finset.sum_add_distrib]

theorem assign_sortingCredit (H : ℕ) (s : Cache S Q) (x : Entry S Q) (hx : EntryValid S Q x) :
    sortingCredit S Q H (assign S Q s x.source x.reverse x.edge x.rank) =
      sortingCredit S Q H s + ((H : ℝ) - s.level x.source.1) +
        ((H : ℝ) - s.level x.reverse.1) :=
  assign_knownValue S Q s x hx (fun v => (H : ℝ) - s.level v)

theorem assign_sortingCredit_le (H : ℕ) (s : Cache S Q) (x : Entry S Q) (hx : EntryValid S Q x) :
    sortingCredit S Q H (assign S Q s x.source x.reverse x.edge x.rank) ≤
      sortingCredit S Q H s + 2 * H := by
  rw [assign_sortingCredit S Q H s x hx]
  linarith [Nat.cast_nonneg (α := ℝ) (s.level x.source.1),
    Nat.cast_nonneg (α := ℝ) (s.level x.reverse.1)]

theorem commit_sortingCredit_le (H : ℕ) (s : Cache S Q) (xs : List (Entry S Q))
    (hx : ∀ x ∈ xs, EntryValid S Q x) :
    sortingCredit S Q H (commit S Q s xs) ≤ sortingCredit S Q H s + 2 * H * xs.length := by
  induction xs generalizing s with
  | nil => simp [commit]
  | cons x xs ih =>
    have hf := assign_sortingCredit_le S Q H s x (hx x (by simp))
    have ht := ih (assign S Q s x.source x.reverse x.edge x.rank) (fun y hy => hx y (by simp [hy]))
    change sortingCredit S Q H
      (commit S Q (assign S Q s x.source x.reverse x.edge x.rank) xs) ≤ _
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem rebuild_sortingCredit (H height : ℕ) (v : V) (s : Cache S Q) :
    sortingCredit S Q H (rebuild S Q height v (s.level v + 1) s) =
      sortingCredit S Q H s - (s.known v).length := by
  classical
  have hp (u : V) :
      ((H : ℝ) - ((rebuild S Q height v (s.level v + 1) s).level u : ℝ)) *
          (((rebuild S Q height v (s.level v + 1) s).known u).length : ℝ) =
        ((H : ℝ) - s.level u) * (s.known u).length -
          (if u = v then ((s.known v).length : ℝ) else 0) := by
    by_cases hu : u = v
    · subst u
      simp only [rebuild, Function.update_self, Nat.cast_add, Nat.cast_one, ↓reduceIte]
      ring
    · simp only [rebuild, Function.update_of_ne hu, hu, ↓reduceIte, sub_zero]
  unfold sortingCredit
  simp_rw [hp]
  rw [Finset.sum_sub_distrib]
  simp

theorem finish_sortingCredit (H height : ℕ) (v : V) (s : Cache S Q) (xs : List (Entry S Q)) :
    sortingCredit S Q H (finish S Q height v s xs).value =
      sortingCredit S Q H (commit S Q s xs) - ((commit S Q s xs).known v).length := by
  have hl := congrFun (Kernel.commit_levels S Q s xs) v
  change sortingCredit S Q H
    (rebuild S Q height v (s.level v + 1) (commit S Q s xs)) = _
  rw [← hl]
  exact rebuild_sortingCredit S Q H height v _

def sortScale (height : ℕ) : ℕ := 72 * (height + 1)

def credit (A : Account S) (H height : ℕ) (s : Cache S Q) : ℝ :=
  A.rate * sortScale height * sortingCredit S Q H s

theorem finish_amortized (A : Account S) (H height : ℕ) (v : V) (s : Cache S Q)
    (xs : List (Entry S Q)) (hx : ∀ x ∈ xs, EntryValid S Q x) :
    A.rate * (finish S Q height v s xs).operations +
        credit S Q A H height (finish S Q height v s xs).value ≤
      credit S Q A H height s +
        A.rate * ((32 + 2 * H * sortScale height : ℕ) * (xs.length : ℝ) + sortScale height + 4) := by
  have hc := commit_sortingCredit_le S Q H s xs hx
  have hs := Sort.array_operations (fun x y : Entry S Q => decide (x.rank.val ≤ y.rank.val))
    height ((commit S Q s xs).known v)
  have hs' :
      (Sort.array (fun x y : Entry S Q => decide (x.rank.val ≤ y.rank.val))
        height ((commit S Q s xs).known v)).operations ≤
      sortScale height * (((commit S Q s xs).known v).length + 1) := by
    simpa only [sortScale, Nat.mul_right_comm] using hs
  have hop : ((finish S Q height v s xs).operations : ℝ) ≤
      32 * (xs.length : ℝ) +
        (sortScale height : ℝ) * (((commit S Q s xs).known v).length + 1) + 4 := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.add_le_add_left hs' (32 * xs.length)) 4
  unfold credit
  rw [finish_sortingCredit]
  have hm := mul_le_mul_of_nonneg_left hc
    (mul_nonneg A.rate_nonneg (Nat.cast_nonneg (sortScale height) : (0 : ℝ) ≤ _))
  have ho := mul_le_mul_of_nonneg_left hop A.rate_nonneg
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at *
  nlinarith

end SteinerUpperBound.Matching.Padded.Cache

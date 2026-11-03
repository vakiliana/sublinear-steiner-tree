module

public import SteinerUpperBound.Model

@[expose] public section

namespace SteinerUpperBound.WeightedSelection

open scoped BigOperators

variable {α : Type*}

def count (p : α → Bool) (l : List α) : ℕ := (l.filter p).length

noncomputable def weighted (w : α → ℝ) (p : α → Bool) (l : List α) : ℝ :=
  ((l.filter p).map w).sum

theorem centered_sum (l : List α) (w : α → ℝ) (a : ℝ) :
    (l.map (fun x => w x - a)).sum = (l.map w).sum - l.length * a := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, ih]
      ring

theorem head_decomposition (a : α) (l : List α) (w : α → ℝ) (p : α → Bool) :
    weighted w p (a :: l) =
      w a * count p (a :: l) + weighted (fun x => w x - w a) p l := by
  unfold weighted count
  rw [centered_sum]
  cases hp : p a <;>
    simp only [List.filter_cons, hp, Bool.false_eq_true,
      ite_false, ite_true, List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one] <;> ring

theorem weighted_eq_sum (w : α → ℝ) (p : α → Bool) (l : List α) :
    weighted w p l = (l.map (fun x => if p x then w x else 0)).sum := by
  induction l with
  | nil => simp [weighted]
  | cons a l ih =>
      cases hp : p a <;> simp [weighted, hp] at ih ⊢ <;> exact ih

theorem le_of_tail_counts (l : List α) (w : α → ℝ) (p q : α → Bool)
    (hw : ∀ x ∈ l, 0 ≤ w x)
    (hs : l.Pairwise (fun x y => w x ≤ w y))
    (ht : ∀ i : ℕ, count p (l.drop i) ≤ count q (l.drop i)) :
    weighted w p l ≤ weighted w q l := by
  induction l generalizing w with
  | nil => simp [weighted]
  | cons a l ih =>
      have hpair := List.pairwise_cons.mp hs
      have hw' : ∀ x ∈ l, 0 ≤ w x - w a := by
        intro x hx
        exact sub_nonneg.mpr (hpair.1 x hx)
      have hs' : l.Pairwise (fun x y => w x - w a ≤ w y - w a) := by
        apply hpair.2.imp
        intro x y hxy
        exact sub_le_sub_right hxy _
      have ht' : ∀ i : ℕ, count p (l.drop i) ≤ count q (l.drop i) := by
        intro i
        simpa only [List.drop_succ_cons] using ht (i + 1)
      have htail := ih (fun x => w x - w a) hw' hs' ht'
      have hc : (count p (a :: l) : ℝ) ≤ count q (a :: l) := by
        have h0 := ht 0
        simp only [List.drop_zero] at h0
        exact_mod_cast h0
      have ha : 0 ≤ w a := hw a List.mem_cons_self
      calc
        _ = w a * count p (a :: l) + weighted (fun x => w x - w a) p l :=
          head_decomposition a l w p
        _ ≤ w a * count q (a :: l) + weighted (fun x => w x - w a) q l :=
          add_le_add (mul_le_mul_of_nonneg_left hc ha) htail
        _ = _ := (head_decomposition a l w q).symm

theorem sorted_cut (l : List α) (w : α → ℝ) (a : ℝ)
    (hs : l.Pairwise (fun x y => w x ≤ w y)) :
    l.takeWhile (fun x => decide (w x < a)) = l.filter (fun x => decide (w x < a)) ∧
      ∀ x ∈ l.dropWhile (fun x => decide (w x < a)), a ≤ w x := by
  induction l with
  | nil => simp
  | cons y l ih =>
      have hpair := List.pairwise_cons.mp hs
      have htail := ih hpair.2
      by_cases hy : w y < a
      · constructor
        · simpa [List.takeWhile, hy] using congrArg (List.cons y) htail.1
        · simpa [List.dropWhile, hy] using htail.2
      · have hall : ∀ x ∈ y :: l, a ≤ w x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact le_of_not_gt hy
          · exact (le_of_not_gt hy).trans (hpair.1 x hx)
        have hf : (y :: l).filter (fun x => decide (w x < a)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro x hx
          simpa only [decide_eq_true_eq, not_lt] using hall x hx
        constructor
        · simp [List.takeWhile, hy, hf]
        · simpa [List.dropWhile, hy] using hall

end SteinerUpperBound.WeightedSelection

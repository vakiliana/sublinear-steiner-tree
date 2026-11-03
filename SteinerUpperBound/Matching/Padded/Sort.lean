module

public import SteinerUpperBound.Matching.Padded.Buckets

@[expose] public section

/-!
# Charged sorting of discovered copies

These routines operate only on already discovered copy records. They never
inspect a candidate slot. List splitting, comparisons, allocation, and copying
into the random-access cache are all included in the operation counter.
-/

namespace SteinerUpperBound.Matching.Padded.Sort

open scoped Classical

variable {A : Type*}

def merge (le : A → A → Bool) : List A → List A → Arithmetic (List A)
  | [], ys => ⟨ys, 1⟩
  | xs, [] => ⟨xs, 1⟩
  | x :: xs, y :: ys =>
    if le x y then
      let r := merge le xs (y :: ys)
      ⟨x :: r.value, r.operations + 6⟩
    else
      let r := merge le (x :: xs) ys
      ⟨y :: r.value, r.operations + 6⟩
termination_by xs ys => xs.length + ys.length

theorem merge_value (le : A → A → Bool) (xs ys : List A) :
    (merge le xs ys).value = xs.merge ys le := by
  cases xs with
  | nil => simp [merge]
  | cons x xs =>
    cases ys with
    | nil => simp [merge]
    | cons y ys =>
      rw [merge, List.cons_merge_cons]
      split_ifs
      · exact congrArg (List.cons x) (merge_value le xs (y :: ys))
      · exact congrArg (List.cons y) (merge_value le (x :: xs) ys)
termination_by xs.length + ys.length

theorem merge_operations (le : A → A → Bool) (xs ys : List A) :
    (merge le xs ys).operations ≤ 8 * (xs.length + ys.length + 1) := by
  cases xs with
  | nil => simp [merge]; omega
  | cons x xs =>
    cases ys with
    | nil => simp [merge]; omega
    | cons y ys =>
      have hl := merge_operations le xs (y :: ys)
      have hr := merge_operations le (x :: xs) ys
      rw [merge]
      split_ifs <;> dsimp only <;> simp only [List.length_cons] at * <;> omega
termination_by xs.length + ys.length

def sample (le : A → A → Bool) : ℕ → List A → Arithmetic (List A)
  | 0, xs => ⟨xs, 1⟩
  | h + 1, xs =>
    if xs.length ≤ 1 then ⟨xs, 1⟩ else
      let k := xs.length / 2
      let l := sample le h (xs.take k)
      let r := sample le h (xs.drop k)
      let m := merge le l.value r.value
      ⟨m.value, l.operations + r.operations + m.operations + 8 * (xs.length + 1)⟩

theorem sample_perm (le : A → A → Bool) (h : ℕ) (xs : List A) :
    (sample le h xs).value.Perm xs := by
  induction h generalizing xs with
  | zero => exact List.Perm.refl _
  | succ h ih =>
    rw [sample]
    split_ifs
    · exact List.Perm.refl _
    · dsimp only
      rw [merge_value]
      have hp := (List.merge_perm_append le).trans
        ((ih (xs.take (xs.length / 2))).append (ih (xs.drop (xs.length / 2))))
      simpa only [List.take_append_drop] using hp

theorem short_pairwise (R : A → A → Prop) (xs : List A) (h : xs.length ≤ 1) :
    xs.Pairwise R := by
  cases xs with
  | nil => simp
  | cons x xs =>
    have he : xs = [] := by
      apply List.length_eq_zero_iff.mp
      simp only [List.length_cons] at h
      omega
    simp [he]

theorem sample_pairwise (R : A → A → Prop) [DecidableRel R] [Std.Total R] [IsTrans A R]
    (h : ℕ) (xs : List A) (hlen : xs.length ≤ 2 ^ h) :
    (sample (fun a b => decide (R a b)) h xs).value.Pairwise R := by
  induction h generalizing xs with
  | zero => exact short_pairwise R xs (by simpa using hlen)
  | succ h ih =>
    rw [sample]
    split_ifs with hshort
    · exact short_pairwise R xs hshort
    · have hh := Binary.halves h xs.length (by omega) hlen
      dsimp only
      rw [merge_value]
      apply List.Pairwise.merge
      · apply ih
        rw [List.length_take_of_le (Nat.div_le_self _ _)]
        exact hh.2.2.1
      · apply ih
        simpa only [List.length_drop] using hh.2.2.2

theorem sample_operations (le : A → A → Bool) (h : ℕ) (xs : List A) :
    (sample le h xs).operations ≤ 64 * xs.length * (h + 1) + 1 := by
  induction h generalizing xs with
  | zero => simp [sample]
  | succ h ih =>
    rw [sample]
    split_ifs with hshort
    · dsimp only
      omega
    · have hl := ih (xs.take (xs.length / 2))
      have hr := ih (xs.drop (xs.length / 2))
      have hm := merge_operations le
        (sample le h (xs.take (xs.length / 2))).value
        (sample le h (xs.drop (xs.length / 2))).value
      rw [(sample_perm le h _).length_eq, (sample_perm le h _).length_eq] at hm
      rw [List.length_take_of_le (Nat.div_le_self _ _)] at hl hm
      rw [List.length_drop] at hr hm
      dsimp only
      have hk := Nat.div_le_self xs.length 2
      have hsplit : xs.length / 2 + (xs.length - xs.length / 2) = xs.length := by omega
      nlinarith

def array (le : A → A → Bool) (h : ℕ) (xs : List A) : Arithmetic (Array A) :=
  let r := sample le h xs
  ⟨r.value.toArray, r.operations + r.value.length + 2⟩

theorem array_operations (le : A → A → Bool) (h : ℕ) (xs : List A) :
    (array le h xs).operations ≤ 72 * (xs.length + 1) * (h + 1) := by
  have hs := sample_operations le h xs
  have hl := (sample_perm le h xs).length_eq
  dsimp only [array]
  rw [hl]
  nlinarith

theorem array_perm (le : A → A → Bool) (h : ℕ) (xs : List A) :
    (array le h xs).value.toList.Perm xs := by
  simpa only [array, List.toList_toArray] using sample_perm le h xs

theorem array_pairwise (R : A → A → Prop) [DecidableRel R] [Std.Total R] [IsTrans A R]
    (h : ℕ) (xs : List A) (hlen : xs.length ≤ 2 ^ h) :
    (array (fun a b => decide (R a b)) h xs).value.toList.Pairwise R := by
  simpa only [array, List.toList_toArray] using sample_pairwise R h xs hlen

end SteinerUpperBound.Matching.Padded.Sort

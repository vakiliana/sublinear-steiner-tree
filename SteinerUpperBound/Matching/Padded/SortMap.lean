module

public import SteinerUpperBound.Matching.Padded.Sort

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Sort

open scoped Classical

variable {A B : Type*} (f : A → B) (leA : A → A → Bool) (leB : B → B → Bool)
    (hle : ∀ a b, leB (f a) (f b) = leA a b)

include hle

theorem merge_map (xs ys : List A) :
    (merge leB (xs.map f) (ys.map f)).value = (merge leA xs ys).value.map f ∧
      (merge leB (xs.map f) (ys.map f)).operations = (merge leA xs ys).operations := by
  cases xs with
  | nil => simp [merge]
  | cons x xs =>
    cases ys with
    | nil => simp [merge]
    | cons y ys =>
      have hl := merge_map xs (y :: ys)
      have hr := merge_map (x :: xs) ys
      simp only [List.map_cons] at hl hr
      simp only [List.map_cons]
      rw [merge, merge]
      rw [hle]
      cases hb : leA x y with
      | true =>
        simp only [↓reduceIte, List.map_cons]
        exact ⟨congrArg (List.cons (f x)) hl.1, congrArg (fun n => n + 6) hl.2⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons]
        exact ⟨congrArg (List.cons (f y)) hr.1, congrArg (fun n => n + 6) hr.2⟩
termination_by xs.length + ys.length
decreasing_by all_goals (simp_wf <;> omega)

theorem sample_map (height : ℕ) (xs : List A) :
    (sample leB height (xs.map f)).value = (sample leA height xs).value.map f ∧
      (sample leB height (xs.map f)).operations = (sample leA height xs).operations := by
  induction height generalizing xs with
  | zero => simp [sample]
  | succ height ih =>
    rw [sample, sample]
    simp only [List.length_map]
    by_cases hs : xs.length ≤ 1
    · simp [hs]
    · simp only [hs, ↓reduceIte, ← List.map_take, ← List.map_drop]
      have hl := ih (xs.take (xs.length / 2))
      have hr := ih (xs.drop (xs.length / 2))
      simp only [hl.1, hr.1, hl.2, hr.2]
      have hm := merge_map f leA leB hle
        (sample leA height (xs.take (xs.length / 2))).value
        (sample leA height (xs.drop (xs.length / 2))).value
      exact ⟨hm.1, by rw [hm.2]⟩

theorem array_map (height : ℕ) (xs : List A) :
    (array leB height (xs.map f)).value.toList = (array leA height xs).value.toList.map f ∧
      (array leB height (xs.map f)).operations = (array leA height xs).operations := by
  have hs := sample_map f leA leB hle height xs
  simp [array, hs.1, hs.2]

end SteinerUpperBound.Matching.Padded.Sort

module

public import SteinerUpperBound.ReusableSample.Transfer

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

noncomputable def logistic (b H c : ℝ) : Rate :=
  ⟨1 / (1 + Real.exp ((H - c) / b)),
    (by positivity), (by
      apply (div_le_one (by positivity : 0 < 1 + Real.exp ((H - c) / b))).mpr
      linarith [Real.exp_pos ((H - c) / b)])⟩

noncomputable def increment (b : ℝ) : ℝ := Real.exp (1 / b) - 1

theorem increment_pos {b : ℝ} (hb : 0 < b) : 0 < increment b := by
  have he := Real.one_lt_exp_iff.mpr (one_div_pos.mpr hb)
  dsimp [increment]
  linarith

theorem logistic_shift (b H c : ℝ) :
    (logistic b H (c + 1) : ℝ) =
      (1 + increment b) * (logistic b H c : ℝ) /
        (1 + increment b * (logistic b H c : ℝ)) := by
  have he : Real.exp ((H - (c + 1)) / b) =
      Real.exp ((H - c) / b) / Real.exp (1 / b) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  dsimp [logistic, increment]
  rw [he]
  have h₀ := Real.exp_pos ((H - c) / b)
  have h₁ := Real.exp_pos (1 / b)
  generalize Real.exp ((H - c) / b) = a at *
  generalize Real.exp (1 / b) = r at *
  have hd : 1 + (r - 1) * (1 / (1 + a)) = (a + r) / (1 + a) := by
    field_simp
    ring
  rw [hd]
  field_simp [show a + r ≠ 0 from (add_pos h₀ h₁).ne']
  ring

theorem logistic_accept_bound (b H c : ℝ) :
    (logistic b H c : ℝ) ≤ Real.exp (-(H - c) / b) := by
  have he : Real.exp (-(H - c) / b) * Real.exp ((H - c) / b) = 1 := by
    rw [← Real.exp_add]
    rw [show -(H - c) / b + (H - c) / b = 0 by ring, Real.exp_zero]
  change 1 / (1 + Real.exp ((H - c) / b)) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 1 + Real.exp ((H - c) / b))).mpr
  nlinarith [Real.exp_pos (-(H - c) / b)]

theorem logistic_reject_bound (b H c : ℝ) :
    1 - (logistic b H c : ℝ) ≤ Real.exp ((H - c) / b) := by
  have hd : 0 < 1 + Real.exp ((H - c) / b) := by positivity
  change 1 - 1 / (1 + Real.exp ((H - c) / b)) ≤ _
  have he := (div_mul_cancel₀ (1 : ℝ) hd.ne')
  nlinarith [sq_nonneg (Real.exp ((H - c) / b))]

section Records

variable {U I : Type*} [Fintype I] [DecidableEq I]

noncomputable def contains (A : Finset U) (x : Option U) : Prop :=
  ∃ u ∈ A, x = some u

@[simp]
theorem contains_none (A : Finset U) : ¬ contains A none := by
  simp [contains]

@[simp]
theorem contains_some (A : Finset U) (u : U) : contains A (some u) ↔ u ∈ A := by
  simp [contains]

theorem contains_union (A B : Finset U) (x : Option U) :
    contains (A ∪ B) x ↔ contains A x ∨ contains B x := by
  cases x <;> simp

theorem contains_sdiff (A B : Finset U) (x : Option U) :
    contains (A \ B) x ↔ contains A x ∧ ¬ contains B x := by
  cases x <;> simp

noncomputable def liveCount (X : I → Option U) (A : Finset U) : ℝ :=
  ∑ i, if contains A (X i) then 1 else 0

omit [DecidableEq I] in
theorem liveCount_nonneg (X : I → Option U) (A : Finset U) : 0 ≤ liveCount X A :=
  Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

omit [DecidableEq I] in
theorem liveCount_le (X : I → Option U) (A : Finset U) :
    liveCount X A ≤ Fintype.card I := by
  calc
    _ ≤ ∑ _ : I, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
    _ = _ := by simp

omit [DecidableEq I] in
theorem liveCount_card (X : I → Option U) (A : Finset U) :
    liveCount X A = ((Finset.univ.filter fun i => contains A (X i)).card : ℝ) := by
  rw [liveCount, ← Finset.sum_filter]
  simp

theorem liveCount_update (X : I → Option U) (i : I) (A : Finset U) (u : U) :
    liveCount (Function.update X i (some u)) A =
      liveCount (Function.update X i none) A + if u ∈ A then 1 else 0 := by
  unfold liveCount
  rw [Fintype.sum_eq_add_sum_compl i, Fintype.sum_eq_add_sum_compl i]
  simp only [Function.update_self, contains_some, contains_none, ↓reduceIte]
  have he : (∑ j ∈ ({i}ᶜ : Finset I),
      if contains A (Function.update X i (some u) j) then (1 : ℝ) else 0) =
      ∑ j ∈ ({i}ᶜ : Finset I), if contains A (Function.update X i none j) then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp only [Function.update_of_ne hji]
  rw [he]
  ring

def zeroRate : Rate := ⟨0, by norm_num, by norm_num⟩

def rejectAll : (n : ℕ) → Tree n
  | 0 => .leaf
  | n + 1 => .node zeroRate (rejectAll n) (rejectAll n)

/-- The actual pool algorithm. Its only output is the ordered acceptance bits.
`C` is the union of rows already accepted; absent records are used only in the
neighboring-dataset proof. Both `H` and the row order stay fixed. -/
noncomputable def poolTree (b H : ℝ) (X : I → Option U) :
    {n : ℕ} → (Fin n → Finset U) → ℕ → Finset U → Tree n
  | 0, _, _, _ => .leaf
  | n + 1, R, t, C =>
      if t = 0 then rejectAll (n + 1)
      else .node (logistic b H (liveCount X (R 0 \ C)))
        (poolTree b H X (fun j => R j.succ) t C)
        (poolTree b H X (fun j => R j.succ) (t - 1) (C ∪ R 0))

/-- The records which have not been deleted by the already selected rows. -/
noncomputable def liveRecords (X : I → Option U) (C : Finset U) : Finset I :=
  Finset.univ.filter fun i => ¬ contains C (X i)

noncomputable def hits (X : I → Option U) (L : Finset I) (A : Finset U) : Finset I :=
  L.filter fun i => contains A (X i)

omit [DecidableEq I] in
theorem hits_liveRecords (X : I → Option U) (C A : Finset U) :
    hits X (liveRecords X C) A =
      Finset.univ.filter fun i => contains (A \ C) (X i) := by
  ext i
  simp only [hits, liveRecords, Finset.mem_filter, Finset.mem_univ, true_and, contains_sdiff]
  tauto

theorem delete_liveRecords (X : I → Option U) (C A : Finset U) :
    liveRecords X C \ hits X (liveRecords X C) A = liveRecords X (C ∪ A) := by
  ext i
  simp only [liveRecords, hits, Finset.mem_sdiff, Finset.mem_filter,
    Finset.mem_univ, true_and, contains_union]
  tauto

omit [DecidableEq I] in
theorem liveRecords_empty (X : I → Option U) : liveRecords X ∅ = Finset.univ := by
  ext i
  simp [liveRecords, contains]

/-- Implementation using only live record flags. Each tested row is scanned once
on the live records, and the saved hit list is deleted on acceptance. No union
of true universe elements is computed by this implementation. -/
noncomputable def liveTree (b H : ℝ) (X : I → Option U) :
    {n : ℕ} → (Fin n → Finset U) → ℕ → Finset I → Tree n
  | 0, _, _, _ => .leaf
  | n + 1, R, t, L =>
      if t = 0 then rejectAll (n + 1)
      else
        let hit := hits X L (R 0)
        .node (logistic b H hit.card)
          (liveTree b H X (fun j => R j.succ) t L)
          (liveTree b H X (fun j => R j.succ) (t - 1) (L \ hit))

theorem poolTree_eq_liveTree (b H : ℝ) (X : I → Option U) {n : ℕ}
    (R : Fin n → Finset U) (t : ℕ) (C : Finset U) :
    poolTree b H X R t C = liveTree b H X R t (liveRecords X C) := by
  induction n generalizing t C with
  | zero => rfl
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [poolTree, liveTree, ht, ↓reduceIte]
      · simp only [poolTree, liveTree, ht, ↓reduceIte]
        rw [hits_liveRecords, ← liveCount_card]
        rw [ih (fun j => R j.succ) t C, ih (fun j => R j.succ) (t - 1) (C ∪ R 0)]
        rw [← delete_liveRecords]
        rw [hits_liveRecords]

/-- Membership-test count, including the complete scan that produces the saved
hit list. Deletion of that list does not make further row membership tests. -/
noncomputable def liveWork (X : I → Option U) :
    {n : ℕ} → (Fin n → Finset U) → ℕ → Finset I → (Fin n → Bool) → ℕ
  | 0, _, _, _, _ => 0
  | _ + 1, R, t, L, T =>
      if t = 0 then 0
      else L.card + liveWork X (fun j => R j.succ) (if T 0 then t - 1 else t)
        (if T 0 then L \ hits X L (R 0) else L) (fun j => T j.succ)

theorem liveWork_le (X : I → Option U) {n : ℕ} (R : Fin n → Finset U)
    (t : ℕ) (L : Finset I) (T : Fin n → Bool) :
    liveWork X R t L T ≤ n * Fintype.card I := by
  induction n generalizing t L with
  | zero => simp [liveWork]
  | succ n ih =>
      by_cases ht : t = 0
      · simp [liveWork, ht]
      · simp only [liveWork, ht, ↓reduceIte]
        have hh := ih (fun j => R j.succ) (if T 0 then t - 1 else t)
          (if T 0 then L \ hits X L (R 0) else L) (fun j => T j.succ)
        have hc := Finset.card_le_univ L
        nlinarith

noncomputable def queryWork {Ns n : ℕ} (R : Fin n → Finset U) (t : ℕ)
    (X : Fin Ns → U) (T : Fin n → Bool) : ℕ :=
  liveWork (fun i => some (X i)) R t Finset.univ T

theorem queryWork_le {Ns n : ℕ} (R : Fin n → Finset U) (t : ℕ)
    (X : Fin Ns → U) (T : Fin n → Bool) : queryWork R t X T ≤ n * Ns := by
  simpa only [queryWork, Fintype.card_fin] using
    liveWork_le (fun i => some (X i)) R t Finset.univ T

theorem poolTree_covered (b H : ℝ) (X : I → Option U) (i : I) (u : U)
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (C : Finset U) (hu : u ∈ C) :
    poolTree b H (Function.update X i none) R t C =
      poolTree b H (Function.update X i (some u)) R t C := by
  induction n generalizing t C with
  | zero => rfl
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [poolTree, ht, ↓reduceIte]
      · have hc : u ∉ R 0 \ C := by simp [hu]
        simp only [poolTree, ht, ↓reduceIte]
        rw [liveCount_update, ite_eq_right hc, add_zero]
        rw [ih (fun j => R j.succ) t C hu]
        rw [ih (fun j => R j.succ) (t - 1) (C ∪ R 0) (Finset.mem_union_left _ hu)]

theorem poolTree_addition (b H : ℝ) (X : I → Option U) (i : I) (u : U)
    {n : ℕ} (R : Fin n → Finset U) (t : ℕ) (C : Finset U) :
    Tree.Addition (increment b)
      (poolTree b H (Function.update X i none) R t C)
      (poolTree b H (Function.update X i (some u)) R t C) := by
  induction n generalizing t C with
  | zero => exact .same _
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [poolTree, ht, ↓reduceIte]
        exact .same _
      · simp only [poolTree, ht, ↓reduceIte]
        by_cases hu : u ∈ R 0 \ C
        · have he := poolTree_covered b H X i u (fun j => R j.succ)
            (t - 1) (C ∪ R 0) (Finset.mem_union_right _ (Finset.mem_sdiff.mp hu).1)
          rw [← he]
          apply Tree.Addition.relevant
          · rw [liveCount_update, ite_eq_left hu]
            exact logistic_shift b H _
          · exact ih (fun j => R j.succ) t C
        · rw [liveCount_update, ite_eq_right hu, add_zero]
          exact Tree.Addition.irrelevant _
            (ih (fun j => R j.succ) t C)
            (ih (fun j => R j.succ) (t - 1) (C ∪ R 0))

noncomputable def mechanism (b : ℝ) (Ns t : ℕ) {n : ℕ} (R : Fin n → Finset U)
    (X : Fin Ns → U) : Law (Fin n → Bool) :=
  (liveTree b (2 * Ns / t) (fun i => some (X i)) R t Finset.univ).law

theorem mechanism_as_pool (b : ℝ) (Ns t : ℕ) {n : ℕ} (R : Fin n → Finset U)
    (X : Fin Ns → U) :
    mechanism b Ns t R X =
      (poolTree b (2 * Ns / t) (fun i => some (X i)) R t ∅).law := by
  rw [poolTree_eq_liveTree, liveRecords_empty]
  rfl

/-- Replacement stability, with the absent record as the common intermediate.
One of the two addition comparisons is exact, improving the usual composition
bound slightly. -/
theorem mechanism_stable (b : ℝ) (hb : 0 < b) (Ns t : ℕ) {n : ℕ}
    (R : Fin n → Finset U) (L : ℝ) (hL : 0 ≤ L)
    (X : Fin Ns → U) (i : Fin Ns) (y : U) :
    Probability.Dominated (mechanism b Ns t R X)
      (mechanism b Ns t R (@Function.update (Fin Ns) (fun _ => U) (Classical.decEq _) X i y))
      ((1 + increment b) * Real.exp (increment b * L))
      ((1 + increment b) * Real.exp (-L)) := by
  classical
  let : DecidableEq (Fin Ns) := Classical.decEq _
  let Z : Fin Ns → Option U := fun j => some (X j)
  have hz : Function.update Z i (some (X i)) = Z := Function.update_eq_self _ _
  have hy : Function.update Z i (some y) = fun j => some (Function.update X i y j) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj, Z]
  have h₀ := poolTree_addition b (2 * Ns / t) Z i (X i) R t ∅
  have h₁ := poolTree_addition b (2 * Ns / t) Z i y R t ∅
  rw [hz] at h₀
  have hq := increment_pos hb
  intro E
  have hf := h₀.forward hq.le E
  have hr := h₁.reverse hq L hL E
  rw [hy] at hr
  have hm := mul_le_mul_of_nonneg_left hr (by linarith : 0 ≤ 1 + increment b)
  rw [mechanism_as_pool, mechanism_as_pool]
  dsimp [Z] at *
  nlinarith

end Records

end SteinerUpperBound.ReusableSample

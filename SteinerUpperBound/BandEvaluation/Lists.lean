module

public import SteinerUpperBound.FiniteMST

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {n : ℕ}

def member (x : Fin n) : List (Fin n) → Code M Q Bool
  | [] => .tick 0 (.pure false)
  | y :: l => .tick 2 (if x = y then .pure true else member x l)

def memberRun (x : Fin n) : List (Fin n) → Outcome Bool
  | [] => ⟨false, 1, 0, 0, 0⟩
  | y :: l => if x = y then ⟨true, 3, 0, 0, 0⟩ else (memberRun x l).add 3 0 0 0

def unique : List (Fin n) → List (Fin n) → Code M Q (List (Fin n))
  | [], acc => .pure acc
  | x :: l, acc => .tick 0 ((member x acc).bind
      (fun hit => .tick 1 (unique l (if hit then acc else x :: acc))))

def uniqueRun : List (Fin n) → List (Fin n) → Outcome (List (Fin n))
  | [], acc => .pure acc
  | x :: l, acc => ((memberRun x acc).combine
      ((uniqueRun l (if (memberRun x acc).value then acc else x :: acc)).add 2 0 0 0)).add 1 0 0 0

def augment (l : List (Fin n)) (v : Fin n) : Code M Q (List (Fin n)) :=
  (member v l).bind (fun hit => .tick 1 (.pure (if hit then l else v :: l)))

def augmentRun (l : List (Fin n)) (v : Fin n) : Outcome (List (Fin n)) :=
  (memberRun v l).combine
    ((Outcome.pure (if (memberRun v l).value then l else v :: l)).add 2 0 0 0)

theorem member_evaluates (oracle : M → ℝ) (bits : Q → Bool) (x : Fin n) (l) :
    Code.Evaluates oracle bits (member x l) (memberRun x l) := by
  induction l with
  | nil => exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 0
  | cons y l ih =>
      unfold member memberRun
      split_ifs
      · exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 2
      · exact Code.Evaluates.tick _ _ _ _ ih 2

theorem unique_evaluates (oracle : M → ℝ) (bits : Q → Bool) (l acc : List (Fin n)) :
    Code.Evaluates oracle bits (unique l acc) (uniqueRun l acc) := by
  induction l generalizing acc with
  | nil => exact Code.evaluates_pure _ _ _
  | cons x l ih =>
      exact Code.Evaluates.tick _ _ _ _
        (Code.Evaluates.bind _ _ _ _ _ _ (member_evaluates _ _ _ _)
          (Code.Evaluates.tick _ _ _ _ (ih _) 1)) 0

theorem augment_evaluates (oracle : M → ℝ) (bits : Q → Bool) (l : List (Fin n)) (v : Fin n) :
    Code.Evaluates oracle bits (augment l v) (augmentRun l v) :=
  Code.Evaluates.bind _ _ _ _ _ _ (member_evaluates _ _ _ _)
    (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 1)

theorem memberRun_true (x : Fin n) (l : List (Fin n)) : (memberRun x l).value = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memberRun]
  | cons y l ih =>
      by_cases h : x = y <;> simp [memberRun, h, ih, Outcome.add]

theorem uniqueRun_set (l acc : List (Fin n)) :
    (uniqueRun l acc).value.toFinset = acc.toFinset ∪ l.toFinset := by
  induction l generalizing acc with
  | nil => simp [uniqueRun, Outcome.pure]
  | cons x l ih =>
      by_cases hx : x ∈ acc
      · have hb := (memberRun_true x acc).mpr hx
        simp only [uniqueRun, Outcome.add, Outcome.combine, hb, ↓reduceIte, ih]
        ext y
        simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons]
        aesop
      · have hb : (memberRun x acc).value = false :=
          Bool.eq_false_iff.mpr (fun h => hx ((memberRun_true x acc).mp h))
        simp only [uniqueRun, Outcome.add, Outcome.combine, hb, Bool.false_eq_true, ↓reduceIte, ih]
        ext y
        simp

theorem uniqueRun_nodup (l acc : List (Fin n)) (hacc : acc.Nodup) : (uniqueRun l acc).value.Nodup := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons x l ih =>
      by_cases hx : x ∈ acc
      · have hb := (memberRun_true x acc).mpr hx
        simpa only [uniqueRun, Outcome.add, Outcome.combine, hb, ↓reduceIte] using ih acc hacc
      · have hb : (memberRun x acc).value = false :=
          Bool.eq_false_iff.mpr (fun h => hx ((memberRun_true x acc).mp h))
        simpa only [uniqueRun, Outcome.add, Outcome.combine, hb, Bool.false_eq_true, ↓reduceIte] using
          ih (x :: acc) (List.nodup_cons.mpr ⟨hx, hacc⟩)

theorem uniqueRun_length (l acc : List (Fin n)) :
    (uniqueRun l acc).value.length ≤ l.length + acc.length := by
  induction l generalizing acc with
  | nil => simp [uniqueRun, Outcome.pure]
  | cons x l ih =>
      have h₀ := ih acc
      have h₁ := ih (x :: acc)
      dsimp only [uniqueRun, Outcome.add, Outcome.combine]
      split_ifs <;> simp only [List.length_cons] at * <;> omega

theorem augmentRun_set (l : List (Fin n)) (v : Fin n) :
    (augmentRun l v).value.toFinset = insert v l.toFinset := by
  by_cases hv : v ∈ l
  · have hb := (memberRun_true v l).mpr hv
    simp [augmentRun, Outcome.combine, Outcome.add, Outcome.pure, hb, hv]
  · have hb : (memberRun v l).value = false :=
      Bool.eq_false_iff.mpr (fun h => hv ((memberRun_true v l).mp h))
    simp [augmentRun, Outcome.combine, Outcome.add, Outcome.pure, hb]

theorem augmentRun_nodup (l : List (Fin n)) (hl : l.Nodup) (v : Fin n) :
    (augmentRun l v).value.Nodup := by
  by_cases hv : v ∈ l
  · have hb := (memberRun_true v l).mpr hv
    simpa [augmentRun, Outcome.combine, Outcome.add, Outcome.pure, hb] using hl
  · have hb : (memberRun v l).value = false :=
      Bool.eq_false_iff.mpr (fun h => hv ((memberRun_true v l).mp h))
    simpa [augmentRun, Outcome.combine, Outcome.add, Outcome.pure, hb] using
      List.nodup_cons.mpr ⟨hv, hl⟩

theorem augmentRun_length (l : List (Fin n)) (v : Fin n) :
    (augmentRun l v).value.length ≤ l.length + 1 := by
  dsimp only [augmentRun, Outcome.combine, Outcome.add, Outcome.pure]
  split_ifs <;> simp

theorem memberRun_work (x : Fin n) (l : List (Fin n)) : (memberRun x l).work ≤ 3 * l.length + 1 := by
  induction l with
  | nil => simp [memberRun]
  | cons y l ih =>
      unfold memberRun
      split_ifs <;> simp only [Outcome.add, List.length_cons] <;> omega

theorem uniqueRun_work (l acc : List (Fin n)) :
    (uniqueRun l acc).work ≤ 8 * l.length * (l.length + acc.length + 1) := by
  induction l generalizing acc with
  | nil => simp [uniqueRun, Outcome.pure]
  | cons x l ih =>
      have hm := memberRun_work x acc
      have h₀ := ih acc
      have h₁ := ih (x :: acc)
      dsimp only [uniqueRun, Outcome.add, Outcome.combine]
      split_ifs <;> simp only [List.length_cons] at * <;> nlinarith

theorem augmentRun_work (l : List (Fin n)) (v : Fin n) :
    (augmentRun l v).work ≤ 3 * l.length + 3 := by
  have hh := memberRun_work v l
  dsimp only [augmentRun, Outcome.combine, Outcome.add, Outcome.pure]
  omega

theorem memberRun_resources (x : Fin n) (l : List (Fin n)) :
    (memberRun x l).metricQueries = 0 ∧ (memberRun x l).retentionQueries = 0 ∧
      (memberRun x l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons y l ih =>
      unfold memberRun
      split_ifs <;> simp only [Outcome.add, ih, Nat.zero_add, and_self]

theorem uniqueRun_resources (l acc : List (Fin n)) :
    (uniqueRun l acc).metricQueries = 0 ∧ (uniqueRun l acc).retentionQueries = 0 ∧
      (uniqueRun l acc).positiveReplies = 0 := by
  induction l generalizing acc with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
      have hm := memberRun_resources x acc
      have ht := ih (if (memberRun x acc).value then acc else x :: acc)
      simp only [uniqueRun, Outcome.add, Outcome.combine, hm, ht, Nat.zero_add, and_self]

theorem augmentRun_resources (l : List (Fin n)) (v : Fin n) :
    (augmentRun l v).metricQueries = 0 ∧ (augmentRun l v).retentionQueries = 0 ∧
      (augmentRun l v).positiveReplies = 0 := by
  have hh := memberRun_resources v l
  simpa only [augmentRun, Outcome.combine, Outcome.add, Outcome.pure, Nat.add_zero, Nat.zero_add] using hh

end SteinerUpperBound.BandEvaluation

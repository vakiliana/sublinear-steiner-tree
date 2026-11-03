module

public import SteinerUpperBound.FiniteMST.Basic

@[expose] public section

namespace SteinerUpperBound.FiniteMST

open QueryProgram
open scoped Classical

variable {M Q : Type*} {m : ℕ}

noncomputable def insert (d : Matrix m) (e : Edge m) : List (Edge m) → Code M Q (List (Edge m))
  | [] => .tick 0 (.pure [e])
  | f :: l => .tick 15 (if edgeWeight d e ≤ edgeWeight d f then .pure (e :: f :: l)
      else (insert d e l).map (List.cons f))

noncomputable def insertRun (d : Matrix m) (e : Edge m) : List (Edge m) → Outcome (List (Edge m))
  | [] => (Outcome.pure [e]).add 1 0 0 0
  | f :: l => if edgeWeight d e ≤ edgeWeight d f then
      (Outcome.pure (e :: f :: l)).add 16 0 0 0
    else ((insertRun d e l).map (List.cons f)).add 16 0 0 0

noncomputable def sort (d : Matrix m) : List (Edge m) → Code M Q (List (Edge m))
  | [] => .pure []
  | e :: l => .tick 0 ((sort d l).bind (insert d e))

noncomputable def sortRun (d : Matrix m) : List (Edge m) → Outcome (List (Edge m))
  | [] => .pure []
  | e :: l => ((sortRun d l).combine (insertRun d e (sortRun d l).value)).add 1 0 0 0

theorem insert_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (d : Matrix m) (e : Edge m) (l : List (Edge m)) :
    Code.Evaluates oracle bits (insert d e l) (insertRun d e l) := by
  induction l with
  | nil => exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 0
  | cons f l ih =>
      unfold insert insertRun
      split_ifs
      · exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 15
      · apply Code.Evaluates.tick
        intro F
        rw [Code.evaluate_map, ih]

theorem sort_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (d : Matrix m) (l : List (Edge m)) :
    Code.Evaluates oracle bits (sort d l) (sortRun d l) := by
  induction l with
  | nil => exact Code.evaluates_pure _ _ _
  | cons e l ih =>
      exact Code.Evaluates.tick _ _ _ _
        (Code.Evaluates.bind _ _ _ _ _ _ ih (insert_evaluates oracle bits d e _)) 0

theorem insertRun_value (d : Matrix m) (e : Edge m) (l : List (Edge m)) :
    (insertRun d e l).value = List.orderedInsert (fun e f => edgeWeight d e ≤ edgeWeight d f) e l := by
  induction l with
  | nil => simp [insertRun, Outcome.add, Outcome.pure]
  | cons f l ih =>
      by_cases h : edgeWeight d e ≤ edgeWeight d f <;>
        simp [insertRun, List.orderedInsert_cons, h, ih, Outcome.add, Outcome.map, Outcome.pure]

theorem sortRun_value (d : Matrix m) (l : List (Edge m)) :
    (sortRun d l).value = List.insertionSort (fun e f => edgeWeight d e ≤ edgeWeight d f) l := by
  induction l with
  | nil => simp [sortRun, Outcome.pure, List.insertionSort_nil]
  | cons e l ih =>
      simp only [sortRun, Outcome.add, Outcome.combine, insertRun_value, ih, List.insertionSort_cons]

theorem sortRun_perm (d : Matrix m) (l : List (Edge m)) : (sortRun d l).value.Perm l := by
  rw [sortRun_value]
  exact List.perm_insertionSort _ _

theorem sortRun_pairwise (d : Matrix m) (l : List (Edge m)) :
    (sortRun d l).value.Pairwise (fun e f => edgeWeight d e ≤ edgeWeight d f) := by
  let r := fun e f : Edge m => edgeWeight d e ≤ edgeWeight d f
  let : Std.Total r := ⟨fun e f => le_total _ _⟩
  let : IsTrans (Edge m) r := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  rw [sortRun_value]
  exact List.pairwise_insertionSort r l

theorem sortRun_sym_pairwise (d : Matrix m) (l : List (Edge m)) (hv : ∀ e ∈ l, valid e) :
    ((sortRun d l).value.map sym).Pairwise (fun e f => weight d e ≤ weight d f) := by
  apply List.pairwise_map.mpr
  apply List.Pairwise.imp_of_mem (p := sortRun_pairwise d l)
  intro e f he hf h
  rw [weight_sym_valid d e (hv e ((sortRun_perm d l).mem_iff.mp he)),
    weight_sym_valid d f (hv f ((sortRun_perm d l).mem_iff.mp hf))]
  exact h

theorem insertRun_work (d : Matrix m) (e : Edge m) (l : List (Edge m)) :
    (insertRun d e l).work ≤ 16 * l.length + 1 := by
  induction l with
  | nil => simp [insertRun, Outcome.add, Outcome.pure]
  | cons f l ih =>
      unfold insertRun
      split_ifs <;> dsimp only [Outcome.add, Outcome.map, Outcome.pure] <;> simp only [List.length_cons]
      · omega
      · omega

theorem sortRun_work (d : Matrix m) (l : List (Edge m)) :
    (sortRun d l).work ≤ 20 * (l.length + 1) ^ 2 := by
  induction l with
  | nil => simp [sortRun, Outcome.pure]
  | cons e l ih =>
      have hi := insertRun_work d e (sortRun d l).value
      have hn := (sortRun_perm d l).length_eq
      rw [hn] at hi
      dsimp only [sortRun, Outcome.add, Outcome.combine]
      simp only [List.length_cons]
      nlinarith

theorem insertRun_resources (d : Matrix m) (e : Edge m) (l : List (Edge m)) :
    (insertRun d e l).metricQueries = 0 ∧ (insertRun d e l).retentionQueries = 0 ∧
      (insertRun d e l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons f l ih =>
      unfold insertRun
      split_ifs <;> simp only [Outcome.add, Outcome.map, Outcome.pure, ih, Nat.zero_add, and_self]

theorem sortRun_resources (d : Matrix m) (l : List (Edge m)) :
    (sortRun d l).metricQueries = 0 ∧ (sortRun d l).retentionQueries = 0 ∧
      (sortRun d l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e l ih =>
      have hi := insertRun_resources d e (sortRun d l).value
      simp only [sortRun, Outcome.add, Outcome.combine, ih, hi, Nat.zero_add, and_self]

end SteinerUpperBound.FiniteMST

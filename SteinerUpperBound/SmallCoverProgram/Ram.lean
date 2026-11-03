module

public import SteinerUpperBound.QueryProgram.Loops

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram

open QueryProgram
open scoped Classical

variable {M Q α S A : Type*} {n : ℕ}

def put (v : Vector α n) (i : Fin n) (a : α) : Vector α n := v.set i.val a i.isLt

theorem get_put (v : Vector α n) (i j : Fin n) (a : α) :
    (put v i a).get j = if i = j then a else v.get j := by
  simp only [put, Vector.get_eq_getElem, Vector.getElem_set, Fin.ext_iff]

theorem folded_value (body : S → A → Outcome S) (l : List A) (s : S) :
    (Code.folded body l s).value = l.foldl (fun t a => (body t a).value) s := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simpa only [Code.folded, Outcome.add, Outcome.combine, List.foldl_cons] using ih _

def allocate (n : ℕ) (a : α) : Code M Q (Vector α n) :=
  .tick n (.pure (Vector.replicate n a))

def allocated (n : ℕ) (a : α) : Outcome (Vector α n) :=
  ⟨Vector.replicate n a, n + 1, 0, 0, 0⟩

theorem allocate_evaluates (m : M → ℝ) (b : Q → Bool) (n : ℕ) (a : α) :
    Code.Evaluates m b (allocate n a) (allocated n a) := by
  exact Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) n

/-- Every body result is written to the actual vector, with a charged RAM write. -/
def tabulate (body : Fin n → Code M Q α) (init : Vector α n) : Code M Q (Vector α n) :=
  Code.foldList (fun v i => (body i).bind (fun a => .tick 0 (.pure (put v i a))))
    (List.finRange n) init

def tabStep (body : Fin n → Outcome α) (v : Vector α n) (i : Fin n) :
    Outcome (Vector α n) :=
  ⟨put v i (body i).value, (body i).work + 1, (body i).metricQueries,
    (body i).retentionQueries, (body i).positiveReplies⟩

def tabulated (body : Fin n → Outcome α) (init : Vector α n) : Outcome (Vector α n) :=
  Code.folded (tabStep body) (List.finRange n) init

theorem tabulate_evaluates (m : M → ℝ) (b : Q → Bool)
    (body : Fin n → Code M Q α) (run : Fin n → Outcome α)
    (hbody : ∀ i, Code.Evaluates m b (body i) (run i)) (init : Vector α n) :
    Code.Evaluates m b (tabulate body init) (tabulated run init) := by
  apply Code.foldList_evaluates
  intro v i
  have hh := Code.Evaluates.bind m b (body i)
    (fun a => Code.tick 0 (Code.pure (put v i a))) (run i)
    ((Outcome.pure (put v i (run i).value)).add 1 0 0 0) (hbody i)
    (Code.Evaluates.tick m b _ _ (Code.evaluates_pure m b _) 0)
  simpa only [Outcome.combine, Outcome.add, Outcome.pure, tabStep, Nat.add_zero, Nat.zero_add] using hh

theorem get_setFold (f : Fin n → α) (l : List (Fin n)) (v : Vector α n) (j : Fin n) :
    (l.foldl (fun a i => put a i (f i)) v).get j = if j ∈ l then f j else v.get j := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
      rw [List.foldl_cons, ih, get_put]
      by_cases hj : j ∈ l
      · simp [hj]
      · by_cases hij : i = j
        · subst j; simp [hj]
        · simp [hj, hij, Ne.symm hij]

theorem tabulated_get (body : Fin n → Outcome α) (init : Vector α n) (j : Fin n) :
    (tabulated body init).value.get j = (body j).value := by
  rw [tabulated, folded_value]
  change ((List.finRange n).foldl (fun v i => put v i (body i).value) init).get j = _
  rw [get_setFold]
  simp

theorem tabulated_work (body : Fin n → Outcome α) (init : Vector α n) (C : ℕ)
    (h : ∀ i, (body i).work ≤ C) :
    (tabulated body init).work ≤ (C + 2) * n := by
  have hh := Code.folded_work (tabStep body) (C + 1)
    (fun v i => by dsimp [tabStep]; have := h i; omega) (List.finRange n) init
  simpa [tabulated, List.length_finRange, Nat.add_assoc] using hh

theorem tabulated_metricQueries (body : Fin n → Outcome α) (init : Vector α n) (C : ℕ)
    (h : ∀ i, (body i).metricQueries ≤ C) :
    (tabulated body init).metricQueries ≤ C * n := by
  have hh := Code.folded_metric_queries (tabStep body) C (fun _ i => h i) (List.finRange n) init
  simpa only [tabulated, List.length_finRange] using hh

theorem folded_retention_zero (body : S → A → Outcome S)
    (h : ∀ s a, (body s a).retentionQueries = 0) (l : List A) (s : S) :
    (Code.folded body l s).retentionQueries = 0 := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp only [Code.folded, Outcome.add, Outcome.combine, h, ih, Nat.zero_add]

theorem folded_positive_zero (body : S → A → Outcome S)
    (h : ∀ s a, (body s a).positiveReplies = 0) (l : List A) (s : S) :
    (Code.folded body l s).positiveReplies = 0 := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih => simp only [Code.folded, Outcome.add, Outcome.combine, h, ih, Nat.zero_add]

theorem tabulated_retention_zero (body : Fin n → Outcome α) (init : Vector α n)
    (h : ∀ i, (body i).retentionQueries = 0) :
    (tabulated body init).retentionQueries = 0 := by
  unfold tabulated
  exact folded_retention_zero (tabStep body) (fun _ i => h i) _ _

theorem tabulated_positive_zero (body : Fin n → Outcome α) (init : Vector α n)
    (h : ∀ i, (body i).positiveReplies = 0) :
    (tabulated body init).positiveReplies = 0 := by
  unfold tabulated
  exact folded_positive_zero (tabStep body) (fun _ i => h i) _ _

end SteinerUpperBound.SmallCoverProgram

module

public import SteinerUpperBound.Covers.Calibration

@[expose] public section

namespace SteinerUpperBound.Covers.RetentionTree

open SteinerLowerBound
open scoped Classical

variable {Q A B : Type*}

def bind : DecisionTree Q Bool A → (A → DecisionTree Q Bool B) → DecisionTree Q Bool B
  | .leaf a, k => k a
  | .query q next, k => .query q (fun b => bind (next b) k)

theorem output_bind (t : DecisionTree Q Bool A) (k : A → DecisionTree Q Bool B) (o : Q → Bool) :
    (bind t k).output o = (k (t.output o)).output o := by
  induction t with
  | leaf => rfl
  | query q next ih => exact ih (o q)

theorem transcript_bind (t : DecisionTree Q Bool A) (k : A → DecisionTree Q Bool B)
    (o : Q → Bool) :
    (bind t k).transcript o = t.transcript o ++ (k (t.output o)).transcript o := by
  induction t with
  | leaf => rfl
  | query q next ih => simp only [bind, DecisionTree.transcript, DecisionTree.output, ih, List.cons_append]

def positives (t : DecisionTree Q Bool A) (o : Q → Bool) : ℕ :=
  (t.transcript o).countP (fun qa => qa.2)

theorem positives_query (q : Q) (next : Bool → DecisionTree Q Bool A) (o : Q → Bool) :
    positives (.query q next) o = (if o q then 1 else 0) + positives (next (o q)) o := by
  simp [positives, DecisionTree.transcript, List.countP_cons, Nat.add_comm]

theorem queries_query (q : Q) (next : Bool → DecisionTree Q Bool A) (o : Q → Bool) :
    (DecisionTree.query q next).queries o = 1 + (next (o q)).queries o := by
  simp [DecisionTree.queries, DecisionTree.transcript, Nat.add_comm]

theorem positives_bind (t : DecisionTree Q Bool A) (k : A → DecisionTree Q Bool B)
    (o : Q → Bool) :
    positives (bind t k) o = positives t o + positives (k (t.output o)) o := by
  simp [positives, transcript_bind, List.countP_append]

theorem queries_bind (t : DecisionTree Q Bool A) (k : A → DecisionTree Q Bool B)
    (o : Q → Bool) :
    (bind t k).queries o = t.queries o + (k (t.output o)).queries o := by
  simp [DecisionTree.queries, transcript_bind]

theorem positives_map (t : DecisionTree Q Bool A) (f : A → B) (o : Q → Bool) :
    positives (t.map f) o = positives t o := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    simp only [DecisionTree.map, positives_query]
    rw [ih]

noncomputable def cached (t : DecisionTree Q Bool A) (cache : Q → Option Bool) :
    DecisionTree Q Bool A :=
  Caching.compile id (fun _ b => b) t cache

theorem cached_positives (t : DecisionTree Q Bool A) (cache : Q → Option Bool)
    (o : Q → Bool) (hc : Caching.Consistent cache o) :
    positives (cached t cache) o ≤ positives t o := by
  classical
  induction t generalizing cache with
  | leaf => simp [cached, Caching.compile, positives, DecisionTree.transcript]
  | query q next ih =>
    cases he : cache q with
    | some b =>
      have ho : o q = b := hc q b he
      have hi := ih b cache hc
      simp only [cached, Caching.compile, id_eq, he] at hi ⊢
      simp only [positives_query, ho]
      exact hi.trans (Nat.le_add_left _ _)
    | none =>
      have hc' : Caching.Consistent (Function.update cache q (some (o q))) o := by
        intro q' b hb
        by_cases hq : q' = q
        · subst q'
          simpa using hb
        · exact hc q' b (by simpa only [Function.update_of_ne hq] using hb)
      have hi := ih (o q) (Function.update cache q (some (o q))) hc'
      simp only [cached, Caching.compile, id_eq, he, positives, DecisionTree.transcript,
        List.countP_cons] at hi ⊢
      omega

end SteinerUpperBound.Covers.RetentionTree

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open scoped Classical BigOperators
open RetentionTree

variable {U : Type*} [Fintype U]

def rowTree : (C : ℕ) → (Fin C → U) → DecisionTree U Bool (Option U)
  | 0, _ => .leaf none
  | C + 1, w => .query (w 0) (fun b =>
      if b then .leaf (some (w 0)) else rowTree C (Fin.tail w))

theorem rowTree_output (b : U → Bool) (C : ℕ) (w : Fin C → U) :
    (rowTree C w).output b = first b C w := by
  induction C with
  | zero => rfl
  | succ C ih =>
    cases h : b (w 0) <;> simp [rowTree, first, DecisionTree.output, h, ih]

theorem rowTree_queries (b : U → Bool) (C : ℕ) (w : Fin C → U) :
    (rowTree C w).queries b = waiting b C w := by
  induction C with
  | zero => rfl
  | succ C ih =>
    cases h : b (w 0) <;>
      simp only [rowTree, queries_query, h, Bool.false_eq_true, ↓reduceIte,
        waiting, ih]
    · rfl

theorem rowTree_positives (b : U → Bool) (C : ℕ) (w : Fin C → U) :
    positives (rowTree C w) b ≤ 1 := by
  induction C with
  | zero => simp [rowTree, positives, DecisionTree.transcript]
  | succ C ih =>
    cases h : b (w 0) <;>
      simp only [rowTree, positives_query, h, Bool.false_eq_true, ↓reduceIte, zero_add]
    · exact ih _
    · simp [positives, DecisionTree.transcript]

def sampleTree (C : ℕ) : (s : ℕ) → (Fin s → Fin C → U) →
    DecisionTree U Bool (Fin s → Option U)
  | 0, _ => .leaf Fin.elim0
  | s + 1, rows => RetentionTree.bind (rowTree C (rows 0))
      (fun result => (sampleTree C s (Fin.tail rows)).map (fun out => Fin.cons result out))

theorem sampleTree_output (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) :
    (sampleTree C s rows).output b = fun j => first b C (rows j) := by
  induction s with
  | zero => exact Subsingleton.elim _ _
  | succ s ih =>
    rw [sampleTree, output_bind, DecisionTree.output_map, rowTree_output, ih]
    funext j
    refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem sampleTree_queries (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) :
    (sampleTree C s rows).queries b = proposals b C s rows := by
  induction s with
  | zero => simp [sampleTree, proposals, DecisionTree.queries, DecisionTree.transcript]
  | succ s ih =>
    rw [sampleTree, queries_bind, DecisionTree.queries_map, rowTree_queries, ih]
    exact (Fin.sum_univ_succ (fun j : Fin (s + 1) => waiting b C (rows j))).symm

theorem sampleTree_positives (b : U → Bool) (C s : ℕ) (rows : Fin s → Fin C → U) :
    positives (sampleTree C s rows) b ≤ s := by
  induction s with
  | zero => simp [sampleTree, positives, DecisionTree.transcript]
  | succ s ih =>
    rw [sampleTree, positives_bind, positives_map]
    have hrow := rowTree_positives b C (rows 0)
    have hrest := ih (Fin.tail rows)
    omega

def labelsTree (root : U) (C s : ℕ) (rows : Fin s → Fin C → U) :
    DecisionTree U Bool (Fin s → U) :=
  (sampleTree C s rows).map (fun out j => (out j).getD root)

noncomputable def cachedSampler (root : U) (C s : ℕ) (rows : Fin s → Fin C → U) :
    DecisionTree U Bool (Fin s → U) :=
  cached (labelsTree root C s rows) (Function.update (fun _ => none) root (some true))

theorem cachedSampler_resources (b : U → Bool) (root : U) (hroot : b root = true)
    (C s : ℕ) (rows : Fin s → Fin C → U) :
    (cachedSampler root C s rows).output b = labels b root C s rows ∧
      (cachedSampler root C s rows).queries b ≤ proposals b C s rows ∧
      proposals b C s rows ≤ s * C ∧
      positives (cachedSampler root C s rows) b ≤ s ∧
      (cachedSampler root C s rows).NoRepeats := by
  classical
  letI : Nonempty U := ⟨root⟩
  let cache : U → Option Bool := Function.update (fun _ => none) root (some true)
  have hc : Caching.Consistent cache b := by
    intro x bit hx
    by_cases h : x = root
    · subst x
      simpa [cache, hroot] using hx.symm
    · simp [cache, h] at hx
  refine ⟨?_, ?_, proposals_le b C s rows, ?_, ?_⟩
  · rw [cachedSampler, cached, Caching.output_compile _ _ _ _ _ hc,
      labelsTree, DecisionTree.output_map, sampleTree_output]
    rfl
  · exact (Caching.queries_compile id (fun _ bit => bit)
      (labelsTree root C s rows) cache b hc).trans_eq (by
        rw [labelsTree, DecisionTree.queries_map, sampleTree_queries]
        rfl)
  · exact (cached_positives (labelsTree root C s rows) cache b hc).trans (by
      rw [labelsTree, positives_map]
      exact sampleTree_positives b C s rows)
  · exact Caching.compile_no_repeats _ _ _ _

end SteinerUpperBound.Covers.Rejection

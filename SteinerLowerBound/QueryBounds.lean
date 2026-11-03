module

public import SteinerLowerBound.Caching
public import SteinerLowerBound.Screening.Adaptive

@[expose] public section

namespace SteinerLowerBound.DecisionTree

open scoped Classical

variable {Q A Z : Type*} [Fintype A]

theorem transcript_agree_used (t : DecisionTree Q A Z) (o o' : Q → A)
    (h : ∀ q ∈ t.used, o q = o' q) : t.transcript o = t.transcript o' := by
  classical
  induction t with
  | leaf => rfl
  | query q next ih =>
      have hq := h q (Finset.mem_insert_self _ _)
      simp only [transcript, hq]
      congr 1
      apply ih
      intro x hx
      exact h x (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
        ⟨o' q, Finset.mem_univ _, hx⟩))

theorem queries_update_of_not_used (t : DecisionTree Q A Z) (o : Q → A)
    (q : Q) (a : A) (hq : q ∉ t.used) :
    t.queries (Function.update o q a) = t.queries o := by
  classical
  unfold queries
  congr 1
  apply transcript_agree_used
  intro x hx
  have hne : x ≠ q := by intro h; subst x; exact hq hx
  simp [Function.update_of_ne hne]

theorem bounded_of_queries [Nonempty A] (t : DecisionTree Q A Z) (n : ℕ)
    (hnr : t.NoRepeats) (hqueries : ∀ o, t.queries o ≤ n) :
    Screening.DecisionTree.Bounded t n := by
  classical
  induction t generalizing n with
  | leaf => trivial
  | query q next ih =>
      cases n with
      | zero =>
          obtain ⟨a⟩ := ‹Nonempty A›
          have h := hqueries (fun _ => a)
          simp [queries, transcript] at h
      | succ n =>
          intro a
          apply ih a n (hnr.1 a)
          intro o
          have h := hqueries (Function.update o q a)
          have h' : (next a).queries (Function.update o q a) ≤ n := by
            simpa [queries, transcript] using h
          rwa [queries_update_of_not_used (next a) o q a (hnr.2 a)] at h'

noncomputable def memoize (t : DecisionTree Q A Z) : DecisionTree Q A Z :=
  Caching.compile id (fun _ a => a) t (fun _ => none)

omit [Fintype A] in
theorem memoize_output (t : DecisionTree Q A Z) (o : Q → A) :
    t.memoize.output o = t.output o :=
  Caching.output_compile id (fun _ a => a) t (fun _ => none) o
    (by intro q a h; simp at h)

omit [Fintype A] in
theorem memoize_queries (t : DecisionTree Q A Z) (o : Q → A) :
    t.memoize.queries o ≤ t.queries o :=
  Caching.queries_compile id (fun _ a => a) t (fun _ => none) o
    (by intro q a h; simp at h)

theorem memoize_noRepeats (t : DecisionTree Q A Z) : t.memoize.NoRepeats :=
  Caching.compile_no_repeats id (fun _ a => a) t (fun _ => none)

theorem memoize_bounded [Nonempty A] (t : DecisionTree Q A Z) (n : ℕ)
    (ht : ∀ o, t.queries o ≤ n) : Screening.DecisionTree.Bounded t.memoize n :=
  bounded_of_queries t.memoize n t.memoize_noRepeats
    (fun o => (t.memoize_queries o).trans (ht o))

end SteinerLowerBound.DecisionTree

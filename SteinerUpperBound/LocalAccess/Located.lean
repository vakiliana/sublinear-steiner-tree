module

public import SteinerUpperBound.LocalAccess.Frame

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V Q : Type*} [Fintype V]

theorem explored_subset (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c)
    (hroot : root ∈ ComponentExplore.retained bits key terminals.toFinset) :
    (ComponentExplore.result w bits key a B terminals root c).value.memory.points.toFinset ⊆
      terminals.toFinset := by
  have hs := (ComponentExplore.result_correct w bits key a B terminals root c hc hroot).1
  intro y hy
  have hr := ComponentExplore.reachable_retained w bits key terminals.toFinset a hroot (hs y hy)
  exact (Finset.mem_filter.mp hr).1

theorem explored_complete (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c)
    (hroot : root ∈ ComponentExplore.retained bits key terminals.toFinset)
    (he : (ComponentExplore.result w bits key a B terminals root c).value.complete = true) :
    (ComponentExplore.result w bits key a B terminals root c).value.memory.points.toFinset =
        ComponentExplore.component
          (ComponentExplore.retainedGraph w bits key terminals.toFinset a) root ∧
      (ComponentExplore.result w bits key a B terminals root c).value.memory.points.length ≤ B := by
  have h := (ComponentExplore.result_correct w bits key a B terminals root c hc hroot).2
  have hv := ComponentExplore.result_valid w bits key a B terminals root c hc
  simpa only [ComponentExplore.Answer.project, ComponentExplore.Memory.graphState,
    he, ite_true, List.toFinset_card_of_nodup hv.points_nodup] using h

theorem locate_cache (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q) :
    (locateResult w bits key a b B vertices terminals root c).value.cache =
      (ComponentExplore.result w bits key a B terminals root c).value.memory.cache := by
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete <;>
    simp only [locateResult, he, Bool.false_eq_true, ite_false, ite_true,
      Outcome.add, Outcome.combine, Outcome.pure]

theorem locate_cache_correct (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c) :
    Cache.Correct bits (locateResult w bits key a b B vertices terminals root c).value.cache := by
  rw [locate_cache]
  exact (ComponentExplore.result_valid w bits key a B terminals root c hc).cache_correct

def locateBudget (n k b B : ℕ) : ℕ :=
  64 * (k + 1) * (B + 2) ^ 2 + frameBudget n k b B + 2

theorem locate_work (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c) (hn : terminals.Nodup)
    (hroot : root ∈ ComponentExplore.retained bits key terminals.toFinset) :
    (locateResult w bits key a b B vertices terminals root c).work ≤
      locateBudget vertices.length terminals.length b B := by
  have hew := ComponentExplore.result_work w bits key a B terminals root c hc
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete with
  | false =>
      simp only [locateResult, he, Bool.false_eq_true, ite_false, Outcome.combine, Outcome.add,
        Outcome.pure, locateBudget]
      omega
  | true =>
      have hlen := (explored_complete w bits key a B terminals root c hc hroot he).2
      have hs := explored_subset w bits key a B terminals root c hc hroot
      have hf := frame_work w (5 * a / 8) b B vertices terminals
        (ComponentExplore.result w bits key a B terminals root c).value.memory.points hn hs hlen
      simp only [locateResult, he, ite_true, Outcome.combine, Outcome.add, Outcome.pure,
        locateBudget]
      omega

theorem locate_metric_queries (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c) (hn : terminals.Nodup)
    (hroot : root ∈ ComponentExplore.retained bits key terminals.toFinset) :
    (locateResult w bits key a b B vertices terminals root c).metricQueries ≤
      (B + 1) * terminals.length + vertices.length * B := by
  have heq := ComponentExplore.result_metric_queries w bits key a B terminals root c
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete with
  | false =>
      simp only [locateResult, he, Bool.false_eq_true, ite_false, Outcome.combine, Outcome.add,
        Outcome.pure]
      omega
  | true =>
      have hlen := (explored_complete w bits key a B terminals root c hc hroot he).2
      have hs := explored_subset w bits key a B terminals root c hc hroot
      have hf := frame_metric_queries w (5 * a / 8) b B vertices terminals
        (ComponentExplore.result w bits key a B terminals root c).value.memory.points hn hs hlen
      simp only [locateResult, he, ite_true, Outcome.combine, Outcome.add, Outcome.pure]
      omega

theorem locate_positive (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q) :
    (locateResult w bits key a b B vertices terminals root c).positiveReplies ≤ B := by
  have heq := ComponentExplore.result_positive w bits key a B terminals root c
  have hf := (frame_counters w (5 * a / 8) b B vertices terminals
    (ComponentExplore.result w bits key a B terminals root c).value.memory.points).2
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete <;>
    simp only [locateResult, he, Bool.false_eq_true, ite_false, ite_true, Outcome.combine,
      Outcome.add, Outcome.pure, hf] <;> omega

theorem locate_some (w : Sym2 V → ℝ) (bits : Q → Bool) (key : V → Q)
    (a : ℝ) (b B : ℕ) (vertices terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct bits c) (hn : terminals.Nodup)
    (hroot : root ∈ ComponentExplore.retained bits key terminals.toFinset)
    (f : Frame V b B) (hf : (locateResult w bits key a b B vertices terminals root c).value.frame =
      some f) :
    f.points.Nodup ∧ f.points.toFinset =
        ComponentExplore.component
          (ComponentExplore.retainedGraph w bits key terminals.toFinset a) root ∧
      f.points.length ≤ B := by
  cases he : (ComponentExplore.result w bits key a B terminals root c).value.complete with
  | false =>
      simp only [locateResult, he, Bool.false_eq_true, ite_false, Outcome.combine, Outcome.add,
        Outcome.pure, reduceCtorEq] at hf
  | true =>
      simp only [locateResult, he, ite_true, Outcome.combine, Outcome.add, Outcome.pure,
        Option.some.injEq] at hf
      subst f
      have hsmall := explored_complete w bits key a B terminals root c hc hroot he
      have hs := explored_subset w bits key a B terminals root c hc hroot
      change (canonicalResult _ _).value.Nodup ∧
        (canonicalResult _ _).value.toFinset = _ ∧ (canonicalResult _ _).value.length ≤ B
      exact ⟨canonical_nodup _ _ hn, (canonical_set _ _ hs).trans hsmall.1,
        (canonical_length _ _ hn hs).trans hsmall.2⟩

end SteinerUpperBound.LocalAccess

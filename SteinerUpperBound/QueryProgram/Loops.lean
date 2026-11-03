module

public import SteinerUpperBound.QueryProgram.Cache

@[expose] public section

namespace SteinerUpperBound.QueryProgram.Code

open SteinerLowerBound
open scoped Classical

variable {M Q A S : Type*}

def foldList (body : S → A → Code M Q S) : List A → S → Code M Q S
  | [], s => .pure s
  | a :: l, s => .tick 0 ((body s a).bind (fun t => foldList body l t))

def folded (body : S → A → Outcome S) : List A → S → Outcome S
  | [], s => .pure s
  | a :: l, s =>
      ((body s a).combine (folded body l (body s a).value)).add 1 0 0 0

theorem foldList_evaluates (m : M → ℝ) (b : Q → Bool)
    (body : S → A → Code M Q S) (step : S → A → Outcome S)
    (hstep : ∀ s a, Evaluates m b (body s a) (step s a)) (l : List A) (s : S) :
    Evaluates m b (foldList body l s) (folded step l s) := by
  induction l generalizing s with
  | nil => exact evaluates_pure _ _ _
  | cons a l ih =>
      exact Evaluates.tick _ _ _ _
        (Evaluates.bind _ _ _ _ _ _ (hstep s a) (ih _)) 0

theorem folded_work (body : S → A → Outcome S) (C : ℕ)
    (h : ∀ s a, (body s a).work ≤ C) (l : List A) (s : S) :
    (folded body l s).work ≤ (C + 1) * l.length := by
  induction l generalizing s with
  | nil => simp only [folded, Outcome.pure, List.length_nil, Nat.mul_zero, le_refl]
  | cons a l ih =>
      have h' := ih (body s a).value
      have h'' := h s a
      simp only [folded, Outcome.add, Outcome.combine, List.length_cons]
      nlinarith

theorem folded_metric_queries (body : S → A → Outcome S) (C : ℕ)
    (h : ∀ s a, (body s a).metricQueries ≤ C) (l : List A) (s : S) :
    (folded body l s).metricQueries ≤ C * l.length := by
  induction l generalizing s with
  | nil => simp only [folded, Outcome.pure, List.length_nil, Nat.mul_zero, le_refl]
  | cons a l ih =>
      have h' := ih (body s a).value
      have h'' := h s a
      simp only [folded, Outcome.add, Outcome.combine, List.length_cons]
      nlinarith

theorem folded_positive_potential (body : S → A → Outcome S) (P : S → ℕ)
    (h : ∀ s a, (body s a).positiveReplies + P s ≤ P (body s a).value)
    (l : List A) (s : S) :
    (folded body l s).positiveReplies + P s ≤ P (folded body l s).value := by
  induction l generalizing s with
  | nil => simp only [folded, Outcome.pure, Nat.zero_add, le_refl]
  | cons a l ih =>
      have h' := ih (body s a).value
      have h'' := h s a
      simp only [folded, Outcome.add, Outcome.combine]
      omega

end SteinerUpperBound.QueryProgram.Code

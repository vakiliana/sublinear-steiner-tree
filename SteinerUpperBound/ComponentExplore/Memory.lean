module

public import SteinerUpperBound.ComponentExplore.Graph

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open QueryProgram
open scoped Classical

variable {V M Q : Type*}

noncomputable def member (x : V) : List V → Code M Q Bool
  | [] => .tick 0 (.pure false)
  | y :: l => .tick 1 (if x = y then .pure true else member x l)

noncomputable def memberResult (x : V) : List V → Outcome Bool
  | [] => ⟨false, 1, 0, 0, 0⟩
  | y :: l =>
      if x = y then ⟨true, 2, 0, 0, 0⟩ else (memberResult x l).add 2 0 0 0

theorem member_evaluates (m : M → ℝ) (b : Q → Bool) (x : V) (l : List V) :
    Code.Evaluates m b (member x l) (memberResult x l) := by
  induction l with
  | nil => intro F; rfl
  | cons y l ih =>
      by_cases h : x = y
      · intro F
        simp only [member, memberResult, h, ite_true, Code.evaluate, Outcome.pure, Outcome.add,
          Nat.add_zero, Nat.zero_add]
      · intro F
        simpa only [member, memberResult, h, ite_false, Code.evaluate] using
          ih (fun o => F (o.add 2 0 0 0))

theorem member_value (x : V) (l : List V) :
    (memberResult x l).value = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memberResult]
  | cons y l ih =>
      by_cases h : x = y
      · simp [memberResult, h]
      · simpa only [memberResult, h, ite_false, Outcome.add, List.mem_cons,
          false_or] using ih

theorem member_value_eq (x : V) (l : List V) :
    (memberResult x l).value = decide (x ∈ l) := by
  cases h : (memberResult x l).value with
  | false =>
      have hn : x ∉ l := by
        intro hx
        have hh := (member_value x l).mpr hx
        simp only [h, Bool.false_eq_true] at hh
      simp [hn]
  | true =>
      have hx := (member_value x l).mp h
      simp [hx]

theorem member_work (x : V) (l : List V) :
    (memberResult x l).work ≤ 2 * l.length + 1 := by
  induction l with
  | nil => simp [memberResult]
  | cons y l ih =>
      by_cases h : x = y <;>
        simp only [memberResult, h, ite_true, ite_false, Outcome.add, List.length_cons] <;> omega

theorem member_counters (x : V) (l : List V) :
    (memberResult x l).metricQueries = 0 ∧
      (memberResult x l).retentionQueries = 0 ∧ (memberResult x l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons y l ih =>
      by_cases h : x = y
      · simp [memberResult, h]
      · simpa only [memberResult, h, ite_false, Outcome.add, Nat.zero_add] using ih

noncomputable def pendingProgram (found done : List V) : List V → Code M Q (Option V)
  | [] => .tick 0 (.pure none)
  | x :: l =>
      (member x found).bind (fun hf =>
        .tick 0 (if hf then
          (member x done).bind (fun hd =>
            .tick 0 (if hd then pendingProgram found done l else .pure (some x)))
        else pendingProgram found done l))

noncomputable def pendingResult (found done : List V) : List V → Outcome (Option V)
  | [] => ⟨none, 1, 0, 0, 0⟩
  | x :: l =>
      let hf := memberResult x found
      if hf.value then
        let hd := memberResult x done
        hf.combine ((hd.combine ((if hd.value then pendingResult found done l
          else Outcome.pure (some x)).add 1 0 0 0)).add 1 0 0 0)
      else hf.combine ((pendingResult found done l).add 1 0 0 0)

theorem pending_evaluates (m : M → ℝ) (b : Q → Bool)
    (found done l : List V) :
    Code.Evaluates m b (pendingProgram found done l) (pendingResult found done l) := by
  induction l with
  | nil => intro F; rfl
  | cons x l ih =>
      intro F
      simp only [pendingProgram, Code.evaluate_bind]
      rw [member_evaluates m b x found]
      simp only [Code.evaluate]
      cases hf : (memberResult x found).value <;>
        simp only [hf, Bool.false_eq_true, ite_false, ite_true]
      · rw [ih]
        simp only [pendingResult, hf, Bool.false_eq_true, ite_false, Outcome.combine,
          Outcome.add, Nat.add_assoc, Nat.zero_add, Nat.add_zero]
      · rw [Code.evaluate_bind, member_evaluates m b x done]
        cases hd : (memberResult x done).value <;>
          simp only [Code.evaluate, hd, Bool.false_eq_true, ite_false, ite_true]
        · simp only [pendingResult, hf, hd, ite_true, Bool.false_eq_true, ite_false,
            Outcome.pure, Outcome.combine, Outcome.add, Nat.add_assoc, Nat.add_zero,
            Nat.zero_add]
        · rw [ih]
          simp only [pendingResult, hf, hd, ite_true, Outcome.combine, Outcome.add,
            Nat.add_assoc, Nat.zero_add, Nat.add_zero]

theorem pending_value (found done l : List V) :
    (pendingResult found done l).value = pending l found.toFinset done.toFinset := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      by_cases hf : x ∈ found <;> by_cases hd : x ∈ done <;>
        simp [pendingResult, pending, member_value_eq, Outcome.combine, Outcome.add,
          Outcome.pure, hf, hd, ih]

theorem pending_work (found done l : List V) :
    (pendingResult found done l).work ≤
      (2 * (found.length + done.length) + 4) * l.length + 1 := by
  induction l with
  | nil => simp only [pendingResult, List.length_nil, Nat.mul_zero, Nat.zero_add, le_refl]
  | cons x l ih =>
      have hf := member_work x found
      have hd := member_work x done
      cases hv : (memberResult x found).value <;>
        cases hw : (memberResult x done).value <;>
        simp only [pendingResult, hv, hw, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure, List.length_cons] <;> nlinarith

theorem pending_counters (found done l : List V) :
    (pendingResult found done l).metricQueries = 0 ∧
      (pendingResult found done l).retentionQueries = 0 ∧
      (pendingResult found done l).positiveReplies = 0 := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
      have hf := member_counters x found
      have hd := member_counters x done
      cases hv : (memberResult x found).value <;>
        cases hw : (memberResult x done).value <;>
        simp only [pendingResult, hv, hw, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.pure, hf.1, hf.2.1, hf.2.2,
          hd.1, hd.2.1, hd.2.2, ih.1, ih.2.1, ih.2.2, Nat.add_zero, Nat.zero_add,
          true_and]

structure Memory (V Q : Type*) where
  points : List V
  processed : List V
  count : ℕ
  cache : Cache Q

namespace Memory

noncomputable def graphState (s : Memory V Q) : State V :=
  ⟨s.points.toFinset, s.processed.toFinset⟩

structure Valid (b : Q → Bool) (s : Memory V Q) : Prop where
  points_nodup : s.points.Nodup
  processed_nodup : s.processed.Nodup
  count_eq : s.count = s.points.length
  cache_correct : Cache.Correct b s.cache

theorem card_eq (b : Q → Bool) (s : Memory V Q) (h : Valid b s) :
    s.graphState.found.card = s.count := by
  simpa only [graphState, List.toFinset_card_of_nodup h.points_nodup] using h.count_eq.symm

end Memory

end SteinerUpperBound.ComponentExplore

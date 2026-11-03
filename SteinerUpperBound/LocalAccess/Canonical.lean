module

public import SteinerUpperBound.LocalAccess.Pack

@[expose] public section

namespace SteinerUpperBound.LocalAccess

open QueryProgram
open scoped Classical

variable {V M Q : Type*}

noncomputable def canonicalProgram (wanted : List V) : List V → Code M Q (List V)
  | [] => .tick 0 (.pure [])
  | x :: l =>
      .tick 0 ((ComponentExplore.member x wanted).bind (fun h =>
        .tick 0 (if h then
          (canonicalProgram wanted l).bind (fun rest => .tick 0 (.pure (x :: rest)))
        else canonicalProgram wanted l)))

noncomputable def canonicalResult (wanted : List V) : List V → Outcome (List V)
  | [] => (Outcome.pure []).add 1 0 0 0
  | x :: l =>
      let p := ComponentExplore.memberResult x wanted
      let rest := if p.value then ((canonicalResult wanted l).map (List.cons x)).add 1 0 0 0
        else canonicalResult wanted l
      (p.combine (rest.add 1 0 0 0)).add 1 0 0 0

theorem canonical_evaluates (m : M → ℝ) (b : Q → Bool) (wanted order : List V) :
    Code.Evaluates m b (canonicalProgram wanted order) (canonicalResult wanted order) := by
  induction order with
  | nil => intro F; rfl
  | cons x l ih =>
      intro F
      simp only [canonicalProgram, canonicalResult, Code.evaluate, Code.evaluate_bind]
      rw [ComponentExplore.member_evaluates m b x wanted]
      cases hp : (ComponentExplore.memberResult x wanted).value <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Code.evaluate]
      · rw [ih]
      · rw [Code.evaluate_bind, ih]
        simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, Outcome.map,
          Nat.zero_add, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem canonical_value (wanted order : List V) :
    (canonicalResult wanted order).value = order.filter (fun x => decide (x ∈ wanted)) := by
  induction order with
  | nil => rfl
  | cons x l ih =>
      by_cases h : x ∈ wanted <;>
        simp [canonicalResult, ComponentExplore.member_value_eq, h, ih, Outcome.add,
          Outcome.combine, Outcome.pure, Outcome.map]

theorem canonical_nodup (wanted order : List V) (hp : order.Nodup) :
    (canonicalResult wanted order).value.Nodup := by
  rw [canonical_value]
  exact hp.filter _

theorem canonical_set (wanted order : List V) (h : wanted.toFinset ⊆ order.toFinset) :
    (canonicalResult wanted order).value.toFinset = wanted.toFinset := by
  rw [canonical_value]
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun hx => ⟨List.mem_toFinset.mp (h (List.mem_toFinset.mpr hx)), hx⟩⟩

theorem canonical_equal (a b order : List V) (h : a.toFinset = b.toFinset) :
    (canonicalResult a order).value = (canonicalResult b order).value := by
  rw [canonical_value, canonical_value]
  congr 1
  funext x
  simp only [← List.mem_toFinset, h]

theorem canonical_work (wanted order : List V) :
    (canonicalResult wanted order).work ≤ (2 * wanted.length + 5) * (order.length + 1) := by
  induction order with
  | nil => simp [canonicalResult, Outcome.add, Outcome.pure]
  | cons x l ih =>
      have hm := ComponentExplore.member_work x wanted
      cases hp : (ComponentExplore.memberResult x wanted).value <;>
        simp only [canonicalResult, hp, Bool.false_eq_true, ite_false, ite_true,
          Outcome.add, Outcome.combine, Outcome.map, List.length_cons] <;> nlinarith

theorem canonical_counters (wanted order : List V) :
    (canonicalResult wanted order).metricQueries = 0 ∧
      (canonicalResult wanted order).retentionQueries = 0 ∧
      (canonicalResult wanted order).positiveReplies = 0 := by
  induction order with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons x l ih =>
      have hm := ComponentExplore.member_counters x wanted
      cases hp : (ComponentExplore.memberResult x wanted).value <;>
        simp [canonicalResult, hp, Outcome.add, Outcome.combine, Outcome.map,
          hm.1, hm.2.1, hm.2.2, ih.1, ih.2.1, ih.2.2]

end SteinerUpperBound.LocalAccess

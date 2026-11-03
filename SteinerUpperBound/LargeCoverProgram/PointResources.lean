module

public import SteinerUpperBound.LargeCoverProgram.PointKernel

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q : Type*} {n d B : ℕ}

noncomputable def frameInitiation (D : Vector Bool n) (f : LocalAccess.Frame (Fin n) d B) : ℝ :=
  if (LocalAccess.hitsResult D f.points).value then 0 else (inverseRate f.points.length : ℝ)

theorem frameInitiation_bounds (D : Vector Bool n) (f : LocalAccess.Frame (Fin n) d B) :
    0 ≤ frameInitiation D f ∧ frameInitiation D f ≤ 1 := by
  dsimp [frameInitiation]
  split_ifs
  · norm_num
  · exact (inverseRate f.points.length).property

theorem afterPointFrame_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => (o.work : ℝ)) =
      (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 8 +
        if (LocalAccess.hitsResult D f.points).value then 0 else
          6 + (inverseRate f.points.length : ℝ) *
            ((vo f c).evaluate w bits (fun o => (o.work : ℝ)) + 4) := by
  rw [afterPointFrame, Code.evaluate_work_bind, LocalAccess.hits_evaluates w bits]
  rw [Code.evaluate_work_bind, length_evaluates w bits]
  rw [(length_result f.points).1]
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false, Code.evaluate, Outcome.add, Outcome.pure,
      Nat.cast_add, Nat.cast_zero, add_zero]
    rw [SavingScores.bernoulli_expect]
    simp only [ite_true, Bool.false_eq_true, ite_false, Code.evaluate_work_bind,
      Code.evaluate, Outcome.add, Outcome.pure, Nat.cast_add, Nat.cast_zero, add_zero]
    simp only [Code.evaluate_add, Code.evaluate_const]
    rw [Mean.work_bind_tick w bits (vo f c)
      (fun reply => ((if reply.1 then (1 / 2 : ℝ) else 0), reply.2)) 3]
    norm_num
    ring
  · simp only [hh, ite_true, Code.evaluate, Outcome.add, Outcome.pure, Nat.cast_add,
      Nat.cast_zero, add_zero]
    norm_num
    ring

theorem afterPointFrame_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) =
      frameInitiation D f * (vo f c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) := by
  rw [afterPointFrame, Code.evaluate_positive_bind, LocalAccess.hits_evaluates w bits]
  rw [Code.evaluate_positive_bind, length_evaluates w bits]
  rw [(length_result f.points).1]
  have hh := LocalAccess.hits_counters D f.points
  have hl := length_result f.points
  simp only [hh.2.2, hl.2.2.2.2, Nat.cast_zero, zero_add]
  cases hb : (LocalAccess.hitsResult D f.points).value
  · simp only [hb, Bool.false_eq_true, ite_false, Code.evaluate, Outcome.add, Outcome.pure,
      Nat.zero_add, frameInitiation]
    rw [SavingScores.bernoulli_expect]
    simp only [ite_true, Bool.false_eq_true, ite_false, Code.evaluate_positive_bind,
      Code.evaluate, Outcome.add, Outcome.pure, Nat.zero_add, Nat.cast_zero, Code.evaluate_const,
      mul_zero, add_zero]
  · simp [hb, Code.evaluate, Outcome.add, Outcome.pure, frameInitiation]

theorem afterPointFrame_expected (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B) (c : Cache Q)
    (hlen : f.points.length ≤ B) (W P : ℝ)
    (hw : (vo f c).evaluate w bits (fun o => (o.work : ℝ)) ≤ W)
    (hp : (vo f c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) ≤ P) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => (o.work : ℝ)) ≤
        4 * B + 24 + frameInitiation D f * W ∧
      (afterPointFrame D vo f c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) ≤
        frameInitiation D f * P := by
  have hi := frameInitiation_bounds D f
  have hh := LocalAccess.hits_work D f.points
  have hl := (length_result f.points).2.1
  have hlen' : (f.points.length : ℝ) ≤ B := by exact_mod_cast hlen
  have hh' : ((LocalAccess.hitsResult D f.points).work : ℝ) ≤ 2 * f.points.length + 1 := by
    exact_mod_cast hh
  constructor
  · rw [afterPointFrame_work, hl]
    push_cast
    cases hb : (LocalAccess.hitsResult D f.points).value
    · have hrate := (inverseRate f.points.length).property
      have hm := mul_le_mul_of_nonneg_left hw hrate.1
      simp only [hb, Bool.false_eq_true, ite_false, frameInitiation]
      nlinarith [hrate.2]
    · simp only [hb, ite_true, frameInitiation, zero_mul, add_zero]
      linarith
  · rw [afterPointFrame_positive]
    exact mul_le_mul_of_nonneg_left hp hi.1

def pointBudget (n k d B : ℕ) : ℕ :=
  LocalAccess.locateBudget n k d B + 4 * B + 40

theorem point_work (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => (o.work : ℝ)) =
      let r := Cache.resolved bits (key root) c
      let l := LocalAccess.locateResult w bits key a d B vertices terminals root r.value.2
      (r.work : ℝ) + 4 + if r.value.1 then
        (l.work : ℝ) + 4 + l.value.frame.elim 0
          (fun f => (afterPointFrame D vo f l.value.cache).evaluate w bits (fun o => (o.work : ℝ)))
      else 0 := by
  rw [point, Code.evaluate_work_bind, Cache.resolve_evaluates w bits, Mean.work_tick]
  dsimp only
  cases hr : (Cache.resolved bits (key root) c).value.1
  · simp [hr, Code.evaluate, Outcome.pure]
  · simp only [hr, ite_true]
    rw [Code.evaluate_work_bind, LocalAccess.locate_evaluates w bits]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame <;>
      simp only [afterPointLocate, hf, Code.evaluate, Outcome.add, Outcome.pure, Nat.cast_add,
        Nat.cast_zero, add_zero, Option.elim_none, Option.elim_some]
    all_goals try simp only [Code.evaluate_add, Code.evaluate_const]
    all_goals norm_num; ring

theorem point_positive (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) =
      let r := Cache.resolved bits (key root) c
      let l := LocalAccess.locateResult w bits key a d B vertices terminals root r.value.2
      (r.positiveReplies : ℝ) + if r.value.1 then
        (l.positiveReplies : ℝ) + l.value.frame.elim 0 (fun f =>
          frameInitiation D f * (vo f l.value.cache).evaluate w bits (fun o => (o.positiveReplies : ℝ)))
      else 0 := by
  rw [point, Code.evaluate_positive_bind, Cache.resolve_evaluates w bits, Mean.positive_tick]
  dsimp only
  cases hr : (Cache.resolved bits (key root) c).value.1
  · simp [hr, Code.evaluate, Outcome.pure]
  · simp only [hr, ite_true]
    rw [Code.evaluate_positive_bind, LocalAccess.locate_evaluates w bits]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame <;>
      simp only [afterPointLocate, hf, Code.evaluate, Outcome.add, Outcome.pure, Nat.zero_add,
        Nat.cast_zero, add_zero, Option.elim_none, Option.elim_some, afterPointFrame_positive]

/-- Actual initiation-weighted VO resource account. Preparation and component
exploration are charged in the base term; only matching calls are weighted.
This theorem has NO assumed point-callback resource bound. -/
theorem point_expected (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (hnd : terminals.Nodup) (hroot : root ∈ terminals) :
    let r := Cache.resolved bits (key root) c
    let l := LocalAccess.locateResult w bits key a d B vertices terminals root r.value.2
    let W := if bits (key root) then l.value.frame.elim 0 (fun f =>
      frameInitiation D f * (vo f l.value.cache).evaluate w bits (fun o => (o.work : ℝ))) else 0
    let P := if bits (key root) then l.value.frame.elim 0 (fun f =>
      frameInitiation D f * (vo f l.value.cache).evaluate w bits (fun o => (o.positiveReplies : ℝ))) else 0
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => (o.work : ℝ)) ≤
        pointBudget vertices.length terminals.length d B + W ∧
      (point key a vertices terminals D vo root c).evaluate w bits (fun o => (o.positiveReplies : ℝ)) ≤
        B + 1 + P := by
  dsimp only
  rw [point_work, point_positive]
  dsimp only
  have hr := Cache.resolved_correct bits (key root) c hc
  have hw : ((Cache.resolved bits (key root) c).work : ℝ) ≤ 3 := by
    exact_mod_cast Cache.resolved_work_le bits (key root) c
  have hp : ((Cache.resolved bits (key root) c).positiveReplies : ℝ) ≤ 1 := by
    exact_mod_cast Cache.resolved_positive_le bits (key root) c
  rw [hr.1]
  cases hb : bits (key root)
  · simp only [hb, Bool.false_eq_true, ite_false, add_zero]
    dsimp [pointBudget]
    push_cast
    constructor <;> linarith [
      (show (0 : ℝ) ≤ LocalAccess.locateBudget vertices.length terminals.length d B by positivity),
      (show (0 : ℝ) ≤ B by positivity)]
  · have hx : root ∈ ComponentExplore.retained bits key
        (@List.toFinset (Fin n) (Classical.decEq _) terminals) := by
      simp [ComponentExplore.retained, hroot, hb]
    have hlocW := LocalAccess.locate_work w bits key a d B vertices terminals root _ hr.2 hnd hx
    have hlocP := LocalAccess.locate_positive w bits key a d B vertices terminals root
      (Cache.resolved bits (key root) c).value.2
    have hlocW' : ((LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).work : ℝ) ≤
          LocalAccess.locateBudget vertices.length terminals.length d B := by exact_mod_cast hlocW
    have hlocP' : ((LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).positiveReplies : ℝ) ≤ B := by exact_mod_cast hlocP
    simp only [hb, ite_true]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame with
    | none =>
        simp only [hf, Option.elim_none, add_zero]
        dsimp [pointBudget]
        push_cast
        constructor <;> linarith
    | some f =>
        have hlen := (LocalAccess.locate_some w bits key a d B vertices terminals root _ hr.2 hnd hx f hf).2.2
        have hh := afterPointFrame_expected w bits D vo f
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).value.cache
          hlen _ _ le_rfl le_rfl
        simp only [hf, Option.elim_some]
        dsimp [pointBudget]
        push_cast
        constructor <;> linarith [hh.1, hh.2]

end SteinerUpperBound.LargeCoverProgram

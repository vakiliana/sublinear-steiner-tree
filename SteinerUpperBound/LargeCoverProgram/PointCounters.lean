module

public import SteinerUpperBound.LargeCoverProgram.PointResources
public import SteinerUpperBound.LargeCoverProgram.PointSupport

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n d B : ℕ}

/-- Exact transport of ANY joint work/metric/retention/disclosure test through
the actual point-frame code. In particular this transports original-counter
Good tests without comparing different compiled seed types. -/
theorem afterPointFrame_counter_test (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (afterPointFrame D vo f c).evaluate w bits
      (fun o => F o.work o.metricQueries o.retentionQueries o.positiveReplies) =
      let base := (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work
      if (LocalAccess.hitsResult D f.points).value then F (base + 8) 0 0 0 else
        (CategoricalCoupling.bernoulli (inverseRate f.points.length)).expect (fun initiate =>
          if initiate then (vo f c).evaluate w bits (fun o =>
            F (base + 18 + o.work) o.metricQueries o.retentionQueries o.positiveReplies)
          else F (base + 14) 0 0 0) := by
  rw [afterPointFrame, Code.evaluate_bind, LocalAccess.hits_evaluates w bits,
    Code.evaluate_bind, length_evaluates w bits]
  rw [(length_result f.points).1]
  have hh := LocalAccess.hits_counters D f.points
  have hl := length_result f.points
  cases hhit : (LocalAccess.hitsResult D f.points).value
  · simp only [hhit, Bool.false_eq_true, ite_false, Code.evaluate, Outcome.add, Outcome.combine,
      hh.1, hh.2.1, hh.2.2, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2, Nat.zero_add, Nat.add_zero]
    apply congrArg (CategoricalCoupling.bernoulli (inverseRate f.points.length)).expect
    funext initiate
    cases initiate
    · simp only [Bool.false_eq_true, ite_false, Code.evaluate, Outcome.pure]
      congr 1 <;> omega
    · simp only [ite_true, Code.evaluate, Code.evaluate_bind, Outcome.add, Outcome.combine, Outcome.pure]
      apply congrArg ((vo f c).evaluate w bits)
      funext o
      congr 1 <;> omega
  · simp only [hhit, ite_true, Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
      hh.1, hh.2.1, hh.2.2, hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2, Nat.zero_add, Nat.add_zero]
    congr 1 <;> omega

theorem point_counter_test (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) :
    (point key a vertices terminals D vo root c).evaluate w bits
      (fun o => F o.work o.metricQueries o.retentionQueries o.positiveReplies) =
      let r := Cache.resolved bits (key root) c
      let l := LocalAccess.locateResult w bits key a d B vertices terminals root r.value.2
      if r.value.1 then
        l.value.frame.elim
          (F (r.work + l.work + 8) (r.metricQueries + l.metricQueries)
            (r.retentionQueries + l.retentionQueries) (r.positiveReplies + l.positiveReplies))
          (fun f => (afterPointFrame D vo f l.value.cache).evaluate w bits (fun o =>
            F (r.work + l.work + 8 + o.work) (r.metricQueries + l.metricQueries + o.metricQueries)
              (r.retentionQueries + l.retentionQueries + o.retentionQueries)
              (r.positiveReplies + l.positiveReplies + o.positiveReplies)))
      else F (r.work + 4) r.metricQueries r.retentionQueries r.positiveReplies := by
  rw [point, Code.evaluate_bind, Cache.resolve_evaluates w bits]
  dsimp only
  cases hr : (Cache.resolved bits (key root) c).value.1
  · simp only [hr, Bool.false_eq_true, ite_false, Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
      Nat.add_zero]
  · simp only [hr, ite_true, Code.evaluate, Code.evaluate_bind]
    rw [LocalAccess.locate_evaluates w bits]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame
    · simp only [afterPointLocate, hf, Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
        Option.elim_none, Nat.add_zero]
      congr 1 <;> omega
    · simp only [afterPointLocate, hf, Code.evaluate, Outcome.add, Outcome.combine, Option.elim_some]
      apply congrArg ((afterPointFrame D vo _ _).evaluate w bits)
      funext o
      congr 1 <;> omega

theorem afterPointFrame_work_tail (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (threshold : ℝ) (ht : 0 ≤ threshold) :
    (afterPointFrame D vo f c).evaluate w bits (fun o =>
      if ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) + threshold <
        (o.work : ℝ) then 1 else 0) =
      frameInitiation D f * (vo f c).evaluate w bits
        (fun o => if threshold < (o.work : ℝ) then 1 else 0) := by
  rw [afterPointFrame_counter_test w bits D vo f c
    (fun work _ _ _ => if
      (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) + threshold <
        (work : ℝ) then 1 else 0)]
  dsimp only
  have h8 : ¬ (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) + threshold <
      ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 8 : ℕ) := by
    push_cast
    linarith
  have h14 : ¬ (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) + threshold <
      ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 14 : ℕ) := by
    push_cast
    linarith
  have hc (z : ℕ) : ((((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) +
      threshold < ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 + z : ℕ)) ↔
      threshold < (z : ℝ) := by push_cast; constructor <;> intro h <;> linarith
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false, h14, hc]
    rw [SavingScores.bernoulli_expect]
    simp only [ite_true, Bool.false_eq_true, ite_false, h14, zero_mul, mul_zero, add_zero, frameInitiation, hh]
  · simp only [hh, ite_true, frameInitiation, zero_mul]
    rw [ite_eq_right h8]

theorem afterPointFrame_positive_tail (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (threshold : ℝ) (ht : 0 ≤ threshold) :
    (afterPointFrame D vo f c).evaluate w bits
      (fun o => if threshold < (o.positiveReplies : ℝ) then 1 else 0) =
      frameInitiation D f * (vo f c).evaluate w bits
        (fun o => if threshold < (o.positiveReplies : ℝ) then 1 else 0) := by
  rw [afterPointFrame_counter_test w bits D vo f c
    (fun _ _ _ positive => if threshold < (positive : ℝ) then 1 else 0)]
  dsimp only
  have hz : ¬ threshold < (0 : ℝ) := not_lt.mpr ht
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false, Nat.cast_zero, hz]
    rw [SavingScores.bernoulli_expect]
    simp only [ite_true, Bool.false_eq_true, ite_false, Nat.cast_zero, hz, zero_mul, mul_zero, add_zero, frameInitiation, hh]
  · simp [hh, frameInitiation, hz]

noncomputable def pointCallCost (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (F : Outcome (Bool × Cache Q) → ℝ) : ℝ :=
  let r := Cache.resolved bits (key root) c
  let l := LocalAccess.locateResult w bits key a d B vertices terminals root r.value.2
  if bits (key root) then l.value.frame.elim 0 (fun f =>
    frameInitiation D f * (vo f l.value.cache).evaluate w bits F) else 0

/-- Actual work tail, with all eager exploration/preparation/bitmap/length
and dispatch work charged BEFORE the initiation-weighted callback tail. -/
theorem point_work_tail (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (hnd : terminals.Nodup) (hroot : root ∈ terminals)
    (threshold : ℝ) (ht : 0 ≤ threshold) :
    (point key a vertices terminals D vo root c).evaluate w bits
      (fun o => if (pointBudget vertices.length terminals.length d B : ℝ) + threshold < o.work then 1 else 0) ≤
      pointCallCost w bits key a vertices terminals D vo root c
        (fun o => if threshold < (o.work : ℝ) then 1 else 0) := by
  rw [point_counter_test w bits key a vertices terminals D vo root c
    (fun work _ _ _ => if (pointBudget vertices.length terminals.length d B : ℝ) + threshold <
      (work : ℝ) then 1 else 0)]
  dsimp only [pointCallCost]
  have hr := Cache.resolved_correct bits (key root) c hc
  have hw := Cache.resolved_work_le bits (key root) c
  rw [hr.1]
  cases hb : bits (key root)
  · simp only [hb, Bool.false_eq_true, ite_false]
    have hn : ¬ (pointBudget vertices.length terminals.length d B : ℝ) + threshold <
        ((Cache.resolved bits (key root) c).work + 4 : ℕ) := by
      have hh : (Cache.resolved bits (key root) c).work + 4 ≤
          pointBudget vertices.length terminals.length d B := by dsimp [pointBudget]; omega
      have hh' : (((Cache.resolved bits (key root) c).work + 4 : ℕ) : ℝ) ≤
          pointBudget vertices.length terminals.length d B := by exact_mod_cast hh
      linarith
    simp only [hn, ite_false, le_refl]
  · simp only [hb, ite_true]
    have hx : root ∈ ComponentExplore.retained bits key
        (@List.toFinset (Fin n) (Classical.decEq _) terminals) := by
      simp [ComponentExplore.retained, hroot, hb]
    have hl := LocalAccess.locate_work w bits key a d B vertices terminals root
      (Cache.resolved bits (key root) c).value.2 hr.2 hnd hx
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame with
    | none =>
      simp only [hf, Option.elim_none]
      have hn : ¬ (pointBudget vertices.length terminals.length d B : ℝ) + threshold <
          ((Cache.resolved bits (key root) c).work +
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).work + 8 : ℕ) := by
        have hh : (Cache.resolved bits (key root) c).work +
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).work + 8 ≤
            pointBudget vertices.length terminals.length d B := by dsimp [pointBudget]; omega
        have hh' : (((Cache.resolved bits (key root) c).work +
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).work + 8 : ℕ) : ℝ) ≤
            pointBudget vertices.length terminals.length d B := by exact_mod_cast hh
        linarith
      simp only [hn, ite_false, le_refl]
    | some f =>
      simp only [hf, Option.elim_some]
      have hlen := (LocalAccess.locate_some w bits key a d B vertices terminals root _ hr.2 hnd hx f hf).2.2
      have hh := LocalAccess.hits_work D f.points
      have hlength := (length_result f.points).2.1
      have hbase : (Cache.resolved bits (key root) c).work +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).work + 8 +
          ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18) ≤
          pointBudget vertices.length terminals.length d B := by
        dsimp [pointBudget]
        nlinarith
      calc
        _ ≤ (afterPointFrame D vo f
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).value.cache).evaluate w bits
            (fun o => if
              (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) +
                threshold < (o.work : ℝ) then 1 else 0) := by
          apply Code.evaluate_mono
          intro o
          by_cases h : (pointBudget vertices.length terminals.length d B : ℝ) + threshold <
              ((Cache.resolved bits (key root) c).work +
                (LocalAccess.locateResult w bits key a d B vertices terminals root
                  (Cache.resolved bits (key root) c).value.2).work + 8 + o.work : ℕ)
          · have hh' : (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) +
                threshold < (o.work : ℝ) := by
              have hbase' : (((Cache.resolved bits (key root) c).work +
                  (LocalAccess.locateResult w bits key a d B vertices terminals root
                    (Cache.resolved bits (key root) c).value.2).work + 8 +
                  ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18) : ℕ) : ℝ) ≤
                  pointBudget vertices.length terminals.length d B := by exact_mod_cast hbase
              push_cast at hbase' h ⊢
              linarith
            simp only [h, hh', ite_true, le_refl]
          · simp only [h, ite_false]
            split_ifs <;> norm_num
        _ = _ := afterPointFrame_work_tail w bits D vo f _ threshold ht

theorem point_positive_tail (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (threshold : ℝ) (ht : 0 ≤ threshold) :
    (point key a vertices terminals D vo root c).evaluate w bits
      (fun o => if (B : ℝ) + 1 + threshold < o.positiveReplies then 1 else 0) ≤
      pointCallCost w bits key a vertices terminals D vo root c
        (fun o => if threshold < (o.positiveReplies : ℝ) then 1 else 0) := by
  rw [point_counter_test w bits key a vertices terminals D vo root c
    (fun _ _ _ positive => if (B : ℝ) + 1 + threshold < (positive : ℝ) then 1 else 0)]
  dsimp only [pointCallCost]
  have hr := Cache.resolved_correct bits (key root) c hc
  have hp := Cache.resolved_positive_le bits (key root) c
  have hl := LocalAccess.locate_positive w bits key a d B vertices terminals root
    (Cache.resolved bits (key root) c).value.2
  have hp' : ((Cache.resolved bits (key root) c).positiveReplies : ℝ) ≤ 1 := by exact_mod_cast hp
  have hl' : ((LocalAccess.locateResult w bits key a d B vertices terminals root
    (Cache.resolved bits (key root) c).value.2).positiveReplies : ℝ) ≤ B := by exact_mod_cast hl
  rw [hr.1]
  cases hb : bits (key root)
  · simp only [hb, Bool.false_eq_true, ite_false]
    have hn : ¬ (B : ℝ) + 1 + threshold < (Cache.resolved bits (key root) c).positiveReplies := by
      linarith [(show (0 : ℝ) ≤ B by positivity)]
    simp only [hn, ite_false, le_refl]
  · simp only [hb, ite_true]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame with
    | none =>
      simp only [hf, Option.elim_none]
      have hn : ¬ (B : ℝ) + 1 + threshold <
          ((Cache.resolved bits (key root) c).positiveReplies +
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).positiveReplies : ℕ) := by
        push_cast
        linarith
      simp only [hn, ite_false, le_refl]
    | some f =>
      simp only [hf, Option.elim_some]
      calc
        _ ≤ (afterPointFrame D vo f
            (LocalAccess.locateResult w bits key a d B vertices terminals root
              (Cache.resolved bits (key root) c).value.2).value.cache).evaluate w bits
            (fun o => if threshold < (o.positiveReplies : ℝ) then 1 else 0) := by
          apply Code.evaluate_mono
          intro o
          by_cases h : (B : ℝ) + 1 + threshold <
              ((Cache.resolved bits (key root) c).positiveReplies +
                (LocalAccess.locateResult w bits key a d B vertices terminals root
                  (Cache.resolved bits (key root) c).value.2).positiveReplies + o.positiveReplies : ℕ)
          · have ho : threshold < (o.positiveReplies : ℝ) := by push_cast at h; linarith
            simp only [h, ho, ite_true, le_refl]
          · simp only [h, ite_false]
            split_ifs <;> norm_num
        _ = _ := afterPointFrame_positive_tail w bits D vo f _ threshold ht

private theorem min_shift_bound (base value threshold : ℝ) (hb : 0 ≤ base) :
    min (base + value) threshold ≤ base + min value threshold := by
  by_cases hv : value ≤ threshold
  · rw [min_eq_left hv]
    exact min_le_left _ _
  · rw [min_eq_right (le_of_not_ge hv)]
    exact (min_le_right _ _).trans (by linarith)

theorem afterPointFrame_work_min (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (threshold : ℝ) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => min (o.work : ℝ) threshold) ≤
      ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) +
        frameInitiation D f * (vo f c).evaluate w bits (fun o => min (o.work : ℝ) threshold) := by
  rw [afterPointFrame_counter_test w bits D vo f c (fun work _ _ _ => min (work : ℝ) threshold)]
  dsimp only
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false, frameInitiation]
    calc
      _ ≤ (CategoricalCoupling.bernoulli (inverseRate f.points.length)).expect (fun initiate =>
          (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) +
            if initiate then (vo f c).evaluate w bits (fun o => min (o.work : ℝ) threshold) else 0) := by
        apply Law.expect_mono
        intro initiate
        cases initiate
        · simp only [Bool.false_eq_true, ite_false, add_zero]
          apply (min_le_left _ _).trans
          exact_mod_cast (show (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 14 ≤
            (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 by omega)
        · simp only [ite_true]
          apply (Code.evaluate_mono w bits (vo f c) (fun o => show
            min (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 + o.work : ℕ) : ℝ) threshold ≤
              (((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 : ℕ) : ℝ) +
                min (o.work : ℝ) threshold by
              push_cast
              exact min_shift_bound _ _ _ (by positivity))).trans_eq
                (by rw [Code.evaluate_add, Code.evaluate_const])
      _ = _ := by
        rw [Law.expect_add, Law.expect_const, SavingScores.bernoulli_expect]
        simp only [ite_true, Bool.false_eq_true, ite_false, mul_zero, add_zero]
  · simp only [hh, ite_true, frameInitiation, zero_mul, add_zero]
    apply (min_le_left _ _).trans
    exact_mod_cast (show (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 8 ≤
      (LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18 by omega)

theorem afterPointFrame_positive_min (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (D : Vector Bool n) (vo : VO Q n d B) (f : LocalAccess.Frame (Fin n) d B)
    (c : Cache Q) (threshold : ℝ) (ht : 0 ≤ threshold) :
    (afterPointFrame D vo f c).evaluate w bits (fun o => min (o.positiveReplies : ℝ) threshold) =
      frameInitiation D f * (vo f c).evaluate w bits (fun o => min (o.positiveReplies : ℝ) threshold) := by
  rw [afterPointFrame_counter_test w bits D vo f c (fun _ _ _ positive => min (positive : ℝ) threshold)]
  dsimp only
  cases hh : (LocalAccess.hitsResult D f.points).value
  · simp only [hh, Bool.false_eq_true, ite_false, Nat.cast_zero, min_eq_left ht]
    rw [SavingScores.bernoulli_expect]
    simp only [ite_true, Bool.false_eq_true, ite_false, frameInitiation, hh, ite_false,
      Nat.cast_zero, min_eq_left ht, mul_zero, add_zero]
  · simp [hh, frameInitiation, ht]

/-- No callback cost assumption is used: only its ACTUAL clipped counter is
initiation weighted, and eager preparation stays fully in the base account. -/
theorem point_work_min (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (hnd : terminals.Nodup) (hroot : root ∈ terminals)
    (threshold : ℝ) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => min (o.work : ℝ) threshold) ≤
      pointBudget vertices.length terminals.length d B +
        pointCallCost w bits key a vertices terminals D vo root c (fun o => min (o.work : ℝ) threshold) := by
  rw [point_counter_test w bits key a vertices terminals D vo root c (fun work _ _ _ => min (work : ℝ) threshold)]
  dsimp only [pointCallCost]
  have hr := Cache.resolved_correct bits (key root) c hc
  have hw := Cache.resolved_work_le bits (key root) c
  rw [hr.1]
  cases hb : bits (key root)
  · simp only [hb, Bool.false_eq_true, ite_false, add_zero]
    apply (min_le_left _ _).trans
    exact_mod_cast (show (Cache.resolved bits (key root) c).work + 4 ≤
      pointBudget vertices.length terminals.length d B by dsimp [pointBudget]; omega)
  · simp only [hb, ite_true]
    have hx : root ∈ ComponentExplore.retained bits key
        (@List.toFinset (Fin n) (Classical.decEq _) terminals) := by
      simp [ComponentExplore.retained, hroot, hb]
    have hl := LocalAccess.locate_work w bits key a d B vertices terminals root
      (Cache.resolved bits (key root) c).value.2 hr.2 hnd hx
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame with
    | none =>
      simp only [hf, Option.elim_none, add_zero]
      apply (min_le_left _ _).trans
      exact_mod_cast (show (Cache.resolved bits (key root) c).work +
        (LocalAccess.locateResult w bits key a d B vertices terminals root
          (Cache.resolved bits (key root) c).value.2).work + 8 ≤
        pointBudget vertices.length terminals.length d B by dsimp [pointBudget]; omega)
    | some f =>
      simp only [hf, Option.elim_some]
      have hlen := (LocalAccess.locate_some w bits key a d B vertices terminals root _ hr.2 hnd hx f hf).2.2
      have hh := LocalAccess.hits_work D f.points
      have hlength := (length_result f.points).2.1
      have hbase : (Cache.resolved bits (key root) c).work +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).work + 8 +
          ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18) ≤
          pointBudget vertices.length terminals.length d B := by dsimp [pointBudget]; nlinarith
      have hmono := Code.evaluate_mono w bits
        (afterPointFrame D vo f
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).value.cache)
        (F := fun o => min (((Cache.resolved bits (key root) c).work +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).work + 8 + o.work : ℕ) : ℝ) threshold)
        (G := fun o => (((Cache.resolved bits (key root) c).work +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).work + 8 : ℕ) : ℝ) + min (o.work : ℝ) threshold)
        (fun o => by push_cast; exact min_shift_bound _ _ _ (by positivity))
      rw [Code.evaluate_add, Code.evaluate_const] at hmono
      have hframe := afterPointFrame_work_min w bits D vo f
        (LocalAccess.locateResult w bits key a d B vertices terminals root
          (Cache.resolved bits (key root) c).value.2).value.cache threshold
      have hbase' : (((Cache.resolved bits (key root) c).work +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).work + 8 +
          ((LocalAccess.hitsResult D f.points).work + (lengthResult f.points).work + 18) : ℕ) : ℝ) ≤
          pointBudget vertices.length terminals.length d B := by exact_mod_cast hbase
      push_cast at hbase' hmono hframe ⊢
      linarith

theorem point_positive_min (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (threshold : ℝ) (ht : 0 ≤ threshold) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => min (o.positiveReplies : ℝ) threshold) ≤
      (B : ℝ) + 1 +
        pointCallCost w bits key a vertices terminals D vo root c (fun o => min (o.positiveReplies : ℝ) threshold) := by
  rw [point_counter_test w bits key a vertices terminals D vo root c (fun _ _ _ positive => min (positive : ℝ) threshold)]
  dsimp only [pointCallCost]
  have hr := Cache.resolved_correct bits (key root) c hc
  have hp := Cache.resolved_positive_le bits (key root) c
  have hl := LocalAccess.locate_positive w bits key a d B vertices terminals root
    (Cache.resolved bits (key root) c).value.2
  have hp' : ((Cache.resolved bits (key root) c).positiveReplies : ℝ) ≤ 1 := by exact_mod_cast hp
  have hl' : ((LocalAccess.locateResult w bits key a d B vertices terminals root
    (Cache.resolved bits (key root) c).value.2).positiveReplies : ℝ) ≤ B := by exact_mod_cast hl
  rw [hr.1]
  cases hb : bits (key root)
  · simp only [hb, Bool.false_eq_true, ite_false, add_zero]
    exact (min_le_left _ _).trans (by linarith [(show (0 : ℝ) ≤ B by positivity)])
  · simp only [hb, ite_true]
    cases hf : (LocalAccess.locateResult w bits key a d B vertices terminals root
        (Cache.resolved bits (key root) c).value.2).value.frame with
    | none =>
      simp only [hf, Option.elim_none, add_zero]
      apply (min_le_left _ _).trans
      push_cast
      linarith
    | some f =>
      simp only [hf, Option.elim_some]
      have hmono := Code.evaluate_mono w bits
        (afterPointFrame D vo f
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).value.cache)
        (F := fun o => min (((Cache.resolved bits (key root) c).positiveReplies +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).positiveReplies + o.positiveReplies : ℕ) : ℝ) threshold)
        (G := fun o => (((Cache.resolved bits (key root) c).positiveReplies +
          (LocalAccess.locateResult w bits key a d B vertices terminals root
            (Cache.resolved bits (key root) c).value.2).positiveReplies : ℕ) : ℝ) +
          min (o.positiveReplies : ℝ) threshold)
        (fun o => by push_cast; exact min_shift_bound _ _ _ (by positivity))
      rw [Code.evaluate_add, Code.evaluate_const, afterPointFrame_positive_min w bits D vo f _ threshold ht] at hmono
      push_cast at hmono ⊢
      linarith

theorem point_clipped_expected (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (key : Fin n → Q) (a : ℝ) (vertices terminals : List (Fin n))
    (D : Vector Bool n) (vo : VO Q n d B) (root : Fin n) (c : Cache Q)
    (hc : Cache.Correct bits c) (hnd : terminals.Nodup) (hroot : root ∈ terminals)
    (threshold : ℝ) (ht : 0 ≤ threshold) :
    (point key a vertices terminals D vo root c).evaluate w bits (fun o => min (o.work : ℝ) threshold) ≤
        pointBudget vertices.length terminals.length d B +
          pointCallCost w bits key a vertices terminals D vo root c (fun o => min (o.work : ℝ) threshold) ∧
      (point key a vertices terminals D vo root c).evaluate w bits (fun o => min (o.positiveReplies : ℝ) threshold) ≤
        (B : ℝ) + 1 +
          pointCallCost w bits key a vertices terminals D vo root c (fun o => min (o.positiveReplies : ℝ) threshold) :=
  ⟨point_work_min w bits key a vertices terminals D vo root c hc hnd hroot threshold,
    point_positive_min w bits key a vertices terminals D vo root c hc threshold ht⟩

end SteinerUpperBound.LargeCoverProgram

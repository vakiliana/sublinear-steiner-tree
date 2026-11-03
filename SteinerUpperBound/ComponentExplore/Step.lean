module

public import SteinerUpperBound.ComponentExplore.Memory

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open QueryProgram
open scoped Classical

variable {V Q : Type*}

namespace Memory

def remember (s : Memory V Q) (y : V) (bit : Bool) (c : Cache Q) : Memory V Q :=
  if bit then ⟨y :: s.points, s.processed, s.count + 1, c⟩ else {s with cache := c}

theorem Valid.remember (b : Q → Bool) (s : Memory V Q) (hs : Valid b s)
    (y : V) (hy : y ∉ s.points) (bit : Bool) (c : Cache Q) (hc : Cache.Correct b c) :
    Valid b (s.remember y bit c) := by
  cases bit with
  | false => exact ⟨hs.points_nodup, hs.processed_nodup, hs.count_eq, hc⟩
  | true =>
      refine ⟨List.nodup_cons.mpr ⟨hy, hs.points_nodup⟩, hs.processed_nodup, ?_, hc⟩
      change s.count + 1 = s.points.length + 1
      exact congrArg (· + 1) hs.count_eq

end Memory

noncomputable def stepProgram (key : V → Q) (a : ℝ) (B : ℕ) (x : V)
    (s : Memory V Q) (y : V) : Code (Sym2 V) Q (Memory V Q) :=
  .tick 0 (if B < s.count then .pure s else
    (member y s.points).bind (fun seen =>
      .tick 0 (if seen then .pure s else
        .metric (Sym2.mk x y) (fun d =>
          .tick 0 (if d < a then
            (Cache.resolve (key y) s.cache).bind (fun r =>
              .tick 3 (.pure (s.remember y r.1 r.2)))
          else .pure s)))))

noncomputable def stepResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) : Outcome (Memory V Q) :=
  if B < s.count then (Outcome.pure s).add 1 0 0 0 else
    let seen := memberResult y s.points
    let rest :=
      if seen.value then Outcome.pure s else
        let r := if w (Sym2.mk x y) < a then
            let c := Cache.resolved b (key y) s.cache
            c.combine ((Outcome.pure (s.remember y c.value.1 c.value.2)).add 4 0 0 0)
          else Outcome.pure s
        (r.add 1 0 0 0).add 1 1 0 0
    (seen.combine (rest.add 1 0 0 0)).add 1 0 0 0

theorem step_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    Code.Evaluates w b (stepProgram key a B x s y) (stepResult w b key a B x s y) := by
  intro F
  by_cases hb : B < s.count
  · simp only [stepProgram, stepResult, hb, ite_true, Code.evaluate]
  · simp only [stepProgram, stepResult, hb, ite_false, Code.evaluate, Code.evaluate_bind]
    rw [member_evaluates w b y s.points]
    cases hs : (memberResult y s.points).value <;>
      simp only [hs, Bool.false_eq_true, ite_false, ite_true]
    · simp only [Code.evaluate]
      by_cases hd : w (Sym2.mk x y) < a
      · simp only [hd, ite_true, Code.evaluate_bind]
        rw [Cache.resolve_evaluates w b (key y) s.cache]
        simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
          Nat.add_assoc, Nat.zero_add, Nat.add_zero]
      · simp only [hd, ite_false, Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
          Nat.add_assoc, Nat.zero_add, Nat.add_zero]
    · simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure,
        Nat.add_assoc, Nat.zero_add, Nat.add_zero]

theorem resolved_positive_bit (b : Q → Bool) (q : Q) (c : Cache Q) :
    (Cache.resolved b q c).positiveReplies ≤
      if (Cache.resolved b q c).value.1 then 1 else 0 := by
  cases h : c q <;> simp only [Cache.resolved, h]
  · cases b q <;> decide
  · split <;> omega

theorem step_valid (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) (hs : Memory.Valid b s) :
    Memory.Valid b (stepResult w b key a B x s y).value := by
  by_cases hb : B < s.count
  · simpa only [stepResult, hb, ite_true, Outcome.add, Outcome.pure] using hs
  · by_cases hm : (memberResult y s.points).value = true
    · simpa only [stepResult, hb, ite_false, hm, ite_true, Outcome.add, Outcome.combine,
        Outcome.pure] using hs
    · have hnot : y ∉ s.points := fun h => hm ((member_value y s.points).mpr h)
      by_cases hd : w (Sym2.mk x y) < a
      · have hc := (Cache.resolved_correct b (key y) s.cache hs.cache_correct).2
        simpa only [stepResult, hb, ite_false, hm, hd, ite_true, Bool.false_eq_true, Outcome.add,
          Outcome.combine, Outcome.pure] using
          hs.remember b s y hnot (Cache.resolved b (key y) s.cache).value.1
            (Cache.resolved b (key y) s.cache).value.2 hc
      · simpa only [stepResult, hb, ite_false, hm, hd, Bool.false_eq_true, Outcome.add, Outcome.combine,
          Outcome.pure] using hs

theorem step_size (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) (hsize : s.count ≤ B + 1) :
    (stepResult w b key a B x s y).value.count ≤ B + 1 := by
  by_cases hb : B < s.count
  · simpa only [stepResult, hb, ite_true, Outcome.add, Outcome.pure] using hsize
  · by_cases hm : (memberResult y s.points).value = true
    · simpa only [stepResult, hb, ite_false, hm, ite_true, Outcome.add, Outcome.combine,
        Outcome.pure] using hsize
    · by_cases hd : w (Sym2.mk x y) < a
      · cases hr : (Cache.resolved b (key y) s.cache).value.1 <;>
          simp only [stepResult, hb, ite_false, hm, hd, ite_true, Bool.false_eq_true,
            Outcome.add, Outcome.combine, Outcome.pure, Memory.remember, hr] <;> omega
      · simpa only [stepResult, hb, ite_false, hm, hd, Bool.false_eq_true, Outcome.add, Outcome.combine,
          Outcome.pure] using hsize

theorem step_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    (stepResult w b key a B x s y).work ≤ 2 * s.points.length + 12 := by
  have hm := member_work y s.points
  have hc := Cache.resolved_work_le b (key y) s.cache
  by_cases hb : B < s.count <;>
    by_cases hs : (memberResult y s.points).value = true <;>
    by_cases hd : w (Sym2.mk x y) < a <;>
    simp only [stepResult, hb, hs, hd, ite_true, ite_false, Bool.false_eq_true, Outcome.add, Outcome.combine,
      Outcome.pure] <;> omega

theorem step_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    (stepResult w b key a B x s y).metricQueries ≤ 1 := by
  have hm := (member_counters y s.points).1
  have hc : (Cache.resolved b (key y) s.cache).metricQueries = 0 := by
    cases h : s.cache (key y) <;> simp only [Cache.resolved, h]
  by_cases hb : B < s.count <;>
    by_cases hs : (memberResult y s.points).value = true <;>
    by_cases hd : w (Sym2.mk x y) < a <;>
    simp only [stepResult, hb, hs, hd, ite_true, ite_false, Bool.false_eq_true, Outcome.add, Outcome.combine,
      Outcome.pure, hm, hc] <;> omega

theorem step_positive_potential (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    (stepResult w b key a B x s y).positiveReplies + s.count ≤
      (stepResult w b key a B x s y).value.count := by
  have hm := (member_counters y s.points).2.2
  have hc := resolved_positive_bit b (key y) s.cache
  cases hr : (Cache.resolved b (key y) s.cache).value.1 <;>
    simp only [hr, Bool.false_eq_true, ite_true, ite_false] at hc <;>
    by_cases hb : B < s.count <;>
      by_cases hs : (memberResult y s.points).value = true <;>
      by_cases hd : w (Sym2.mk x y) < a <;>
      simp only [stepResult, hb, hs, hd, ite_true, ite_false, Bool.false_eq_true, Outcome.add,
        Outcome.combine, Outcome.pure, hm, Memory.remember, hr] <;> omega

end SteinerUpperBound.ComponentExplore

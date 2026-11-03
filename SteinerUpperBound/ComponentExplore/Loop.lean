module

public import SteinerUpperBound.ComponentExplore.Scan

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open QueryProgram
open scoped Classical

set_option maxHeartbeats 800000

variable {V Q : Type*} [Fintype V]

namespace Memory

def process (s : Memory V Q) (x : V) : Memory V Q :=
  {s with processed := x :: s.processed}

theorem Valid.process (b : Q → Bool) (s : Memory V Q) (hs : Valid b s)
    (x : V) (hx : x ∉ s.processed) : Valid b (s.process x) :=
  ⟨hs.points_nodup, List.nodup_cons.mpr ⟨hx, hs.processed_nodup⟩,
    hs.count_eq, hs.cache_correct⟩

end Memory

theorem pendingResult_some (found done l : List V) {x : V}
    (h : (pendingResult found done l).value = some x) :
    x ∈ l ∧ x ∈ found.toFinset ∧ x ∉ done := by
  have hp := pending_some l found.toFinset done.toFinset
    ((pending_value found done l).symm.trans h)
  exact ⟨hp.1, hp.2.1, fun hx => hp.2.2 (List.mem_toFinset.mpr hx)⟩

structure Answer (V Q : Type*) where
  memory : Memory V Q
  complete : Bool

noncomputable def Answer.project (r : Answer V Q) : Result V :=
  ⟨r.memory.graphState, r.complete⟩

noncomputable def loopProgram (key : V → Q) (a : ℝ) (B : ℕ) (l : List V) :
    ℕ → Memory V Q → Code (Sym2 V) Q (Answer V Q)
  | 0, s =>
      .tick 0 (if B < s.count then .pure ⟨s, false⟩ else
        (pendingProgram s.points s.processed l).bind (fun p =>
          .tick 0 (.pure ⟨s, p.isNone⟩)))
  | fuel + 1, s =>
      .tick 0 (if B < s.count then .pure ⟨s, false⟩ else
        (pendingProgram s.points s.processed l).bind (fun p =>
          .tick 0 (match p with
            | none => .pure ⟨s, true⟩
            | some x => .tick 0 ((scanProgram key a B x l (s.process x)).bind
                (fun t => loopProgram key a B l fuel t)))))

noncomputable def loopResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) : ℕ → Memory V Q → Outcome (Answer V Q)
  | 0, s =>
      if B < s.count then (Outcome.pure ⟨s, false⟩).add 1 0 0 0 else
        let p := pendingResult s.points s.processed l
        (p.combine ((Outcome.pure ⟨s, p.value.isNone⟩).add 1 0 0 0)).add 1 0 0 0
  | fuel + 1, s =>
      if B < s.count then (Outcome.pure ⟨s, false⟩).add 1 0 0 0 else
        let p := pendingResult s.points s.processed l
        let rest : Outcome (Answer V Q) := match p.value with
          | none => Outcome.pure ⟨s, true⟩
          | some x =>
              let r := scanResult w b key a B x l (s.process x)
              (r.combine (loopResult w b key a B l fuel r.value)).add 1 0 0 0
        (p.combine (rest.add 1 0 0 0)).add 1 0 0 0

theorem loop_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q) :
    Code.Evaluates w b (loopProgram key a B l fuel s) (loopResult w b key a B l fuel s) := by
  induction fuel generalizing s with
  | zero =>
      intro F
      by_cases hb : B < s.count
      · simp only [loopProgram, loopResult, hb, ite_true, Code.evaluate]
      · simp only [loopProgram, loopResult, hb, ite_false, Code.evaluate, Code.evaluate_bind]
        rw [pending_evaluates w b s.points s.processed l] <;> simp only [Code.evaluate]
  | succ fuel ih =>
      intro F
      by_cases hb : B < s.count
      · simp only [loopProgram, loopResult, hb, ite_true, Code.evaluate]
      · simp only [loopProgram, loopResult, hb, ite_false, Code.evaluate, Code.evaluate_bind]
        rw [pending_evaluates w b s.points s.processed l]
        cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simp only [hp, Code.evaluate]
        | some x =>
            simp only [hp, Code.evaluate, Code.evaluate_bind]
            rw [scan_evaluates w b key a B x l (s.process x), ih] <;>
              simp only [Outcome.add, Outcome.combine, Nat.add_assoc, Nat.zero_add, Nat.add_zero]

theorem loop_valid (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q) (hs : Memory.Valid b s) :
    Memory.Valid b (loopResult w b key a B l fuel s).value.memory := by
  induction fuel generalizing s with
  | zero =>
      by_cases hb : B < s.count <;>
        simpa only [loopResult, hb, ite_true, ite_false, Outcome.pure, Outcome.add,
          Outcome.combine] using hs
  | succ fuel ih =>
      by_cases hb : B < s.count
      · simpa only [loopResult, hb, ite_true, Outcome.pure, Outcome.add] using hs
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simpa only [loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
              Outcome.combine] using hs
        | some x =>
            have hx := (pendingResult_some s.points s.processed l hp).2.2
            have hn := scan_valid w b key a B x l (s.process x) (hs.process b s x hx)
            simpa only [loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
              Outcome.combine] using ih _ hn

theorem loop_count (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q) (hs : s.count ≤ B + 1) :
    (loopResult w b key a B l fuel s).value.memory.count ≤ B + 1 := by
  induction fuel generalizing s with
  | zero =>
      by_cases hb : B < s.count <;>
        simpa only [loopResult, hb, ite_true, ite_false, Outcome.pure, Outcome.add,
          Outcome.combine] using hs
  | succ fuel ih =>
      by_cases hb : B < s.count
      · simpa only [loopResult, hb, ite_true, Outcome.pure, Outcome.add] using hs
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simpa only [loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
              Outcome.combine] using hs
        | some x =>
            have hn := scan_count w b key a B x l (s.process x) hs
            simpa only [loopResult, hb, ite_false, hp, Outcome.pure, Outcome.add,
              Outcome.combine] using ih _ hn

theorem loop_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q) :
    (loopResult w b key a B l fuel s).metricQueries ≤ fuel * l.length := by
  induction fuel generalizing s with
  | zero =>
      have hp := (pending_counters s.points s.processed l).1
      by_cases hb : B < s.count <;>
        simp only [loopResult, hb, ite_true, ite_false, Outcome.add, Outcome.combine,
          Outcome.pure, hp] <;> omega
  | succ fuel ih =>
      have hp0 := (pending_counters s.points s.processed l).1
      by_cases hb : B < s.count
      · simp only [loopResult, hb, ite_true, Outcome.add, Outcome.pure]
        omega
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, hp0]
            omega
        | some x =>
            have hr := scan_metric_queries w b key a B x l (s.process x)
            have hn := ih (scanResult w b key a B x l (s.process x)).value
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, hp0]
            nlinarith

theorem loop_positive_potential (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q) :
    (loopResult w b key a B l fuel s).positiveReplies + s.count ≤
      (loopResult w b key a B l fuel s).value.memory.count := by
  induction fuel generalizing s with
  | zero =>
      have hp := (pending_counters s.points s.processed l).2.2
      by_cases hb : B < s.count <;>
        simp only [loopResult, hb, ite_true, ite_false, Outcome.add, Outcome.combine,
          Outcome.pure, hp] <;> omega
  | succ fuel ih =>
      have hp0 := (pending_counters s.points s.processed l).2.2
      by_cases hb : B < s.count
      · simp only [loopResult, hb, ite_true, Outcome.add, Outcome.pure]
        omega
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, hp0]
            omega
        | some x =>
            have hr := scan_positive_potential w b key a B x l (s.process x)
            have hn := ih (scanResult w b key a B x l (s.process x)).value
            change (scanResult w b key a B x l (s.process x)).positiveReplies + s.count ≤
              (scanResult w b key a B x l (s.process x)).value.count at hr
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, hp0]
            omega

noncomputable def iterationBudget (B k : ℕ) : ℕ :=
  (6 * (B + 1) + 20) * (k + 1)

theorem pending_budget (B : ℕ) (l : List V) (s : Memory V Q)
    (hpoints : s.points.length ≤ B + 1) (hdone : s.processed.length ≤ B + 1) :
    (pendingResult s.points s.processed l).work ≤
      (4 * (B + 1) + 4) * l.length + 1 := by
  have h := pending_work s.points s.processed l
  have hc : 2 * (s.points.length + s.processed.length) + 4 ≤ 4 * (B + 1) + 4 := by omega
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right l.length hc) 1)

theorem loop_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (fuel : ℕ) (s : Memory V Q)
    (hs : Memory.Valid b s) (hsize : s.count ≤ B + 1)
    (hprocessed : s.processed.length + fuel ≤ B + 1) :
    (loopResult w b key a B l fuel s).work ≤ (fuel + 1) * iterationBudget B l.length := by
  induction fuel generalizing s with
  | zero =>
      have hp := pending_work s.points s.processed l
      have hlen : s.points.length ≤ B + 1 := hs.count_eq ▸ hsize
      have hpu := pending_budget B l s hlen (by omega)
      by_cases hb : B < s.count <;>
        simp only [loopResult, hb, ite_true, ite_false, Outcome.add, Outcome.combine,
          Outcome.pure, iterationBudget] <;> nlinarith [Nat.zero_le (B * l.length)]
  | succ fuel ih =>
      have hp0 := pending_work s.points s.processed l
      have hlen : s.points.length ≤ B + 1 := hs.count_eq ▸ hsize
      have hpu := pending_budget B l s hlen (by omega)
      by_cases hb : B < s.count
      · simp only [loopResult, hb, ite_true, Outcome.add, Outcome.pure, iterationBudget]
        nlinarith [Nat.zero_le (fuel * B * l.length), Nat.zero_le (fuel * B),
          Nat.zero_le (fuel * l.length), Nat.zero_le (B * l.length)]
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, iterationBudget]
            nlinarith [Nat.zero_le (fuel * B * l.length), Nat.zero_le (fuel * B),
              Nat.zero_le (fuel * l.length), Nat.zero_le (B * l.length)]
        | some x =>
            have hx := (pendingResult_some s.points s.processed l hp).2.2
            have hv := hs.process b s x hx
            have hr := scan_work w b key a B x l (s.process x) hv hsize
            have hn := scan_valid w b key a B x l (s.process x) hv
            have hz := scan_count w b key a B x l (s.process x) hsize
            have hd : (scanResult w b key a B x l (s.process x)).value.processed.length +
                fuel ≤ B + 1 := by
              rw [scan_processed]
              simpa only [Memory.process, List.length_cons, Nat.add_assoc,
                Nat.add_left_comm, Nat.add_comm] using hprocessed
            have ht := ih _ hn hz hd
            simp only [loopResult, hb, ite_false, hp, Outcome.add, Outcome.combine,
              Outcome.pure, iterationBudget]
            dsimp only [iterationBudget] at ht
            nlinarith

end SteinerUpperBound.ComponentExplore

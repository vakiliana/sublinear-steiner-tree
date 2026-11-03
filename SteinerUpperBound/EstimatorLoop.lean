module

public import SteinerUpperBound.ProbabilityAccounting
public import SteinerUpperBound.EstimationAlgebra

@[expose] public section

namespace SteinerUpperBound.EstimatorLoop

open QueryProgram
open scoped Classical

structure ScaleRecord (I : Type*) where
  index : I
  saving : ℝ
  band : ℝ

structure State (I Q : Type*) where
  cache : Cache Q
  records : List (ScaleRecord I)

variable {M Q I : Type*}

abbrev Step (M Q I : Type*) :=
  I → Cache Q → Code M Q (Option (ℝ × ℝ × Cache Q))

noncomputable def rounds (step : Step M Q I) : List I → State I Q → Code M Q (Option (State I Q))
  | [], s => .tick 0 (.pure (some s))
  | i :: l, s =>
      (step i s.cache).bind (fun r =>
        .tick 4 (match r with
          | none => .pure none
          | some (z, t, c) => rounds step l ⟨c, ⟨i, z, t⟩ :: s.records⟩))

def GoodState (bits : Q → Bool) (R : I → ℝ → ℝ → Prop) (s : State I Q) : Prop :=
  Cache.Correct bits s.cache ∧ ∀ r ∈ s.records, R r.index r.saving r.band

def GoodStep (bits : Q → Bool) (R : I → ℝ → ℝ → Prop) (i : I)
    (r : Option (ℝ × ℝ × Cache Q)) : Prop :=
  ∃ z t c, r = some (z, t, c) ∧ Cache.Correct bits c ∧ R i z t

def Completed (bits : Q → Bool) (R : I → ℝ → ℝ → Prop) (indices old : List I)
    (r : Option (State I Q)) : Prop :=
  ∃ s, r = some s ∧ GoodState bits R s ∧
    s.records.map ScaleRecord.index = indices.reverse ++ old

theorem rounds_success (m : M → ℝ) (bits : Q → Bool) (step : Step M Q I)
    (R : I → ℝ → ℝ → Prop) (error : I → ℝ) (indices : List I) (s : State I Q)
    (hs : GoodState bits R s) (he : ∀ i ∈ indices, 0 ≤ error i)
    (hstep : ∀ i ∈ indices, ∀ c, Cache.Correct bits c →
      1 - error i ≤ Code.valueProbability m bits (step i c) (GoodStep bits R i)) :
    1 - (indices.map error).sum ≤
      Code.valueProbability m bits (rounds step indices s)
        (Completed bits R indices (s.records.map ScaleRecord.index)) := by
  induction indices generalizing s with
  | nil =>
      have hgood : Completed bits R [] (s.records.map ScaleRecord.index) (some s) :=
        ⟨s, rfl, hs, by simp⟩
      simp [rounds, Code.valueProbability, Code.evaluate, Outcome.add, Outcome.pure, hgood]
  | cons i l ih =>
      have htail : 0 ≤ (l.map error).sum := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        exact he j (List.mem_cons_of_mem _ hj)
      let next : Option (ℝ × ℝ × Cache Q) → Code M Q (Option (State I Q)) :=
        fun r => .tick 4 (match r with
          | none => .pure none
          | some (z, t, c) => rounds step l ⟨c, ⟨i, z, t⟩ :: s.records⟩)
      have hn (r : Option (ℝ × ℝ × Cache Q)) (hr : GoodStep bits R i r) :
          1 - (l.map error).sum ≤ Code.valueProbability m bits (next r)
            (Completed bits R (i :: l) (s.records.map ScaleRecord.index)) := by
        obtain ⟨z, t, c, rfl, hc, hR⟩ := hr
        let s' : State I Q := ⟨c, ⟨i, z, t⟩ :: s.records⟩
        have hs' : GoodState bits R s' := by
          refine ⟨hc, ?_⟩
          intro r hr
          rcases List.mem_cons.mp hr with hr | hr
          · subst r
            exact hR
          · exact hs.2 r hr
        have ht := ih s' hs'
          (fun j hj => he j (List.mem_cons_of_mem _ hj))
          (fun j hj c hc => hstep j (List.mem_cons_of_mem _ hj) c hc)
        simpa only [next, Code.valueProbability, Code.evaluate, Outcome.add, Completed,
          s', List.map_cons, List.reverse_cons, List.singleton_append, List.append_assoc] using ht
      have hbind := Code.bind_success m bits (step i s.cache) next
        (GoodStep bits R i) (Completed bits R (i :: l) (s.records.map ScaleRecord.index))
        (error i) (l.map error).sum (he i List.mem_cons_self) htail
        (hstep i List.mem_cons_self s.cache hs.1) hn
      simpa only [rounds, next, List.map_cons, List.sum_cons, sub_add_eq_sub_sub] using hbind

def totalStep (scale : I → ℝ) (totals : ℝ × ℝ) (r : ScaleRecord I) : Code M Q (ℝ × ℝ) :=
  .tick 4 (.pure (totals.1 + scale r.index * r.saving, totals.2 + r.band))

def totalResult (scale : I → ℝ) (totals : ℝ × ℝ) (r : ScaleRecord I) : Outcome (ℝ × ℝ) :=
  ⟨(totals.1 + scale r.index * r.saving, totals.2 + r.band), 5, 0, 0, 0⟩

def totals (scale : I → ℝ) (records : List (ScaleRecord I)) : Code M Q (ℝ × ℝ) :=
  Code.foldList (totalStep scale) records (0, 0)

def summed (scale : I → ℝ) (records : List (ScaleRecord I)) : Outcome (ℝ × ℝ) :=
  Code.folded (totalResult scale) records (0, 0)

theorem totals_evaluates (m : M → ℝ) (bits : Q → Bool) (scale : I → ℝ)
    (records : List (ScaleRecord I)) :
    Code.Evaluates m bits (totals scale records) (summed scale records) := by
  apply Code.foldList_evaluates
  intro s r F
  rfl

theorem folded_totals (scale : I → ℝ) (records : List (ScaleRecord I)) (s : ℝ × ℝ) :
    (Code.folded (totalResult scale) records s).value =
      (s.1 + (records.map (fun r => scale r.index * r.saving)).sum,
        s.2 + (records.map ScaleRecord.band).sum) := by
  induction records generalizing s with
  | nil => simp [Code.folded, Outcome.pure]
  | cons r l ih =>
      simpa only [Code.folded, Outcome.add, Outcome.combine, totalResult,
        List.map_cons, List.sum_cons, add_assoc] using
        ih (s.1 + scale r.index * r.saving, s.2 + r.band)

theorem totals_value (scale : I → ℝ) (records : List (ScaleRecord I)) :
    (summed scale records).value =
      ((records.map (fun r => scale r.index * r.saving)).sum,
        (records.map ScaleRecord.band).sum) := by
  simpa only [summed, zero_add] using folded_totals scale records (0, 0)

noncomputable def finish (scale : I → ℝ) (upper Qs Qq : ℝ)
    (r : Option (State I Q)) : Code M Q (Option ℝ) :=
  match r with
  | none => .tick 0 (.pure none)
  | some s => (totals scale s.records).bind (fun st =>
      .tick 5 (.pure (some (Estimation.output upper st.1 st.2 Qs Qq))))

theorem totals_work (scale : I → ℝ) (records : List (ScaleRecord I)) :
    (summed scale records).work ≤ 6 * records.length := by
  simpa only [summed] using Code.folded_work (totalResult scale) 5 (fun _ _ => le_rfl) records (0, 0)

theorem totals_counters (scale : I → ℝ) (records : List (ScaleRecord I)) :
    (summed scale records).metricQueries = 0 ∧ (summed scale records).retentionQueries = 0 ∧
      (summed scale records).positiveReplies = 0 := by
  have hg (s : ℝ × ℝ) :
      (Code.folded (totalResult scale) records s).metricQueries = 0 ∧
        (Code.folded (totalResult scale) records s).retentionQueries = 0 ∧
        (Code.folded (totalResult scale) records s).positiveReplies = 0 := by
    induction records generalizing s with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons r l ih =>
        simp only [Code.folded, Outcome.add, Outcome.combine, totalResult, Nat.zero_add]
        exact ih _
  exact hg _

end SteinerUpperBound.EstimatorLoop

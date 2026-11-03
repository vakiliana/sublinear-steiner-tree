module

public import SteinerLowerBound.MetricComparison.CompilerLaws
public import SteinerLowerBound.Screening.Adaptive

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Compiler

open scoped BigOperators Classical
open HardDistribution
open Decoder

variable {Q A C S Z Ω : Type*}

def reportRecord {n : ℕ} (r : Report Q A Z n) : List (Q × A) :=
  (List.ofFn r.1).filterMap id

@[simp]
theorem reportRecord_empty (r : Z) (n : ℕ) :
    reportRecord (emptyReport (Q := Q) (A := A) r n) = [] := by
  simp [reportRecord, emptyReport]

@[simp]
theorem reportRecord_prepend (q : Q) (a : A) {n : ℕ} (r : Report Q A Z n) :
    reportRecord (prependReport q a r) = (q, a) :: reportRecord r := by
  simp [reportRecord, prependReport, List.ofFn_succ]

@[simp]
theorem prependReport_snd (q : Q) (a : A) {n : ℕ} (r : Report Q A Z n) :
    (prependReport q a r).2 = r.2 := rfl

namespace Decoder

noncomputable def fullRun (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool) :
    DecisionTree Q A Z → List Q → Z × List (Q × A)
  | .leaf r, _ => (r, [])
  | .query q next, h =>
      let a := D.publicAnswer oracle h q
      let r := D.fullRun oracle (next a) (h ++ [q])
      (r.1, (q, a) :: r.2)

theorem execute_fullRun (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool)
    (t : DecisionTree Q A Z) (n : ℕ) (hn : Screening.DecisionTree.Bounded t n) (h : List Q) :
    (D.execute oracle n t h).2 = some (D.fullRun oracle t h).1 ∧
      reportRecord (D.execute oracle n t h) = (D.fullRun oracle t h).2 := by
  induction t generalizing n h with
  | leaf r =>
    simp only [execute, fullRun]
    exact ⟨rfl, reportRecord_empty r n⟩
  | query q next ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      obtain ⟨ho, ht⟩ := ih (D.publicAnswer oracle h q) n (hn _) (h ++ [q])
      simpa only [execute, fullRun, prependReport_snd, reportRecord_prepend] using
        And.intro ho (congrArg (List.cons (q, D.publicAnswer oracle h q)) ht)

theorem fullRun_static_output (D : Decoder Q A C S) (o : C × S → Bool)
    (t : DecisionTree Q A Z) (h : List Q) :
    (D.fullRun (fun _ => o) t h).1 =
      t.output (D.publicAnswer (fun _ => o) []) := by
  induction t generalizing h with
  | leaf => rfl
  | query q next ih =>
    simpa only [fullRun, DecisionTree.output, publicAnswer] using
      ih (D.publicAnswer (fun _ => o) h q) (h ++ [q])

theorem fullRun_static_transcript (D : Decoder Q A C S) (o : C × S → Bool)
    (t : DecisionTree Q A Z) (h : List Q) :
    (D.fullRun (fun _ => o) t h).2 =
      t.transcript (D.publicAnswer (fun _ => o) []) := by
  induction t generalizing h with
  | leaf => rfl
  | query q next ih =>
    simpa only [fullRun, DecisionTree.transcript, publicAnswer] using
      congrArg (List.cons (q, D.publicAnswer (fun _ => o) h q))
        (ih (D.publicAnswer (fun _ => o) h q) (h ++ [q]))

theorem fullRun_screening_record (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool)
    (t : DecisionTree Q A Z) (r : Screening.Record Q A) :
    Screening.DecisionTree.run (fun (_ : Unit) h q => D.publicAnswer oracle h q) () r t =
      r ++ (D.fullRun oracle t (Screening.questions r)).2 := by
  induction t generalizing r with
  | leaf => simp [Screening.DecisionTree.run, fullRun]
  | query q next ih =>
    simp only [Screening.DecisionTree.run]
    rw [ih]
    simp only [fullRun, Screening.questions, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]

variable [Fintype Q] [Fintype A] [Fintype C] [Fintype S] [Fintype Z]

theorem compiled_full_transcripts_close (D : Decoder Q A C S)
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree Q A Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) (E : Set (List (Q × A))) :
    |(k.centersLaw (C := C) w).prob {σ |
        t.transcript (D.publicAnswer
          (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) []) ∈ E} -
      (gatedCentersLaw (C := C) k w (small_of_R k hR)).prob {σ |
        (D.fullRun (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) t []).2 ∈ E}| ≤
      512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)) := by
  have hh := D.reports_close k w hR hm t ht q {r | reportRecord r ∈ E}
  simp only [staticReportLaw, gatedReportLaw, Law.prob_map, Set.mem_preimage,
    Set.mem_ofPred_eq] at hh
  have hs (σ : C → State S k.d) :
      reportRecord (D.execute (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) q t []) =
        t.transcript (D.publicAnswer
          (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) []) :=
    (D.execute_fullRun _ t q hq []).2.trans (D.fullRun_static_transcript _ t [])
  have hg (σ : C → GatedState S k.d) :
      reportRecord (D.execute (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) q t []) =
        (D.fullRun (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) t []).2 :=
    (D.execute_fullRun _ t q hq []).2
  simpa only [Set.preimage, Set.mem_ofPred_eq, hs, hg] using hh

theorem compiled_outputs_close (D : Decoder Q A C S)
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree Q A Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) (fallback : Z) :
    Law.Close
      ((k.centersLaw (C := C) w).map (fun σ =>
        t.output (D.publicAnswer (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) [])))
      ((gatedCentersLaw (C := C) k w (small_of_R k hR)).map (fun σ =>
        (D.fullRun (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) t []).1))
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  have hh := (D.reports_close k w hR hm t ht q).map (fun r => r.2.getD fallback)
  simp only [staticReportLaw, gatedReportLaw, map_comp] at hh
  have hs (σ : C → State S k.d) :
      (D.execute (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) q t []).2.getD fallback =
        t.output (D.publicAnswer
          (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) []) := by
    rw [(D.execute_fullRun _ t q hq []).1, Option.getD_some,
      D.fullRun_static_output]
  have hg (σ : C → GatedState S k.d) :
      (D.execute (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) q t []).2.getD fallback =
        (D.fullRun (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) h cu.1 cu.2) t []).1 := by
    rw [(D.execute_fullRun _ t q hq []).1, Option.getD_some]
  simpa only [hs, hg] using hh

end Decoder

end SteinerLowerBound.MetricComparison.Compiler

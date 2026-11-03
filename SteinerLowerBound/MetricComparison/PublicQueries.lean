module

public import SteinerLowerBound.MetricComparison.PublicGated

@[expose] public section

/-!
# Arbitrary public distance-query protocols

Public terminals are `Screening.Terminal S G I`, with a permutation from
public labels to internal positions. Queries are unordered pairs of public
terminals and centers. Replies use the shared four-element distance alphabet.

The compiler preserves every public query, including deterministic queries.
It uses a guarded center--special schedule; `Decoder.invariant_advance` and
`Decoder.schedule_eq_request` prove that the guard never changes a coherent
execution. Actual full transcripts and outputs are projections of the binary
observation laws. The final theorems average over iid weights and an independent
uniform terminal permutation, keeping the public decision tree fixed.
-/

namespace SteinerLowerBound.MetricComparison.Public

open scoped BigOperators Classical
open HardDistribution
open Screening (Terminal Reply)
open Compiler

variable {S G I C Z Ω : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable def onlineRun {Q A Z : Type*} (answer : List Q → Q → A) :
    DecisionTree Q A Z → List Q → Z × List (Q × A)
  | .leaf r, _ => (r, [])
  | .query q next, h =>
      let a := answer h q
      let r := onlineRun answer (next a) (h ++ [q])
      (r.1, (q, a) :: r.2)

theorem onlineRun_compiled {Q A Z : Type*} (D : Decoder Q A C S)
    (oracle : List (C × S) → C × S → Bool)
    (t : DecisionTree Q A Z) (h : List Q) :
    onlineRun (D.publicAnswer oracle) t h = D.fullRun oracle t h := by
  induction t generalizing h with
  | leaf => rfl
  | query q next ih =>
    simp only [onlineRun, Decoder.fullRun]
    rw [ih]

noncomputable def gatedRun (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset S) (t : DecisionTree (Queries S G I C) Reply Z)
    (h : List (Queries S G I C)) : Z × List (Queries S G I C × Reply) :=
  onlineRun (gatedAnswer π F H) t h

theorem gatedRun_compiled (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset S) (t : DecisionTree (Queries S G I C) Reply Z)
    (h : List (Queries S G I C)) :
    gatedRun π F H t h =
      (decoder π).fullRun (fun hs cu => TwoAnchor.answer F H hs cu.1 cu.2) t h := by
  have he : gatedAnswer π F H =
      (decoder π).publicAnswer (fun hs cu => TwoAnchor.answer F H hs cu.1 cu.2) :=
    funext fun h => funext fun q => gatedAnswer_eq_decoded π F H h q
  rw [gatedRun, he, onlineRun_compiled]

variable [Fintype C] [Fintype Z]

theorem conditional_report_projections (k : Setup S Ω) (w : S → Ω)
    (π : Equiv.Perm (Terminal S G I))
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) (q : ℕ) :
    (decoder π).staticReportLaw k w t q =
        ((History.staticObserver k w).observationLaw ((decoder π).schedule t) q).map
          ((decoder π).decodeReport q t) ∧
      (decoder π).gatedReportLaw k w hsmall t q =
        (canonicalObservationLaw k w hsmall ((decoder π).schedule t) q).map
          ((decoder π).decodeReport q t) :=
  ⟨(decoder π).staticReportLaw_projection k w t ht q,
    (decoder π).gatedReportLaw_projection k w hsmall t ht q⟩

theorem conditional_outputs_close (k : Setup S Ω) (w : S → Ω)
    (π : Equiv.Perm (Terminal S G I))
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) :
    Law.Close
      ((k.centersLaw (C := C) w).map (fun σ =>
        t.output (staticAnswer π (fun c => neighbors k.d (σ c)))))
      ((gatedCentersLaw (C := C) k w (small_of_R k hR)).map (fun σ =>
        (gatedRun π (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) t []).1))
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  have hh := (decoder π).compiled_outputs_close k w hR hm t ht q hq
    (t.output (fun _ => Reply.far))
  simpa only [staticAnswer, gatedRun_compiled] using hh

theorem conditional_transcripts_close (k : Setup S Ω) (w : S → Ω)
    (π : Equiv.Perm (Terminal S G I))
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q)
    (E : Set (List (Queries S G I C × Reply))) :
    |(k.centersLaw (C := C) w).prob {σ |
        t.transcript (staticAnswer π (fun c => neighbors k.d (σ c))) ∈ E} -
      (gatedCentersLaw (C := C) k w (small_of_R k hR)).prob {σ |
        (gatedRun π (fun c => fillerNeighbors (σ c).1)
          (fun c => potentialSupport (σ c).2) t []).2 ∈ E}| ≤
      512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)) := by
  have hh := (decoder π).compiled_full_transcripts_close k w hR hm t ht q hq E
  simpa only [staticAnswer, gatedRun_compiled] using hh

variable [Fintype Ω]

noncomputable def publicDataLaw (μ : Law Ω) :
    Law ((S → Ω) × Equiv.Perm (Terminal S G I)) :=
  Law.step (μ.iid S) (fun _ => Law.uniform (Equiv.Perm (Terminal S G I)))

noncomputable def metricOutputLaw (k : Setup S Ω) (μ : Law Ω)
    (t : DecisionTree (Queries S G I C) Reply Z) : Law Z :=
  (publicDataLaw (G := G) (I := I) μ).bind (fun data =>
    (k.centersLaw (C := C) data.1).map (fun σ =>
      t.output (staticAnswer data.2 (fun c => neighbors k.d (σ c)))))

noncomputable def gatedOutputLaw (k : Setup S Ω) (μ : Law Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Queries S G I C) Reply Z) : Law Z :=
  (publicDataLaw (G := G) (I := I) μ).bind (fun data =>
    (gatedCentersLaw (C := C) k data.1 hsmall).map (fun σ =>
      (gatedRun data.2 (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) t []).1))

theorem public_outputs_close (k : Setup S Ω) (μ : Law Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) :
    Law.Close (metricOutputLaw k μ t) (gatedOutputLaw k μ (small_of_R k hR) t)
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  have hh := Law.Close.bind_same (publicDataLaw (G := G) (I := I) μ)
    (fun data => (k.centersLaw (C := C) data.1).map (fun σ =>
      t.output (staticAnswer data.2 (fun c => neighbors k.d (σ c)))))
    (fun data => (gatedCentersLaw (C := C) k data.1 (small_of_R k hR)).map (fun σ =>
      (gatedRun data.2 (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) t []).1))
    (fun _ => 512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)))
    (fun data => conditional_outputs_close k data.1 data.2 hR hm t ht q hq)
  simpa only [Law.expect_const, metricOutputLaw, gatedOutputLaw] using hh

noncomputable def metricTranscriptProbability (k : Setup S Ω) (μ : Law Ω)
    (t : DecisionTree (Queries S G I C) Reply Z)
    (E : Set (List (Queries S G I C × Reply))) : ℝ :=
  (publicDataLaw (G := G) (I := I) μ).expect (fun data =>
    (k.centersLaw (C := C) data.1).prob {σ |
      t.transcript (staticAnswer data.2 (fun c => neighbors k.d (σ c))) ∈ E})

noncomputable def gatedTranscriptProbability (k : Setup S Ω) (μ : Law Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Queries S G I C) Reply Z)
    (E : Set (List (Queries S G I C × Reply))) : ℝ :=
  (publicDataLaw (G := G) (I := I) μ).expect (fun data =>
    (gatedCentersLaw (C := C) k data.1 hsmall).prob {σ |
      (gatedRun data.2 (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) t []).2 ∈ E})

theorem public_transcripts_close (k : Setup S Ω) (μ : Law Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q)
    (E : Set (List (Queries S G I C × Reply))) :
    |metricTranscriptProbability k μ t E -
      gatedTranscriptProbability k μ (small_of_R k hR) t E| ≤
      512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)) := by
  unfold metricTranscriptProbability gatedTranscriptProbability
  rw [← Law.expect_sub]
  apply ((publicDataLaw (G := G) (I := I) μ).abs_expect_le _).trans
  have hh := (publicDataLaw (G := G) (I := I) μ).expect_mono
    (fun data => conditional_transcripts_close k data.1 data.2 hR hm t ht q hq E)
  simpa only [Law.expect_const] using hh

section ScreeningInterface

variable {Q Q' A R : Type*}

def mapQuestions (f : Q → Q') : DecisionTree Q A R → DecisionTree Q' A R
  | .leaf r => .leaf r
  | .query q next => .query (f q) (fun a => mapQuestions f (next a))

theorem mem_used_mapQuestions [Fintype A] (f : Q → Q') (t : DecisionTree Q A R) (q' : Q') :
    q' ∈ (mapQuestions f t).used ↔ ∃ q ∈ t.used, f q = q' := by
  classical
  induction t with
  | leaf => simp [mapQuestions, DecisionTree.used]
  | query q next ih =>
    simp only [mapQuestions, DecisionTree.used, Finset.mem_insert, Finset.mem_biUnion,
      Finset.mem_univ, true_and, ih]
    aesop

theorem mapQuestions_noRepeats [Fintype A] (f : Q → Q') (hf : Function.Injective f)
    (t : DecisionTree Q A R) (ht : t.NoRepeats) : (mapQuestions f t).NoRepeats := by
  induction t with
  | leaf => trivial
  | query q next ih =>
    refine ⟨fun a => ih a (ht.1 a), ?_⟩
    intro a ha
    obtain ⟨r, hr, he⟩ := (mem_used_mapQuestions f (next a) (f q)).mp ha
    have hrq := hf he
    subst r
    exact ht.2 a hr

theorem mapQuestions_bounded (f : Q → Q') (t : DecisionTree Q A R) (n : ℕ)
    (ht : Screening.DecisionTree.Bounded t n) :
    Screening.DecisionTree.Bounded (mapQuestions f t) n := by
  induction t generalizing n with
  | leaf => trivial
  | query q next ih =>
    cases n with
    | zero => contradiction
    | succ n => exact fun a => ih a n (ht a)

theorem onlineRun_mapQuestions (f : Q → Q') (answer : List Q' → Q' → A)
    (t : DecisionTree Q A R) (h : List Q) :
    onlineRun answer (mapQuestions f t) (h.map f) =
      let r := onlineRun (fun h q => answer (h.map f) (f q)) t h
      (r.1, r.2.map (fun qa => (f qa.1, qa.2))) := by
  induction t generalizing h with
  | leaf => rfl
  | query q next ih =>
    simp only [mapQuestions, onlineRun]
    have hh : h.map f ++ [f q] = (h ++ [q]).map f := by simp
    rw [hh, ih]
    simp only [List.map_cons]

theorem onlineRun_screening_record (answer : List Q → Q → A)
    (t : DecisionTree Q A R) (r : Screening.Record Q A) :
    Screening.DecisionTree.run (fun (_ : Unit) h q => answer h q) () r t =
      r ++ (onlineRun answer t (Screening.questions r)).2 := by
  induction t generalizing r with
  | leaf => simp [Screening.DecisionTree.run, onlineRun]
  | query q next ih =>
    simp only [Screening.DecisionTree.run]
    rw [ih]
    simp only [onlineRun, Screening.questions, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]

theorem orient_injective : Function.Injective (orient : Queries S G I C →
    Screening.Query (Terminal S G I) C) := by
  intro q q' he
  have hh := congrArg encode he
  simpa only [encode_orient] using hh

theorem oriented_noRepeats (t : DecisionTree (Queries S G I C) Reply Z) (ht : t.NoRepeats) :
    (mapQuestions orient t).NoRepeats :=
  mapQuestions_noRepeats orient orient_injective t ht

theorem oriented_bounded (t : DecisionTree (Queries S G I C) Reply Z) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) :
    Screening.DecisionTree.Bounded (mapQuestions orient t) q :=
  mapQuestions_bounded orient t q hq

theorem gated_record_screening (π : Equiv.Perm (Terminal S G I)) (F H : C → Finset S)
    (t : DecisionTree (Queries S G I C) Reply Z) :
    Screening.DecisionTree.run
      (fun (_ : Unit) h q => Screening.queryAnswer π (internalSupport F) (internalSupport H) h q)
      () [] (mapQuestions orient t) =
        (gatedRun π F H t []).2.map (fun qa => (orient qa.1, qa.2)) := by
  rw [onlineRun_screening_record]
  simp only [Screening.questions, List.map_nil, List.nil_append]
  have hh := onlineRun_mapQuestions orient
    (Screening.queryAnswer π (internalSupport F) (internalSupport H)) t []
  simp only [List.map_nil] at hh
  rw [hh]
  rfl

theorem gated_record_recover (π : Equiv.Perm (Terminal S G I)) (F H : C → Finset S)
    (t : DecisionTree (Queries S G I C) Reply Z) :
    (Screening.DecisionTree.run
      (fun (_ : Unit) h q => Screening.queryAnswer π (internalSupport F) (internalSupport H) h q)
      () [] (mapQuestions orient t)).map (fun qa => (encode qa.1, qa.2)) =
        (gatedRun π F H t []).2 := by
  rw [gated_record_screening, List.map_map]
  simp only [Function.comp_def, encode_orient]
  exact List.map_id _

end ScreeningInterface

end SteinerLowerBound.MetricComparison.Public

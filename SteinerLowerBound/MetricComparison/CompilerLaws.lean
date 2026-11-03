module

public import SteinerLowerBound.MetricComparison.Compiler

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Compiler

open scoped BigOperators Classical
open HardDistribution

theorem law_ext {W : Type*} [Fintype W] (μ ν : Law W)
    (h : ∀ w, μ.mass w = ν.mass w) : μ = ν := by
  cases μ with
  | mk mass nonneg total =>
    cases ν with
    | mk mass' nonneg' total' =>
      have he : mass = mass' := funext h
      cases he
      rfl

theorem law_ext_prob {W : Type*} [Fintype W] (μ ν : Law W)
    (h : ∀ E, μ.prob E = ν.prob E) : μ = ν := by
  classical
  apply law_ext
  intro w
  simpa only [Law.prob, Set.mem_singleton_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] using h {w}

theorem map_comp {W X Y : Type*} [Fintype W] [Fintype X] [Fintype Y]
    (μ : Law W) (f : W → X) (g : X → Y) :
    (μ.map f).map g = μ.map (fun w => g (f w)) := by
  apply law_ext_prob
  intro E
  rw [Law.prob_map, Law.prob_map, Law.prob_map]
  rfl

namespace Decoder

variable {Q A C S Z Ω : Type*} [Fintype A] [Fintype S]

theorem binaryRun_static (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (root : DecisionTree Q A Z) (σ : C → State S k.d)
    (n : ℕ) (x : Control C (History S)) (h : List (C × S)) :
    D.binaryRun (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) root n x h =
      (History.staticObserver k w).run (D.schedule root) σ n x := by
  classical
  induction n generalizing x h with
  | zero => rfl
  | succ n ih =>
    cases he : D.schedule root x with
    | none =>
      simp only [binaryRun, Observer.run, Observer.globalAnswer, he, Option.toList_none,
        List.append_nil]
      exact congrArg (Prod.mk false) (ih _ _)
    | some cu =>
      simp only [binaryRun, Observer.run, Observer.globalAnswer, he, Option.toList_some,
        History.staticObserver]
      exact congrArg (Prod.mk _) (ih _ _)

theorem binaryRun_canonical (D : Decoder Q A C S) (root : DecisionTree Q A Z)
    (F H : C → Finset S) (n : ℕ) (x : Control C (History S)) (h : List (C × S)) :
    D.binaryRun (fun h cu => TwoAnchor.answer F H h cu.1 cu.2) root n x h =
      canonicalRun (D.schedule root) F H n x h := by
  induction n generalizing x h with
  | zero => rfl
  | succ n ih =>
    cases he : D.schedule root x with
    | none =>
      simp only [binaryRun, canonicalRun, he, Option.toList_none, List.append_nil]
      exact congrArg (Prod.mk false) (ih _ _)
    | some cu =>
      rcases cu with ⟨c, u⟩
      simp only [binaryRun, canonicalRun, he, Option.toList_some]
      exact congrArg (Prod.mk _) (ih _ _)

variable [Fintype C] [Fintype Q] [Fintype Z]

noncomputable def staticReportLaw (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (t : DecisionTree Q A Z) (q : ℕ) : Law (Report Q A Z q) :=
  (k.centersLaw (C := C) w).map (fun σ =>
    D.execute (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) q t [])

noncomputable def gatedReportLaw (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree Q A Z) (q : ℕ) : Law (Report Q A Z q) :=
  (gatedCentersLaw (C := C) k w hsmall).map (fun σ =>
    D.execute (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
      (fun c => potentialSupport (σ c).2) h cu.1 cu.2) q t [])

theorem staticReportLaw_projection (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (t : DecisionTree Q A Z) (ht : t.NoRepeats) (q : ℕ) :
    D.staticReportLaw k w t q =
      ((History.staticObserver k w).observationLaw (D.schedule t) q).map
        (D.decodeReport q t) := by
  classical
  change (k.centersLaw w).map _ =
    ((k.centersLaw w).map (fun σ =>
      (History.staticObserver k w).run (D.schedule t) σ q
        (Control.initial (History.memory S)))).map _
  rw [map_comp]
  congr 1
  funext σ
  have hh := D.execute_eq_projection
    (fun _ cu => decide (cu.2 ∈ neighbors k.d (σ cu.1))) t q
    (Control.initial (History.memory S)) [] (D.invariant_initial t ht)
  rw [D.binaryRun_static k w t σ q _ _] at hh
  exact hh.symm

theorem gatedReportLaw_projection (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree Q A Z) (ht : t.NoRepeats) (q : ℕ) :
    D.gatedReportLaw k w hsmall t q =
      (canonicalObservationLaw k w hsmall (D.schedule t) q).map
        (D.decodeReport q t) := by
  classical
  unfold gatedReportLaw canonicalObservationLaw
  rw [map_comp]
  congr 1
  funext σ
  have hh := D.execute_eq_projection
    (fun h cu => TwoAnchor.answer (fun c => fillerNeighbors (σ c).1)
      (fun c => potentialSupport (σ c).2) h cu.1 cu.2) t q
    (Control.initial (History.memory S)) [] (D.invariant_initial t ht)
  rw [D.binaryRun_canonical] at hh
  exact hh.symm

theorem reports_close (D : Decoder Q A C S) (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (t : DecisionTree Q A Z) (ht : t.NoRepeats) (q : ℕ) :
    Law.Close (D.staticReportLaw k w t q)
      (D.gatedReportLaw k w (small_of_R k hR) t q)
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  rw [D.staticReportLaw_projection k w t ht q,
    D.gatedReportLaw_projection k w (small_of_R k hR) t ht q]
  exact (metric_canonical_comparison_sqrt k w hR hm (D.schedule t)
    (D.schedule_nonrepeating t) q).map (D.decodeReport q t)

end Decoder

end SteinerLowerBound.MetricComparison.Compiler

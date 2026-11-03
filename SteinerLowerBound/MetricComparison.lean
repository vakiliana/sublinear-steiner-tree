module

public import SteinerLowerBound.MetricComparison.Canonical
public import SteinerLowerBound.MetricComparison.Parameters
public import SteinerLowerBound.FiniteVariation

@[expose] public section

/-!
# Metric versus two-anchor observations

The comparison is conditional on arbitrary fixed weights and therefore also
holds after revealing or averaging them. `Control.Nonrepeating` expresses
fresh center--special queries; `none` is an uninformative deterministic step.
The history stores the first two positives and the preactivation negatives.

The proof compares the actual static and gated center laws directly. Before
two positives, the gated probabilities are filler probabilities. At two
positives, the history masses are respectively `β + a` and `β + a - a₀`;
their next-positive numerators agree. After three positives, the entire
conditional laws agree. This gives a pure square-root bound, stronger than
the square-root-plus-linear bound in the manuscript.
-/

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S Ω C : Type*} [Fintype S] [Fintype C]

theorem metric_gated_comparison_sqrt
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule) (q : ℕ) :
    Law.Close
      ((History.staticObserver k w).observationLaw schedule q)
      ((gatedObserver k w (small_of_R k hR)).observationLaw schedule q)
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  let memory := History.memory S
  let μ := History.staticObserver k w
  let ν := gatedObserver k w (small_of_R k hR)
  let ε := 16384 * scale k ^ 2 / ((Fintype.card S : ℝ) * k.R ^ 2)
  let Rel := fun x y : Control C (History S) => x = y ∧ x.Valid memory
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hstable : ∀ x y, Rel x y → ∀ b,
      Rel (Control.advance memory schedule x b) (Control.advance memory schedule y b) := by
    intro x y hxy b
    obtain ⟨rfl, hx⟩ := hxy
    exact ⟨rfl, Control.advance_valid memory schedule hs x hx b⟩
  have hlocal : ∀ x y, Rel x y →
      1 - Law.affinity (μ.globalKernel schedule x) (ν.globalKernel schedule y) ≤ ε := by
    intro x y hxy
    obtain ⟨rfl, hx⟩ := hxy
    cases he : schedule x with
    | none =>
      simp only [Observer.globalKernel, he, Law.affinity_self, sub_self]
      exact hε
    | some cu =>
      rcases cu with ⟨c, u⟩
      simp only [Observer.globalKernel, he]
      exact local_kernel_affinity k w (small_of_R k hR) hR hm (x.history c)
        (hx c) u (hs x hx c u he)
  have hi : Rel (Control.initial memory) (Control.initial memory) :=
    ⟨rfl, fun _ => memory.initial_valid⟩
  have hh := sequential_close (μ.globalKernel schedule) (Control.advance memory schedule)
    (ν.globalKernel schedule) (Control.advance memory schedule) Rel hstable hε hlocal q
      (Control.initial memory) (Control.initial memory) hi
  rw [← μ.observationLaw_eq_sequential schedule hs,
    ← ν.observationLaw_eq_sequential schedule hs] at hh
  apply hh.mono
  let t := (q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hL : 0 < scale k := scale_pos k
  have hsqrt : Real.sqrt (2 * (q : ℝ) * ε) ≤ 256 * scale k * Real.sqrt t := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ = 32768 * scale k ^ 2 * t := by dsimp only [ε, t]; ring
      _ ≤ 65536 * scale k ^ 2 * t := by
        nlinarith [mul_nonneg (sq_nonneg (scale k)) ht]
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt ht]; ring
  dsimp only [t] at hsqrt
  nlinarith

theorem metric_gated_comparison
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule) (q : ℕ) :
    Law.Close
      ((History.staticObserver k w).observationLaw schedule q)
      ((gatedObserver k w (small_of_R k hR)).observationLaw schedule q)
      (512 * scale k *
        (Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)) +
          (q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  apply (metric_gated_comparison_sqrt k w hR hm schedule hs q).mono
  have hL : 0 < scale k := scale_pos k
  have ht : 0 ≤ (q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2) := by positivity
  nlinarith

theorem metric_canonical_comparison_sqrt
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule) (q : ℕ) :
    Law.Close
      ((History.staticObserver k w).observationLaw schedule q)
      (canonicalObservationLaw k w (small_of_R k hR) schedule q)
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  rw [← observationLaw_eq_canonical k w (small_of_R k hR) schedule hs q]
  exact metric_gated_comparison_sqrt k w hR hm schedule hs q

noncomputable def transcript
    (schedule : Control C (History S) → Option (C × S)) :
    (q : ℕ) → Control C (History S) → Answers q →
      Fin q → Option ((C × S) × Bool)
  | 0, _, _ => Fin.elim0
  | q + 1, x, a =>
      Fin.cases ((schedule x).map (fun v => (v, a.1)))
        (transcript schedule q (Control.advance (History.memory S) schedule x a.1) a.2)

theorem metric_canonical_transcript_comparison
    (k : Setup S Ω) (w : S → Ω)
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (schedule : Control C (History S) → Option (C × S))
    (hs : Control.Nonrepeating (History.memory S) schedule) (q : ℕ) :
    Law.Close
      (((History.staticObserver k w).observationLaw schedule q).map
        (transcript schedule q (Control.initial (History.memory S))))
      ((canonicalObservationLaw k w (small_of_R k hR) schedule q).map
        (transcript schedule q (Control.initial (History.memory S))))
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) :=
  (metric_canonical_comparison_sqrt k w hR hm schedule hs q).map _

theorem metric_gated_comparison_revealed [Fintype Ω]
    (k : Setup S Ω) (ρ : Law (S → Ω))
    (hR : 16 * scale k ≤ k.R) (hm : 16 ≤ Fintype.card S)
    (schedule : (S → Ω) → Control C (History S) → Option (C × S))
    (hs : ∀ w, Control.Nonrepeating (History.memory S) (schedule w)) (q : ℕ) :
    Law.Close
      (ρ.bind (fun w => ((History.staticObserver k w).observationLaw (schedule w) q).map
        (fun a => (w, a))))
      (ρ.bind (fun w => ((gatedObserver k w (small_of_R k hR)).observationLaw (schedule w) q).map
        (fun a => (w, a))))
      (512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2))) := by
  have hh := Law.Close.bind_same ρ
    (fun w => ((History.staticObserver k w).observationLaw (schedule w) q).map (fun a => (w, a)))
    (fun w => ((gatedObserver k w (small_of_R k hR)).observationLaw (schedule w) q).map
      (fun a => (w, a)))
    (fun _ => 512 * scale k * Real.sqrt ((q : ℝ) / ((Fintype.card S : ℝ) * k.R ^ 2)))
    (fun w => (metric_gated_comparison_sqrt k w hR hm (schedule w) (hs w) q).map
      (fun a => (w, a)))
  simpa only [Law.expect_const] using hh

end SteinerLowerBound.MetricComparison

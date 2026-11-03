module

public import SteinerUpperBound.Covers.Actual
public import SteinerUpperBound.Covers.GlobalCap
public import SteinerUpperBound.Covers.ProposalCap
public import SteinerUpperBound.Covers.Scales

@[expose] public section

/-!
# Exact integration interfaces

The declarations below are checked restatements of existing theorems, collected
without changing their implementations.

Original declaration locations:
* `Covers.actual_all_scales`: `SteinerUpperBound.Covers.Actual`.
* `Covers.Factory.global_capped_law_close`: `SteinerUpperBound.Covers.GlobalCap`.
* `Covers.Factory.cached_factory_cap_tail`: `SteinerUpperBound.Covers.Interpreter`.
  This module also exports the spelling alias `Factory.capped_factory_cap_tail`.
* `Covers.Rejection.capped_sampler_and_calibration`:
  `SteinerUpperBound.Covers.ProposalCap`.

The namespace `Covers.Interfaces` exposes all four full signatures in this file.
For the cover factory instantiate `U = Terminal I`, `Q = S × Terminal I`,
`target q = q.2`, and `rel q = near I (r q.1)`. Initial cache entries for
designated retained terminals are `some true`; all others are `none`. The
global-cap event counts *new* positive disclosures, excluding that initial cache.

The sampler uses a fixed membership oracle `b : U → Bool`; its code does not
receive the nonemptiness proof, the retained cardinality, or a sampler-law
certificate. The calibration estimates use `proposals`, the actual uncached
proposal counter, which equals the executed stopping count off the cap event.
-/

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical
open FiniteSampling RetentionTree

/-- Spelling alias for `cached_factory_cap_tail`; both names remain public. -/
theorem capped_factory_cap_tail {Q U R : Type*} [Fintype Q] [Fintype U] [Nonempty U]
    (dummy : U) (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) (a : ℝ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (tape (Law.uniform U) B).prob
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ a} ≤
      Real.exp (a - (B : ℝ) / (2 * Fintype.card U)) :=
  cached_factory_cap_tail dummy target rel caps trials t cache B a

end SteinerUpperBound.Covers.Factory

namespace SteinerUpperBound.Covers.Interfaces

open SteinerLowerBound
open scoped Classical BigOperators
open Factory FiniteSampling RetentionTree Rejection

noncomputable local instance {V : Type*} (I : Instance V) : DecidableEq (Terminal I) :=
  Classical.decEq _

theorem actual_all_scales {V S : Type*} [Fintype V] [Fintype S] [Nonempty S]
    (I : Instance V) (r : S → ℝ) (hr : ∀ i, 0 < r i) (root : Terminal I)
    (β : ℝ) (hβ : 0 < β) :
    (Law.pi (fun i : S => actualBits I (r i) root
      (privateDrawBudget I.terminals.card (Fintype.card S) β)
      (retentionBudget I.terminals.card (Fintype.card S) β))).prob
      {b | ∃ i : S, ¬ IsCover I ((hopCount I.terminals.card : ℝ) * r i) (b i) ∨
        Real.exp 1 * (1 + (retentionBudget I.terminals.card (Fintype.card S) β : ℝ) *
          (1 + 2 * I.mst / r i)) + sizeSlack (Fintype.card S) β ≤
            ((CategoricalCoupling.selected (b i)).card : ℝ)} ≤ β :=
  SteinerUpperBound.Covers.actual_all_scales I r hr root β hβ

theorem global_capped_law_close {Q U R : Type*}
    [Fintype Q] [Fintype U] [Nonempty U] [Fintype R]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    Law.Close
      ((tape (Law.uniform U) B).map (fun w => output (run target B s w)))
      ((Law.pi (cachedKernel cache (coordinateLaw target rel caps trials))).map
        (fun b => some (t.output b)))
      ((tape (Law.uniform U) B).prob {w | Pending (run target B s w)}) :=
  Factory.global_capped_law_close target rel caps trials t cache B

theorem capped_factory_cap_tail {Q U R : Type*} [Fintype Q] [Fintype U] [Nonempty U]
    (dummy : U) (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) (a : ℝ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (tape (Law.uniform U) B).prob
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ a} ≤
      Real.exp (a - (B : ℝ) / (2 * Fintype.card U)) :=
  Factory.capped_factory_cap_tail dummy target rel caps trials t cache B a

theorem capped_sampler_and_calibration {U : Type*} [Fintype U] [Nonempty U]
    (b : U → Bool) (hb : (retained b).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := calibrationSamples (β / 2) ξ
    let C := proposalRowCap (Fintype.card U) s (β / 2) ξ
    let B := proposalBudget (Fintype.card U) s β
    (poolLaw C s).prob
      {rows | B < proposals b C s rows ∨
        ¬ Successful b C s rows ∨ ¬ Calibrated b C s ξ rows} ≤ β :=
  Rejection.capped_sampler_and_calibration b hb β ξ hβ hβ1 hξ hξ1

end SteinerUpperBound.Covers.Interfaces

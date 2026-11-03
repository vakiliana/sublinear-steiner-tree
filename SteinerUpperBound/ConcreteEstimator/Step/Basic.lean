module

public import SteinerUpperBound.ConcreteEstimator
public import SteinerUpperBound.EstimatorFrontend.Analysis.World

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator.Step

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ} {tables : Tables}

noncomputable def raw (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (p : PublicParameters) (inverse : Vector (Fin (k + 1)) n) (tables : Tables)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k)) :
    Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate tables k) (LargeCoverProgram.Answer (RuntimeWorld.Coordinate tables k) n) :=
  SavingEstimator.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
    (tables.coarse.scale i.val) p cache

def Performance (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ) (δ : ℝ) : Prop :=
  ∀ i cache, Cache.Correct bits cache →
    ∃ Good : ((raw label root p inverse tables i cache).compile I.weight).Seed → Prop,
      ((raw label root p inverse tables i cache).compile I.weight).law.prob {s | ¬ Good s} ≤ δ ∧
      ((raw label root p inverse tables i cache).compile I.weight).law.expect
        (fun s => if Good s then
          (((((raw label root p inverse tables i cache).compile I.weight).tree s).output bits).work : ℝ) else 0) ≤ AW ∧
      ((raw label root p inverse tables i cache).compile I.weight).law.expect
        (fun s => if Good s then
          (((((raw label root p inverse tables i cache).compile I.weight).tree s).output bits).positiveReplies : ℝ)
          else 0) ≤ AP

noncomputable def error (n : ℕ) (δ : ℝ) : ℝ :=
  4 * beta n + δ + 5 / (EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1))

theorem error_nonneg (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) : 0 ≤ error n δ := by
  have hb := (beta_bounds n).1.le
  unfold error
  positivity

theorem value (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k))
    (F : Option (ℝ × Cache (RuntimeWorld.Coordinate tables k)) → ℝ) :
    (ConcreteEstimator.step label root p inverse tables AW AP i cache).evaluate m bits (fun o => F o.value) =
      (SavingEstimator.Clocked.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
        (tables.coarse.scale i.val) p AW AP cache).evaluate m bits (fun o => F o.value) := by
  rw [ConcreteEstimator.step, Covers.OracleProgram.Mean.evaluate_bind_value, BandEstimator.scale_evaluates]
  rfl

theorem valueProbability (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k))
    (P : Option (ℝ × Cache (RuntimeWorld.Coordinate tables k)) → Prop) :
    Code.valueProbability m bits (ConcreteEstimator.step label root p inverse tables AW AP i cache) P =
      Code.valueProbability m bits
        (SavingEstimator.Clocked.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
          (tables.coarse.scale i.val) p AW AP cache) P :=
  value m bits label root p inverse AW AP i cache (fun r => if P r then 1 else 0)

theorem retained_count (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (hT : Finset.univ.image label.get = I.terminals)
    (inverse : Vector (Fin (k + 1)) n) (i : EstimatorFrontend.Index tables) :
    SavingEstimator.retainedCount bits label (RuntimeWorld.coarseKey tables inverse i.val) =
      (EstimatorFrontend.Analysis.coarseRetained I tables inverse bits i).card := by
  have hlist := (PublicTerminals.toList_toFinset label).trans hT
  have h := LargeCoverProgram.labelCount_eq_points I bits label
    (RuntimeWorld.coarseKey tables inverse i.val) hlist (PublicTerminals.toList_nodup label hinj)
  rw [hlist] at h
  exact h

theorem retained_saving (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (inverse : Vector (Fin (k + 1)) n) (i : EstimatorFrontend.Index tables) :
    SavingEstimator.saving I bits (RuntimeWorld.coarseKey tables inverse i.val) (tables.coarse.scale i.val) =
      Covers.Geometry.savingOn I (EstimatorFrontend.Analysis.coarseRetained I tables inverse bits i)
        (tables.coarse.scale i.val) (5 * tables.coarse.scale i.val / 8) := by
  have hN :
      I.terminals.filter (fun v => bits (RuntimeWorld.coarseKey tables inverse i.val v) = true) =
        EstimatorFrontend.Analysis.coarseRetained I tables inverse bits i := by
    ext v
    simp only [EstimatorFrontend.Analysis.coarseRetained, ComponentExplore.retained, Finset.mem_filter]
  unfold SavingEstimator.saving
  rw [hN]

theorem goodReply_bounds (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (hT : Finset.univ.image label.get = I.terminals)
    (inverse : Vector (Fin (k + 1)) n) (i : EstimatorFrontend.Index tables)
    (r : Option (ℝ × Cache (RuntimeWorld.Coordinate tables k)))
    (h : SavingEstimator.Clocked.GoodReply I bits label (RuntimeWorld.coarseKey tables inverse i.val)
      (tables.coarse.scale i.val) r) :
    Code.SomeGood (fun zc => Cache.Correct bits zc.2 ∧
      EstimatorFrontend.Analysis.SavingBounds I tables inverse bits i zc.1) r := by
  obtain ⟨Z, c, hv, hc, h₀, h₁, hl⟩ := h
  rw [retained_saving] at h₁ hl
  rw [retained_count I bits label hinj hT inverse i] at hl
  exact ⟨(Z, c), hv, hc, h₀, h₁, hl⟩

end SteinerUpperBound.ConcreteEstimator.Step

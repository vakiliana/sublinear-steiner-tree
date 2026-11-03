module

public import SteinerUpperBound.ConcreteEstimator.Step.Basic
public import SteinerUpperBound.EstimatorFrontend.Resources

@[expose] public section

namespace SteinerUpperBound.ConcreteEstimator.Step

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Matching.Padded
open scoped Classical

variable {n k : ℕ} {tables : Tables}

def workBound (n : ℕ) (p : PublicParameters) (AW AP : ℕ) : ℕ :=
  (SavingEstimator.Clocked.budget p AW AP).workBudget + 25 + 2 * heightBudget n + 3

def positiveBound (p : PublicParameters) (AW AP : ℕ) : ℕ :=
  (SavingEstimator.Clocked.budget p AW AP).disclosureBudget + 1

theorem workBound_public (n count AW AP : ℕ) :
    workBound n (parameters n count) AW AP =
      (EstimatorClocks.stage n AW AP).workBudget + 25 + 2 * heightBudget n + 3 := rfl

theorem positiveBound_public (n count AW AP : ℕ) :
    positiveBound (parameters n count) AW AP = (EstimatorClocks.stage n AW AP).disclosureBudget + 1 := rfl

theorem work (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k)) :
    (ConcreteEstimator.step label root p inverse tables AW AP i cache).evaluate m bits (fun o => (o.work : ℝ)) =
      ((2 * i.val + 3 : ℕ) : ℝ) +
        (SavingEstimator.Clocked.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
          (tables.coarse.scale i.val) p AW AP cache).evaluate m bits (fun o => (o.work : ℝ)) := by
  rw [ConcreteEstimator.step, Code.evaluate_work_bind, BandEstimator.scale_evaluates]
  rfl

theorem positive (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k)) :
    (ConcreteEstimator.step label root p inverse tables AW AP i cache).evaluate m bits
        (fun o => (o.positiveReplies : ℝ)) =
      (SavingEstimator.Clocked.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
        (tables.coarse.scale i.val) p AW AP cache).evaluate m bits (fun o => (o.positiveReplies : ℝ)) := by
  rw [ConcreteEstimator.step, Code.evaluate_positive_bind, BandEstimator.scale_evaluates]
  simp only [BandEstimator.scaleResult, Nat.cast_zero, zero_add]

theorem expected (m : Sym2 (Fin n) → ℝ) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (hheight : tables.coarse.intervals + 1 ≤ heightBudget n)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k)) :
    (ConcreteEstimator.step label root p inverse tables AW AP i cache).evaluate m bits (fun o => (o.work : ℝ)) ≤
        workBound n p AW AP ∧
      (ConcreteEstimator.step label root p inverse tables AW AP i cache).evaluate m bits
        (fun o => (o.positiveReplies : ℝ)) ≤ positiveBound p AW AP := by
  have h := SavingEstimator.Clocked.fromParameters_expected m bits label root
    (RuntimeWorld.coarseKey tables inverse i.val) (tables.coarse.scale i.val) p AW AP cache
  have hi : 2 * i.val + 3 ≤ 2 * heightBudget n + 3 := by have hh := i.isLt; omega
  have hi' : ((2 * i.val + 3 : ℕ) : ℝ) ≤ ((2 * heightBudget n + 3 : ℕ) : ℝ) := by exact_mod_cast hi
  push_cast at hi'
  rw [work, positive]
  constructor
  · unfold workBound
    push_cast
    linarith [h.1]
  · simpa only [positiveBound, Nat.cast_add, Nat.cast_one] using h.2

theorem cache_ensures (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (i : EstimatorFrontend.Index tables) (cache : Cache (RuntimeWorld.Coordinate tables k))
    (hc : Cache.Correct bits cache) :
    Causal.Ensures I.weight bits (ConcreteEstimator.step label root p inverse tables AW AP i cache)
      (EstimatorFrontend.Resources.CacheSafe bits) := by
  apply LargeCoverProgram.Support.ensures_bind_evaluates I.weight bits
    (BandEstimator.scaleProgram tables.coarse i.val) _ _ (BandEstimator.scale_evaluates I.weight bits _ _)
  apply LargeCoverProgram.Support.ensures_mono I.weight bits _ (SavingEstimator.Clocked.CacheSafe bits) _
    (SavingEstimator.Clocked.fromParameters_cache_ensures I bits label root
      (RuntimeWorld.coarseKey tables inverse i.val) (tables.coarse.scale i.val) p AW AP
      ((PublicTerminals.toList_toFinset label).trans hT) (PublicTerminals.toList_nodup label hinj) cache hc)
  intro r hr zc he
  subst r
  exact hr

theorem saving_resources (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hheight : tables.coarse.intervals + 1 ≤ heightBudget n) :
    EstimatorFrontend.Resources.SavingResources I bits (ConcreteEstimator.step label root p inverse tables AW AP)
      (workBound n p AW AP) (positiveBound p AW AP) where
  work i cache _ := (expected I.weight bits label root p inverse AW AP hheight i cache).1
  positive i cache _ := (expected I.weight bits label root p inverse AW AP hheight i cache).2
  cache i cache hc := cache_ensures I bits label root p inverse AW AP hinj hT i cache hc

end SteinerUpperBound.ConcreteEstimator.Step

module

public import SteinerUpperBound.ConcreteEstimator.Step.Basic

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.ConcreteEstimator.Step

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ} {tables : Tables}

theorem saving_contract (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ) (δ : ℝ)
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hp : p = parameters n (k + 1))
    (hroot : ∀ i : EstimatorFrontend.Index tables,
      bits (RuntimeWorld.coarseKey tables inverse i.val (label.get root)) = true)
    (performance : Performance I bits label root p inverse AW AP δ) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root p inverse tables AW AP) (error n δ) := by
  subst p
  intro i cache hc
  obtain ⟨Good, hbad, hwork, hpositive⟩ := performance i cache hc
  have hlist := (PublicTerminals.toList_toFinset label).trans hT
  have hs := SavingEstimator.Clocked.fromParameters_success_byHeight I bits label root
    (RuntimeWorld.coarseKey tables inverse i.val) (tables.coarse.scale i.val)
    hlist (PublicTerminals.toList_nodup label hinj) AW AP cache hc (hroot i) Good δ hbad hwork hpositive
  have hm := BandEstimator.valueProbability_mono I.weight bits
    (SavingEstimator.Clocked.fromParameters label root (RuntimeWorld.coarseKey tables inverse i.val)
      (tables.coarse.scale i.val) (parameters n (k + 1)) AW AP cache)
    (SavingEstimator.Clocked.GoodReply I bits label (RuntimeWorld.coarseKey tables inverse i.val)
      (tables.coarse.scale i.val))
    (Code.SomeGood (fun zc => Cache.Correct bits zc.2 ∧
      EstimatorFrontend.Analysis.SavingBounds I tables inverse bits i zc.1))
    (goodReply_bounds I bits label hinj hT inverse i)
  rw [valueProbability]
  calc
    _ = 1 - 4 * beta n - δ -
        5 / (EstimatorClocks.amplification * ((heightBudget n : ℝ) + 1)) := by
      unfold error
      ring
    _ ≤ _ := hs
    _ ≤ _ := hm

theorem saving_contract_of_geometry (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate tables k → Bool)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (p : PublicParameters)
    (inverse : Vector (Fin (k + 1)) n) (AW AP : ℕ) (δ R : ℝ)
    (G : EstimatorFrontend.Analysis.Geometry I label root tables inverse bits R)
    (hp : p = parameters n (k + 1))
    (performance : Performance I bits label root p inverse AW AP δ) :
    EstimatorFrontend.Analysis.SavingContract I tables inverse bits
      (ConcreteEstimator.step label root p inverse tables AW AP) (error n δ) := by
  have hT : Finset.univ.image label.get = I.terminals := by
    ext x
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using Finset.ext_iff.mp G.terminals x
  exact saving_contract I bits label root p inverse AW AP δ G.injective hT hp G.coarse_root performance

end SteinerUpperBound.ConcreteEstimator.Step

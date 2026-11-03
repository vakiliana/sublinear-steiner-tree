module

public import SteinerLowerBound.MetricComparison.PublicLaw
public import SteinerLowerBound.Screening.VisibleLaw

@[expose] public section

/-!
# Exact agreement of the two gated source laws

The public comparison draws independent `(filler, mark)` records by center.
The screening experiment instead draws all fillers, then all conditional
marks, and finally the terminal permutation. These are exactly the same law
for every finite observation of a fixed public algorithm's full run.
-/

namespace SteinerLowerBound.MetricComparison.PublicGatedLaw

open scoped BigOperators Classical
open HardDistribution
open Screening (Terminal Reply)

theorem step_eq_bind_map {A B : Type*} [Fintype A] [Fintype B]
    (μ : Law A) (k : A → Law B) :
    Law.step μ k = μ.bind (fun a => (k a).map (fun b => (a, b))) := by
  apply LawOperations.ext_prob
  intro E
  rw [Law.prob_step, Law.prob_bind]
  apply congrArg (Law.expect μ)
  funext a
  rw [Law.prob_map]
  rfl

theorem step_bind {A B Z : Type*} [Fintype A] [Fintype B] [Fintype Z]
    (μ : Law A) (k : A → Law B) (f : A × B → Law Z) :
    (Law.step μ k).bind f = μ.bind (fun a => (k a).bind (fun b => f (a, b))) := by
  apply LawOperations.ext_prob
  intro E
  simp only [Law.prob_bind, PublicLaw.expect_step]

theorem uniform_bind_fintype {A Z : Type*} [Nonempty A] [Fintype Z]
    (i j : Fintype A) (f : A → Law Z) :
    @Law.bind A Z i inferInstance (@Law.uniform A i inferInstance) f =
      @Law.bind A Z j inferInstance (@Law.uniform A j inferInstance) f := by
  have he : i = j := Subsingleton.elim _ _
  cases he
  rfl

variable {S G I C W R Z : Type*}
variable [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W] [Fintype Z]

theorem gatedCentersLaw_split (k : Setup S W) (w : S → W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    gatedCentersLaw (C := C) k w hsmall =
      (Screening.Experiment.fillerFamilyLaw (C := C) k).bind (fun F =>
        (Law.pi (fun c => markLaw k w hsmall (F c))).map
          (fun marks c => (F c, marks c))) := by
  unfold gatedCentersLaw gatedCenterLaw
  simp_rw [step_eq_bind_map]
  rw [LawOperations.pi_bind]
  apply congrArg (Law.bind (Screening.Experiment.fillerFamilyLaw (C := C) k))
  funext F
  exact (LawOperations.pi_map (fun c => markLaw k w hsmall (F c))
    (fun c H => (F c, H))).symm

noncomputable def runLaw (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Public.Queries S G I C) Reply R)
    (f : R × List (Public.Queries S G I C × Reply) → Z) : Law Z :=
  (Public.publicDataLaw (G := G) (I := I) μ).bind (fun data =>
    (gatedCentersLaw (C := C) k data.1 hsmall).map (fun σ =>
      f (Public.gatedRun data.2 (fun c => fillerNeighbors (σ c).1)
        (fun c => potentialSupport (σ c).2) t [])))

theorem runLaw_disintegrate (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Public.Queries S G I C) Reply R)
    (f : R × List (Public.Queries S G I C × Reply) → Z) :
    runLaw k μ hsmall t f =
      (μ.iid S).bind (fun w =>
        (Law.uniform (Equiv.Perm (Terminal S G I))).bind (fun π =>
          (Screening.Experiment.fillerFamilyLaw (C := C) k).bind (fun F =>
            (Law.pi (fun c => markLaw k w hsmall (F c))).map (fun marks =>
              f (Public.gatedRun π (fun c => fillerNeighbors (F c))
                (fun c => potentialSupport (marks c)) t []))))) := by
  unfold runLaw Public.publicDataLaw
  rw [step_bind]
  apply congrArg (Law.bind (μ.iid S))
  funext w
  apply congrArg (Law.bind (Law.uniform (Equiv.Perm (Terminal S G I))))
  funext π
  rw [gatedCentersLaw_split, LawOperations.map_bind]
  apply congrArg (Law.bind (Screening.Experiment.fillerFamilyLaw (C := C) k))
  funext F
  rw [LawOperations.map_comp]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

theorem runLaw_eq_experiment (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Public.Queries S G I C) Reply R)
    (f : R × List (Public.Queries S G I C × Reply) → Z) :
    runLaw k μ hsmall t f =
      (Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall).map
        (fun ω => f (Public.gatedRun ω.2
          (fun c => fillerNeighbors (ω.1.1.2 c))
          (fun c => potentialSupport (ω.1.2 c)) t [])) := by
  classical
  let πLaw := Law.uniform (Equiv.Perm (Terminal S G I))
  let FLaw := Screening.Experiment.fillerFamilyLaw (C := C) k
  let out := fun (w : S → W) (F : C → Filler S) (π : Equiv.Perm (Terminal S G I)) =>
    (Law.pi (fun c => markLaw k w hsmall (F c))).map (fun marks =>
      f (Public.gatedRun π (fun c => fillerNeighbors (F c))
        (fun c => potentialSupport (marks c)) t []))
  calc
    _ = (μ.iid S).bind (fun w => πLaw.bind (fun π => FLaw.bind (fun F => out w F π))) := by
      rw [runLaw_disintegrate]
      apply congrArg (Law.bind (μ.iid S))
      funext w
      exact uniform_bind_fintype _ _ _
    _ = πLaw.bind (fun π => (μ.iid S).bind (fun w => FLaw.bind (fun F => out w F π))) :=
      LawOperations.bind_comm (μ.iid S) πLaw _
    _ = πLaw.bind (fun π => FLaw.bind (fun F => (μ.iid S).bind (fun w => out w F π))) := by
      apply congrArg (Law.bind πLaw)
      funext π
      exact LawOperations.bind_comm (μ.iid S) FLaw (fun w F => out w F π)
    _ = _ := by
      rw [Screening.Experiment.law_map_disintegrate, Screening.Experiment.commonLaw_bind]

theorem gatedOutputLaw_eq_experiment [Fintype R] (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (t : DecisionTree (Public.Queries S G I C) Reply R) :
    Public.gatedOutputLaw k μ hsmall t =
      (Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall).map
        (fun ω => (Public.gatedRun ω.2
          (fun c => fillerNeighbors (ω.1.1.2 c))
          (fun c => potentialSupport (ω.1.2 c)) t []).1) := by
  exact runLaw_eq_experiment k μ hsmall t Prod.fst

end SteinerLowerBound.MetricComparison.PublicGatedLaw

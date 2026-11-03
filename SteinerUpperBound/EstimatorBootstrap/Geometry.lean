module

public import SteinerUpperBound.EstimatorBootstrap
public import SteinerUpperBound.EstimatorFrontend.Analysis

@[expose] public section

noncomputable section

namespace SteinerUpperBound.EstimatorBootstrap

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ}

noncomputable local instance geometryVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance geometryLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance geometryCoordinateDecEq (t : Tables) : DecidableEq (RuntimeWorld.Coordinate t k) :=
  Classical.decEq _

def PhaseGood (I : Instance (Fin n)) (R : ℝ) (hR : 0 < R) : Set (Fin FinitePhase.count) :=
  {phase | Covers.Geometry.BandCompleteness.weightedPhaseBad I
    ((coarseGrid (k + 1) (by omega) R hR phase).toStructural rfl)
    (EstimatorAnalysis.radii ((coarseGrid (k + 1) (by omega) R hR phase).toStructural rfl)) ≤
      I.mst / 200}

theorem phase_failure (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hT : Finset.univ.image label.get = I.terminals) (root : Fin (k + 1))
    (R : ℝ) (hR : 0 < R) (hRL : R ≤ I.mst) :
    FinitePhase.law.prob (PhaseGood (k := k) I R hR)ᶜ ≤ 1 / 1000 := by
  have hnonempty : I.terminals.Nonempty :=
    ⟨label.get root, hT ▸ Finset.mem_image.mpr ⟨root, Finset.mem_univ _, rfl⟩⟩
  exact RuntimeGeometry.phase_failure I (k + 1) (by omega) R hR hnonempty hRL

theorem generated_geometry (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (hk : 2 ≤ I.terminals.card) (root : Fin (k + 1)) (R : ℝ) (hR : 0 < R)
    (hRL : R ≤ I.mst) (hmin : floorScale (k + 1) R ≤ Structural.minimumTerminalDistance I)
    (hdiam : TreeGeometry.terminalDiameter I ≤ 2 * R)
    (phase : Fin FinitePhase.count) (hphase : phase ∈ PhaseGood (k := k) I R hR) :
    let t := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
    ∀ bits, 0 < (Covers.OracleProgram.bits
        (RuntimeWorld.configuration (parameters n (k + 1)) label t) I.weight
        (LabelledFactory.initialCache root)).mass bits →
      RuntimeWorld.Good I label t bits →
      EstimatorFrontend.Analysis.Geometry I label root t
        (PublicTerminals.inverseResult label root).value bits R := by
  intro t bits hb hg
  have hcount : 2 ≤ k + 1 := by rw [← LabelledCovers.terminal_card I label hinj hT]; exact hk
  have hlength := RuntimeGrids.length_bound n (k + 1) (by omega)
    (PublicTerminals.length_le label hinj) R hR phase
  have hleft := PublicTerminals.inverse_left label hinj root
  have hc := coarseGrid_endpoints (k + 1) hcount R hR phase
  have hf := fineGrid_endpoints (k + 1) hcount R hR
  refine
    { injective := hinj
      terminals := hT
      inverse_left := hleft
      world := hg
      coarse_root := fun i =>
        RuntimeWorld.coarse_root _ label t _ hleft root I.weight bits hb i.val
      fine_root := fun i _ =>
        RuntimeWorld.fine_root _ label t _ hleft root I.weight bits hb i
      coarse_ratio := rfl
      fine_ratio := rfl
      coarse_height := ?_
      fine_height := ?_
      radius_nonneg := hR.le
      radius_le := hRL
      coarse_last := hc.2.2
      fine_last := hf.2.2
      fine_first := ?_
      fine_diameter := ?_
      covers := RuntimeGeometry.coarse_covers I (k + 1) hcount R hR phase hmin hdiam
      phase := hphase }
  · change t.coarse.intervals + 1 ≤ _
    change t.coarse.intervals + t.fine.intervals + 2 ≤ _ at hlength
    omega
  · change t.fine.intervals ≤ _
    change t.coarse.intervals + t.fine.intervals + 2 ≤ _ at hlength
    omega
  · intro x hx y hy hxy
    exact RuntimeGeometry.fine_first I (k + 1) hcount R hR
      (fun x hx y hy hxy => hmin.trans (Structural.minimumTerminalDistance_le I hx hy hxy)) hx hy hxy
  · intro x hx y hy
    exact RuntimeGeometry.fine_last I (k + 1) (by omega) R hR hcount hdiam hx hy

end SteinerUpperBound.EstimatorBootstrap

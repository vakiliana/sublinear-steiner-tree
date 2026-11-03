module

public import SteinerLowerBound.Simulation.Probability
public import SteinerLowerBound.Screening.VisibleTail

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerLowerBound.Simulation.Public

open scoped Classical
open HardDistribution
open MetricComparison.Public

variable {S G I C W Z V : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem tree_valid_real (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    Protocol.Valid (VisibleMass.region d F) (fun Q => (Q.card : ℝ) ≤ 2 * (R : ℝ)) ∅
      (tree π d F D t R algorithm) := by
  apply valid_mono_cap _ _ _ _ _ (tree_valid π d F D t R algorithm)
  intro Q hQ
  exact_mod_cast hQ

theorem tree_overflow_fraction (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (hd : 0 < d)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) (o : Candidate S C d → Bool)
    (hstop : ((tree π d F D t R algorithm).output o).state.stop = some .closure) :
    (R : ℝ) / d < (retainedRead (tree π d F D t R algorithm) o : ℝ) := by
  have h := tree_overflow_retained π d F D t R algorithm o hstop
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  apply (div_lt_iff₀ hd').mpr
  rw [mul_comm]
  exact_mod_cast h

theorem tree_overflow_proposals (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (o : Candidate S C d → Option Bool)
    (hstop : ((RetainedProtocol.lift (tree π d F D t R algorithm)).output o).state.stop =
      some .closure) :
    R < d * ProposalProtocol.proposalsRead (RetainedProtocol.lift (tree π d F D t R algorithm)) o := by
  rw [output_lift] at hstop
  exact (tree_overflow_retained π d F D t R algorithm _ hstop).trans_le
    (Nat.mul_le_mul_left d (retainedRead_le_proposals _ o))

variable [Fintype W]

noncomputable def closureError (k : Setup S W) : ℝ :=
  Screening.Experiment.categoricalError k +
    k.d * Screening.Experiment.visibleLoad k / k.R + 3 / (Fintype.card S : ℝ) ^ 3

theorem experiment_closure_overflow_probability (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (hR : k.R = Fintype.card I)
    (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    (Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall).prob {ω |
      ((tree ω.2 k.d ω.1.1.2 (Fintype.card G / 16)
        ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm).output
          (bits k.d ω.1.2)).state.stop = some .closure} ≤ closureError k := by
  let t := fun (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S) =>
    tree π k.d F (Fintype.card G / 16)
      ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm
  have ht : ∀ π F, Protocol.Valid (VisibleMass.region k.d F)
      (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅ (t π F) := by
    intro π F
    rw [hR]
    exact tree_valid_real π k.d F (Fintype.card G / 16)
      ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm
  apply ((Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall).prob_mono ?_).trans
    (Screening.Experiment.visible_retained_product_tail k μ hM hsmall hC t ht)
  intro ω hω
  have h := tree_overflow_retained ω.2 k.d ω.1.1.2 _ _ _ algorithm (bits k.d ω.1.2) hω
  change k.R < k.d * (retainedRead (t ω.2 ω.1.1.2)
    (Screening.Experiment.visibleBits k ω.1.2) : ℝ)
  rw [hR, ← bits_eq_visibleBits]
  exact_mod_cast h

noncomputable def screeningError (k : Setup S W) (q : ℕ) : ℝ :=
  Screening.screeningConstant k.d (anchorConstant k.d k.H0 k.M)
    (Screening.Experiment.vertexConstant k.d k.H0 k.M) *
      ((q : ℝ) / (Fintype.card G * (Fintype.card G * Fintype.card I)) +
        (q : ℝ) / ((Fintype.card G * Fintype.card I) * Fintype.card I))

variable [Fintype V]

theorem experiment_projection_close_bound (k : Setup S W) (μ : Law W)
    (hM : 0 < k.M) (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (hhalf : anchorConstant k.d k.H0 k.M / k.R ≤ 1 / 2)
    (hm : Fintype.card S = k.d * Fintype.card G)
    (hA : 64 ≤ Fintype.card G) (hR : 0 < Fintype.card I)
    (hRsize : k.R = Fintype.card I)
    (hC : (Fintype.card C : ℝ) = (Fintype.card S : ℝ) * k.R)
    (q : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (hq : Screening.DecisionTree.Bounded algorithm q)
    (f : Z × List (Queries S G I C × Reply) → V) :
    Law.Close
      ((Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall).map (fun ω =>
        f (gatedRun ω.2 (fun c => fillerNeighbors (ω.1.1.2 c))
          (fun c => (ω.1.2 c).elim ∅ Subtype.val) algorithm [])))
      (Screening.Experiment.visibleOutputLaw k μ hsmall (experimentTree k algorithm f))
      (screeningError (G := G) (I := I) k q + closureError k) := by
  apply (experiment_projection_close k μ hsmall algorithm f).mono
  exact add_le_add
    (Screening.Experiment.screening_two_anchor k μ hsmall hhalf hm hA hR hRsize q
      (mapQuestions orient algorithm) (mapQuestions_bounded orient algorithm q hq))
    (experiment_closure_overflow_probability k μ hM hsmall hC hRsize algorithm)

end SteinerLowerBound.Simulation.Public

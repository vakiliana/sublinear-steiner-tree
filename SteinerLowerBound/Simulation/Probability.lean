module

public import SteinerLowerBound.Simulation.Projection
public import SteinerLowerBound.Screening.VisibleLaw

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical

theorem onlineRun_record {Ω Q A Z : Type*} (answer : Ω → List Q → Q → A)
    (ω : Ω) (algorithm : DecisionTree Q A Z) (r : Screening.Record Q A) :
    Screening.DecisionTree.run answer ω r algorithm =
      r ++ (MetricComparison.Public.onlineRun (answer ω) algorithm (Screening.questions r)).2 := by
  induction algorithm generalizing r with
  | leaf => simp [Screening.DecisionTree.run, MetricComparison.Public.onlineRun]
  | query q next ih =>
      simp only [Screening.DecisionTree.run]
      rw [ih]
      simp only [MetricComparison.Public.onlineRun, Screening.questions,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.nil_append]

namespace Public

open HardDistribution
open MetricComparison.Public

variable {S G I C W Z V : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype W]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem experiment_internalFillers (b : Screening.Experiment.Base S C W) :
    Screening.Experiment.fillers (G := G) (I := I) b = internalFillers b.2 := rfl

theorem experiment_internalStars (d : ℕ) (H : C → Option (Subsets S d)) :
    Screening.starSupports (Screening.Experiment.starSupport (G := G) (I := I) d) H =
      internalStars d H := by
  funext c
  cases he : H c <;>
    simp [Screening.starSupports, Screening.Experiment.starSupport,
      Screening.liftSpecial, internalStars, internalSupport, he]

theorem experiment_answer (k : Setup S W)
    (ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k) :
    Screening.Experiment.gatedAnswer k ω = actualAnswer ω.2 k.d ω.1.1.2 ω.1.2 := by
  unfold Screening.Experiment.gatedAnswer actualAnswer
  rw [experiment_internalFillers, experiment_internalStars]

theorem experiment_anchored (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k)
    (hpos : 0 < (Screening.Experiment.law k μ hsmall).mass ω) :
    Anchored k.d ω.1.1.2 ω.1.2 := by
  classical
  have hcfg := Screening.Experiment.positive_configuration_anchor_support k μ hsmall ω hpos
  intro c h he u hu
  have hhn : h.val.Nonempty := Finset.card_pos.mp (by
    rw [h.property]
    have := k.d_ge_three
    omega)
  obtain ⟨v, hv⟩ := hhn
  have hstar : (Screening.starSupports
      (Screening.Experiment.starSupport (G := G) (I := I) k.d) ω.1.2 c).Nonempty := by
    refine ⟨Sum.inl v, ?_⟩
    simpa [Screening.starSupports, he, Screening.Experiment.starSupport] using
      (Screening.mem_liftSpecial (G := G) (I := I) h.val v).mpr hv
  have hin : Sum.inl u ∈ Screening.Experiment.fillers (G := G) (I := I) ω.1.1 c := by
    exact (Screening.mem_liftSpecial _ _).mpr hu
  have hout := hcfg c hstar hin
  simpa only [Screening.starSupports, he, Option.elim_some,
    Screening.Experiment.starSupport, Screening.mem_liftSpecial] using hout

theorem experiment_failure (k : Setup S W)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k) :
    Screening.Experiment.failure k (mapQuestions orient algorithm) ω ↔
      let b := actualBook ω.2 k.d ω.1.1.2 ω.1.2 (Fintype.card G / 16)
        ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I)
        (Screening.questions (onlineRun (actualAnswer ω.2 k.d ω.1.1.2 ω.1.2)
          (mapQuestions orient algorithm) []).2)
      b.stop ≠ none ∧ b.stop ≠ some .closure := by
  unfold Screening.Experiment.failure
  rw [onlineRun_record]
  simp only [Screening.questions, List.map_nil, List.nil_append]
  rw [experiment_answer, experiment_internalFillers, experiment_internalStars]
  rfl

theorem bits_eq_visibleBits (k : Setup S W) (H : C → Option (Subsets S k.d)) :
    bits k.d H = Screening.Experiment.visibleBits k H := by
  funext x
  exact decide_eq_decide.mpr Iff.rfl

noncomputable def experimentTree (k : Setup S W)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V)
    (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S) :
    DecisionTree (Candidate S C k.d) Bool V :=
  projectedTree π k.d F (Fintype.card G / 16)
    ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm f

theorem experimentTree_valid (k : Setup S W)
    (hR : k.R = Fintype.card I)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V)
    (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S) :
    Protocol.Valid (VisibleMass.region k.d F) (fun Q => (Q.card : ℝ) ≤ 2 * k.R) ∅
      (experimentTree k algorithm f π F) := by
  rw [hR]
  exact projectedTree_valid_real π k.d F _ _ _ algorithm f

variable [Fintype V]

theorem experiment_projection_close (k : Setup S W) (μ : Law W)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (f : Z × List (Queries S G I C × Reply) → V) :
    Law.Close
      ((Screening.Experiment.law k μ hsmall).map (fun ω =>
        f (gatedRun ω.2 (fun c => fillerNeighbors (ω.1.1.2 c))
          (fun c => (ω.1.2 c).elim ∅ Subtype.val) algorithm [])))
      (Screening.Experiment.visibleOutputLaw k μ hsmall (experimentTree k algorithm f))
      ((Screening.Experiment.law k μ hsmall).prob
        {ω | Screening.Experiment.failure k (mapQuestions orient algorithm) ω} +
        (Screening.Experiment.law k μ hsmall).prob {ω |
          ((tree ω.2 k.d ω.1.1.2 (Fintype.card G / 16)
            ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm).output
              (bits k.d ω.1.2)).state.stop = some .closure}) := by
  classical
  let law := Screening.Experiment.law (G := G) (I := I) (C := C) k μ hsmall
  let actual := fun ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k =>
    f (gatedRun ω.2 (fun c => fillerNeighbors (ω.1.1.2 c))
      (fun c => (ω.1.2 c).elim ∅ Subtype.val) algorithm [])
  let simulated := fun ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k =>
    f (observable ((tree ω.2 k.d ω.1.1.2 (Fintype.card G / 16)
      ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm).output
        (bits k.d ω.1.2)))
  let bad := {ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k |
    Screening.Experiment.failure k (mapQuestions orient algorithm) ω}
  let overflow := {ω : Screening.Experiment.Configuration (G := G) (I := I) (C := C) k |
    ((tree ω.2 k.d ω.1.1.2 (Fintype.card G / 16)
      ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm).output
        (bits k.d ω.1.2)).state.stop = some .closure}
  have hm : law.prob {ω | actual ω ≠ simulated ω} ≤ law.prob bad + law.prob overflow := by
    apply (law.prob_mono_support (F := bad ∪ overflow) ?_).trans (law.prob_union_le bad overflow)
    intro ω hpos hne
    by_cases hbad : ω ∈ bad
    · exact Or.inl hbad
    right
    have hgood : NoOtherStop (actualBook ω.2 k.d ω.1.1.2 ω.1.2 (Fintype.card G / 16)
        ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I)
        (Screening.questions (onlineRun (actualAnswer ω.2 k.d ω.1.1.2 ω.1.2)
          (mapQuestions orient algorithm) []).2)) := by
      have hh := (experiment_failure k algorithm ω).not.mp hbad
      exact Classical.or_iff_not_imp_left.mpr (fun hn => Classical.not_not.mp (fun hc => hh ⟨hn, hc⟩))
    rcases tree_actual_or_overflow ω.2 k.d ω.1.1.2 ω.1.2
        (experiment_anchored k μ hsmall ω hpos) _ _ _ algorithm hgood with hov | he
    · exact hov
    · have hab : observable ((tree ω.2 k.d ω.1.1.2 (Fintype.card G / 16)
          ((Fintype.card G * Fintype.card I + 15) / 16) (Fintype.card I) algorithm).output
            (bits k.d ω.1.2)) =
          gatedRun ω.2 (fun c => fillerNeighbors (ω.1.1.2 c))
            (fun c => (ω.1.2 c).elim ∅ Subtype.val) algorithm [] :=
        Prod.ext he.1 he.2
      exact False.elim (hne (congrArg f hab).symm)
  have hc := (Law.close_maps law actual simulated).mono hm
  have heq : Screening.Experiment.visibleOutputLaw k μ hsmall (experimentTree k algorithm f) =
      law.map simulated := by
    unfold Screening.Experiment.visibleOutputLaw
    apply congrArg
    funext ω
    rw [experimentTree, projectedTree, DecisionTree.output_map, ← bits_eq_visibleBits]
  rw [heq]
  exact hc

end Public

end SteinerLowerBound.Simulation

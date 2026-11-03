module

public import SteinerUpperBound.LargeCoverProgram.Deletion

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators
open Covers.FiniteSampling

variable {Q : Type*} {n k : ℕ}

theorem deletion_value_close (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).Nonempty)
    (F : Option (Selection (Fin n) × Vector Bool n) → ℝ)
    (hF₀ : ∀ v, 0 ≤ F v) (hF₁ : ∀ v, F v ≤ 1) :
    |(deletion p terminals root key a c).evaluate w bits (fun o => F o.value.value) -
      (tape (Covers.Rejection.uniformRetained (fun u => bits (key (terminals.get u))) hb) p.poolSamples).expect
        (fun labels => (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
          (ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
            (fun i => terminals.get (labels i)) (5 * a / 8))).expect
              (fun T => F (some (deletionValue w a T))))| ≤
      Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals := by
  let phi : Option (Fin p.poolSamples → Fin (k + 1)) → ℝ := fun labels =>
    labels.elim (F none) (fun labels =>
      (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
        (ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
          (fun i => terminals.get (labels i)) (5 * a / 8))).expect
          (fun T => F (some (deletionValue w a T))))
  have hp₀ : ∀ labels, 0 ≤ phi labels := by
    intro labels
    cases labels with
    | none => exact hF₀ none
    | some labels => exact Law.expect_nonneg _ (fun T => hF₀ _)
  have hp₁ : ∀ labels, phi labels ≤ 1 := by
    intro labels
    cases labels with
    | none => exact hF₁ none
    | some labels =>
        exact (Law.expect_mono _ (fun T => hF₁ _)).trans_eq (Law.expect_const _ 1)
  have he :
      (deletion p terminals root key a c).evaluate w bits (fun o => F o.value.value) =
      ((Covers.Rejection.poolLaw p.poolRowCap p.poolSamples).map
        (Mean.cappedAccepted (fun u => bits (key (terminals.get u))) root
          p.poolRowCap p.poolSamples p.poolProposals)).expect phi := by
    rw [deletion, Code.evaluate_bind]
    simp only [Outcome.combine]
    have hfun : (fun o : Outcome (Sampler.Records Q k p.poolSamples) =>
        (deletionAfterPool p terminals a o.value).evaluate w bits (fun z => F z.value.value)) =
        fun o => phi (Mean.selected (Sampler.Observation.ofRecords o.value)) := by
      funext o
      exact deletionAfterPool_value w bits p terminals a o.value F
    rw [hfun]
    rw [Mean.sampler_selected_expect w bits _ root _ _ _ c hc phi, Law.expect_map]
  rw [he]
  have ht := (Mean.cappedAccepted_uniform_close (fun u => bits (key (terminals.get u))) hb root
    p.poolRowCap p.poolSamples p.poolProposals).expect_bound phi hp₀ hp₁
  simpa only [Law.expect_map, Option.elim_some, phi] using ht

theorem expect_withFintype {U : Type*} (i j : Fintype U) (mu : @Law U i) (F : U → ℝ) :
    @Law.expect U j (LawOperations.withFintype i j mu) F = @Law.expect U i mu F := by
  have he : i = j := Subsingleton.elim _ _
  cases he
  rfl

theorem tape_map_expect {U V : Type*} [Fintype U] [Fintype V]
    (mu : Law U) (f : U → V) (s : ℕ) (F : (Fin s → V) → ℝ) :
    (tape (mu.map f) s).expect F =
      (tape mu s).expect (fun labels => F (fun i => f (labels i))) := by
  induction s with
  | zero =>
      simp only [tape, Law.expect_pure]
      congr 1
      funext i
      exact Fin.elim0 i
  | succ s ih =>
      rw [expect_tape_succ, expect_tape_succ, Law.expect_map]
      apply congrArg mu.expect
      funext u
      rw [ih]
      apply congrArg (tape mu s).expect
      funext labels
      congr 1
      funext i
      refine Fin.cases rfl (fun _ => rfl) i

theorem uniformRetained_map {U : Type*} [Fintype U] (b : U → Bool)
    (hb : (Covers.Rejection.retained b).Nonempty) :
    letI : Nonempty ↥(Covers.Rejection.retained b) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
    (Law.uniform ↥(Covers.Rejection.retained b)).map Subtype.val =
      Covers.Rejection.uniformRetained b hb := by
  letI : Nonempty ↥(Covers.Rejection.retained b) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  apply LawOperations.ext_mass
  intro u
  by_cases hu : b u = true
  · have hm : u ∈ Covers.Rejection.retained b := by
      simpa only [Covers.Rejection.retained, CategoricalCoupling.selected,
        Finset.mem_filter, Finset.mem_univ, true_and] using hu
    let x : ↥(Covers.Rejection.retained b) := ⟨u, hm⟩
    have he (z : ↥(Covers.Rejection.retained b)) : z.val = u ↔ z = x := by
      exact ⟨fun hz => Subtype.ext hz, fun hz => congrArg Subtype.val hz⟩
    simp only [Law.map, Law.uniform, he, Fintype.card_coe,
      Covers.Rejection.uniformRetained, hu, ite_true]
    simp
  · have he (z : ↥(Covers.Rejection.retained b)) : z.val ≠ u := by
      intro hz
      have hm : b z.val = true := by
        simpa [Covers.Rejection.retained, CategoricalCoupling.selected] using z.property
      exact hu (hz ▸ hm)
    simp [Law.map, Covers.Rejection.uniformRetained, hu, he]

noncomputable def selectionBits (selected : Selection (Fin n)) : Fin n → Bool :=
  fun v => decide (v ∈ selected.centers)

theorem selectionBits_value (bits : Fin n → Bool) :
    selectionBits (selectionValue (fun v : Fin n => v) bits) = bits := by
  funext v
  simp only [selectionBits, selection_mem]
  cases hb : bits v
  · simp [hb]
  · simp [hb]

noncomputable def retainedRows (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ) :
    Fin n → Finset ↥(Covers.Rejection.retained (fun u => bits (key (terminals.get u)))) :=
  ReusableSample.OracleProgram.rows w (fun v : Fin n => v)
    (fun u => terminals.get u.val) (5 * a / 8)

def PoolGood (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (value : Option (Selection (Fin n) × Vector Bool n)) : Prop :=
  value.elim False (fun v =>
    ReusableSample.Specification (retainedRows w bits terminals key a) p.t (selectionBits v.1))

theorem PoolGood_deletionValue (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ) (T : Fin n → Bool) :
    PoolGood w bits p terminals key a (some (deletionValue w a T)) ↔
      ReusableSample.Specification (retainedRows w bits terminals key a) p.t T := by
  simp only [PoolGood, Option.elim_some, deletionValue, selectionBits_value]

/-- Fresh actual rejection samples feed the reusable sample. The TV loss is
the actual proposal/row cap error; calibration is not conditioned upon. -/
theorem deletion_pool_failure (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).Nonempty)
    (beta : ℝ) (ht : 0 < p.t) (hbeta : 0 < beta) (hbeta' : beta < 1 / 4)
    (hL : ReusableSample.logBudget p.t beta ≤ p.Lbar)
    (hM : ReusableSample.rowBudget n p.t beta ≤ p.Mbar) :
    (deletion p terminals root key a c).probability w bits
      {o | ¬ PoolGood w bits p terminals key a o.value.value} ≤
      Mean.capError (fun u => bits (key (terminals.get u)))
        p.poolRowCap p.poolSamples p.poolProposals + beta := by
  let bu := fun u => bits (key (terminals.get u))
  let U := ↥(Covers.Rejection.retained bu)
  letI : Nonempty U := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  let R := retainedRows w bits terminals key a
  let F : Option (Selection (Fin n) × Vector Bool n) → ℝ := fun v =>
    if PoolGood w bits p terminals key a v then 0 else 1
  let f : (Fin p.poolSamples → U) → ℝ := fun X =>
    (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
      (ReusableSample.membershipMatrix R X)).prob
        {T | ¬ ReusableSample.Specification R p.t T}
  have hold := (ReusableSample.integer_reusable_sample_rational R p.t ht beta hbeta hbeta'
    p.Lbar p.Mbar hL hM).1
  have hfail : (ReusableSample.rationalRun p.Lbar p.poolSamples p.t R).prob
      {T | ¬ ReusableSample.Specification R p.t T} ≤ beta := by
    have hh := (ReusableSample.rationalRun p.Lbar p.poolSamples p.t R).prob_compl
      {T | ReusableSample.Specification R p.t T}
    change (ReusableSample.rationalRun p.Lbar p.poolSamples p.t R).prob
      {T | ¬ ReusableSample.Specification R p.t T} =
        1 - (ReusableSample.rationalRun p.Lbar p.poolSamples p.t R).prob _ at hh
    dsimp [Parameters.poolSamples] at *
    linarith
  have hbe := @Law.prob_bind (Fin p.poolSamples → U) (Fin n → Bool)
    (ReusableSample.dataFintype (U := U) p.poolSamples) inferInstance
    ((Law.uniform U).iid (Fin p.poolSamples))
    (fun X => ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
      (ReusableSample.membershipMatrix R X)) {T | ¬ ReusableSample.Specification R p.t T}
  change (@Law.prob (Fin n → Bool) inferInstance
    (@Law.bind (Fin p.poolSamples → U) (Fin n → Bool)
      (ReusableSample.dataFintype (U := U) p.poolSamples) inferInstance
      ((Law.uniform U).iid (Fin p.poolSamples))
      (fun X => ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
        (ReusableSample.membershipMatrix R X))) _) ≤ beta at hfail
  rw [hbe] at hfail
  have hte : (tape (Law.uniform U) p.poolSamples).expect f =
      @Law.expect (Fin p.poolSamples → U) (ReusableSample.dataFintype (U := U) p.poolSamples)
        ((Law.uniform U).iid (Fin p.poolSamples)) f := by
    rw [tape_eq_iid]
    exact expect_withFintype (ReusableSample.dataFintype (U := U) p.poolSamples) inferInstance
      ((Law.uniform U).iid (Fin p.poolSamples)) f
  have htf : (tape (Law.uniform U) p.poolSamples).expect f ≤ beta := by
    rw [hte]
    exact hfail
  have hmat (X : Fin p.poolSamples → U) :
      ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
        (fun i => terminals.get (X i).val) (5 * a / 8) =
        ReusableSample.membershipMatrix R X := by
    exact ReusableSample.OracleProgram.observed_eq_membership w (fun v : Fin n => v)
      (fun u : U => terminals.get u.val) X (5 * a / 8)
  have hideal :
      (tape (Covers.Rejection.uniformRetained bu hb) p.poolSamples).expect
        (fun labels => (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
          (ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
            (fun i => terminals.get (labels i)) (5 * a / 8))).expect
              (fun T => F (some (deletionValue w a T)))) ≤ beta := by
    rw [← uniformRetained_map bu hb, tape_map_expect]
    have he : (fun X : Fin p.poolSamples → U =>
        (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
          (ReusableSample.OracleProgram.observedMatrix w (fun v : Fin n => v)
            (fun i => terminals.get ((X i).val)) (5 * a / 8))).expect
              (fun T => F (some (deletionValue w a T)))) = f := by
      funext X
      rw [hmat]
      dsimp [f]
      rw [Law.prob_eq_expect]
      apply congrArg (ReusableSample.rationalMatrixMechanism p.Lbar p.poolSamples p.t
        (ReusableSample.membershipMatrix R X)).expect
      funext T
      dsimp [F]
      by_cases hg : ReusableSample.Specification R p.t T <;>
        simp only [PoolGood_deletionValue, show retainedRows w bits terminals key a = R from rfl,
          hg, ite_true, ite_false, not_true_eq_false, not_false_eq_true]
    rw [he]
    exact htf
  have he := deletion_value_close w bits p terminals root key a c hc hb F
    (fun v => by dsimp [F]; split_ifs <;> norm_num)
    (fun v => by dsimp [F]; split_ifs <;> norm_num)
  have hactual : (deletion p terminals root key a c).probability w bits
      {o | ¬ PoolGood w bits p terminals key a o.value.value} =
        (deletion p terminals root key a c).evaluate w bits (fun o => F o.value.value) := by
    unfold Code.probability
    apply congrArg ((deletion p terminals root key a c).evaluate w bits)
    funext o
    dsimp [F]
    split_ifs <;> simp_all
  rw [hactual]
  linarith [(abs_le.mp he).2]

end SteinerUpperBound.LargeCoverProgram

module

public import SteinerUpperBound.EstimatorBootstrap
public import SteinerUpperBound.ProbabilityAccounting

@[expose] public section

noncomputable section

namespace SteinerUpperBound.EstimatorBootstrap

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids
open scoped Classical

variable {n k : ℕ}

noncomputable local instance probabilityVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance probabilityLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _
noncomputable local instance probabilityCoordinateDecEq (t : Tables) :
    DecidableEq (RuntimeWorld.Coordinate t k) := Classical.decEq _

private theorem expect_of_good_support {S : Type*} [Fintype S] (mu : Law S)
    (G : Set S) (f : S → ℝ) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hf : ∀ s, 0 ≤ f s) (hg : ∀ s, 0 < mu.mass s → s ∈ G → 1 - epsilon ≤ f s) :
    1 - epsilon - mu.prob Gᶜ ≤ mu.expect f := by
  have h := mu.expect_mono_support (f := fun s => (1 - epsilon) - if s ∈ G then 0 else 1)
    (g := f) (by
      intro s hs
      by_cases hG : s ∈ G
      · simpa only [hG, ite_true, sub_zero] using hg s hs hG
      · simp only [hG, ite_false]
        linarith [hf s])
  have hi : mu.expect (fun s => if s ∈ G then 0 else (1 : ℝ)) = mu.prob Gᶜ := by
    rw [Law.prob_eq_expect]
    apply congrArg mu.expect
    funext s
    by_cases hG : s ∈ G <;> simp [hG]
  simpa only [Law.expect_sub, Law.expect_const, hi] using h

private theorem readout_sound (P : ℝ → Prop) (r : Option (Option ℝ))
    (hr : Code.SomeGood (Code.SomeGood P) r) : P (r.join.getD 0) := by
  obtain ⟨a, rfl, b, rfl, hb⟩ := hr
  exact hb

private theorem scalar_factory_success {V Q : Type*} [Fintype Q] {count : ℕ}
    (cfg : Covers.OracleProgram.Config V Q count) (cache : Cache Q) (W D ordinary positive : ℕ)
    (frontend : Code (Sym2 V) Q (Option ℝ)) (m : Sym2 V → ℝ) (P : ℝ → Prop)
    (G : Set (Q → Bool)) (sampleLoss worldLoss cutoff : ℝ) (he : 0 ≤ sampleLoss) (ha : 0 < cutoff)
    (hworld : (Covers.OracleProgram.bits cfg m cache).prob Gᶜ ≤ worldLoss)
    (hfront : ∀ bits, 0 < (Covers.OracleProgram.bits cfg m cache).mass bits → bits ∈ G →
      1 - sampleLoss ≤ Code.valueProbability m bits frontend (Code.SomeGood P))
    (hwork : (Covers.OracleProgram.bits cfg m cache).expect (fun bits =>
      frontend.evaluate m bits (fun o => (o.work : ℝ))) ≤ ordinary)
    (hpositive : (Covers.OracleProgram.bits cfg m cache).expect (fun bits =>
      frontend.evaluate m bits (fun o => (o.positiveReplies : ℝ))) ≤ positive) :
    1 - sampleLoss - worldLoss - (ordinary : ℝ) / (W + 1 : ℕ) - (positive : ℝ) / cutoff -
        Real.exp (cutoff - (D : ℝ) / (2 * (count + 1))) ≤
      (FactoryExecution.program cfg cache W D frontend).evaluate m Code.emptyBits
        (fun o => if P (o.value.join.getD 0) then (1 : ℝ) else 0) := by
  have hmix := expect_of_good_support (Covers.OracleProgram.bits cfg m cache) G
    (fun bits => Code.valueProbability m bits frontend (Code.SomeGood P)) sampleLoss he
    (fun bits => Code.valueProbability_nonneg m bits frontend (Code.SomeGood P)) hfront
  have hmix' : 1 - sampleLoss - worldLoss ≤
      (Covers.OracleProgram.bits cfg m cache).expect (fun bits =>
        Code.valueProbability m bits frontend (Code.SomeGood P)) := by linarith
  have hex := FactoryExecution.success cfg cache W D frontend m (Code.SomeGood P)
    (1 - sampleLoss - worldLoss) ordinary positive cutoff ha hmix' hwork hpositive
  have hr :
      Code.valueProbability m Code.emptyBits (FactoryExecution.program cfg cache W D frontend)
          (Code.SomeGood (Code.SomeGood P)) ≤
        (FactoryExecution.program cfg cache W D frontend).evaluate m Code.emptyBits
          (fun o => if P (o.value.join.getD 0) then (1 : ℝ) else 0) := by
    apply Code.evaluate_mono
    intro o
    by_cases h : Code.SomeGood (Code.SomeGood P) o.value
    · simp only [h, readout_sound P o.value h, ite_true, le_refl]
    · simp only [h, ite_false]
      split_ifs <;> norm_num
  exact hex.trans hr

/-- Check the factory/readout conversion while `tables` is abstract. Applying
this opaque theorem to generated tables avoids reducing their dependent
coordinate indices while the kernel checks the outer phase mixture. -/
private theorem table_factory_success (p : PublicParameters)
    (label : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (inverse : Vector (Fin (k + 1)) n)
    (tables : Tables) (W D ordinary positive : ℕ) (frontend : Frontend n k)
    (m : Sym2 (Fin n) → ℝ) (P : ℝ → Prop)
    (G : Set (RuntimeWorld.Coordinate tables k → Bool)) (sampleLoss worldLoss cutoff : ℝ)
    (he : 0 ≤ sampleLoss) (ha : 0 < cutoff)
    (hworld : (Covers.OracleProgram.bits (RuntimeWorld.configuration p label tables) m
      (LabelledFactory.initialCache root)).prob Gᶜ ≤ worldLoss)
    (hfront : ∀ bits, 0 < (Covers.OracleProgram.bits (RuntimeWorld.configuration p label tables) m
        (LabelledFactory.initialCache root)).mass bits → bits ∈ G →
      1 - sampleLoss ≤ Code.valueProbability m bits
        (frontend p inverse tables (LabelledFactory.initialCache root)) (Code.SomeGood P))
    (hwork : (Covers.OracleProgram.bits (RuntimeWorld.configuration p label tables) m
        (LabelledFactory.initialCache root)).expect (fun bits =>
      (frontend p inverse tables (LabelledFactory.initialCache root)).evaluate m bits
        (fun o => (o.work : ℝ))) ≤ ordinary)
    (hpositive : (Covers.OracleProgram.bits (RuntimeWorld.configuration p label tables) m
        (LabelledFactory.initialCache root)).expect (fun bits =>
      (frontend p inverse tables (LabelledFactory.initialCache root)).evaluate m bits
        (fun o => (o.positiveReplies : ℝ))) ≤ positive) :
    1 - sampleLoss - worldLoss - (ordinary : ℝ) / (W + 1 : ℕ) - (positive : ℝ) / cutoff -
        Real.exp (cutoff - (D : ℝ) / (2 * (k + 1))) ≤
      Code.valueProbability m Code.emptyBits (atTables p label root W D frontend inverse tables) P := by
  exact (scalar_factory_success (RuntimeWorld.configuration p label tables) (LabelledFactory.initialCache root)
    W D ordinary positive (frontend p inverse tables (LabelledFactory.initialCache root)) m P G
    sampleLoss worldLoss cutoff he ha hworld hfront hwork hpositive).trans_eq
      (atTables_probability p label root W D frontend inverse tables m P).symm

theorem prepared_success (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (hT : Finset.univ.image label.get = I.terminals)
    (root : Fin (k + 1)) (W D ordinary positive : ℕ) (cutoff : ℝ) (ha : 0 < cutoff)
    (frontend : Frontend n k) (R : ℝ) (hR : 0 < R) (P : ℝ → Prop)
    (PhaseGood : Set (Fin FinitePhase.count)) (phaseLoss sampleLoss : ℝ)
    (he : 0 ≤ sampleLoss) (hphase : FinitePhase.law.prob PhaseGoodᶜ ≤ phaseLoss)
    (hfront : ∀ phase ∈ PhaseGood,
      let t := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      ∀ bits, 0 < (Covers.OracleProgram.bits
          (RuntimeWorld.configuration (parameters n (k + 1)) label t) I.weight
          (LabelledFactory.initialCache root)).mass bits →
        RuntimeWorld.Good I label t bits →
        1 - sampleLoss ≤ Code.valueProbability I.weight bits
          (frontend (parameters n (k + 1)) (PublicTerminals.inverseResult label root).value t
            (LabelledFactory.initialCache root)) (Code.SomeGood P))
    (hwork : ∀ phase,
      let t := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label t)
          I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
        (frontend (parameters n (k + 1)) (PublicTerminals.inverseResult label root).value t
          (LabelledFactory.initialCache root)).evaluate I.weight bits (fun o => (o.work : ℝ))) ≤ ordinary)
    (hpositive : ∀ phase,
      let t := (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      (Covers.OracleProgram.bits (RuntimeWorld.configuration (parameters n (k + 1)) label t)
          I.weight (LabelledFactory.initialCache root)).expect (fun bits =>
        (frontend (parameters n (k + 1)) (PublicTerminals.inverseResult label root).value t
          (LabelledFactory.initialCache root)).evaluate I.weight bits
            (fun o => (o.positiveReplies : ℝ))) ≤ positive) :
    1 - sampleLoss - 1 / 4000000 - phaseLoss - (ordinary : ℝ) / (W + 1 : ℕ) -
        (positive : ℝ) / cutoff - Real.exp (cutoff - (D : ℝ) / (2 * (k + 1))) ≤
      Code.valueProbability I.weight Code.emptyBits (prepared label root W D frontend R hR) P := by
  let loss : ℝ := sampleLoss + 1 / 4000000 + (ordinary : ℝ) / (W + 1 : ℕ) +
    (positive : ℝ) / cutoff + Real.exp (cutoff - (D : ℝ) / (2 * (k + 1)))
  have hloss : 0 ≤ loss := by dsimp only [loss]; positivity
  have hgood (phase : Fin FinitePhase.count) (hpg : phase ∈ PhaseGood) :
      1 - loss ≤ Code.valueProbability I.weight Code.emptyBits
        (atTables (parameters n (k + 1)) label root W D frontend
          (PublicTerminals.inverseResult label root).value
          (RuntimeGrids.result (k + 1) (by omega) R hR phase).value) P := by
    have hex := table_factory_success (parameters n (k + 1)) label root
      (PublicTerminals.inverseResult label root).value
      (RuntimeGrids.result (k + 1) (by omega) R hR phase).value
      W D ordinary positive frontend I.weight P
      {bits | RuntimeWorld.Good I label
        (RuntimeGrids.result (k + 1) (by omega) R hR phase).value bits}
      sampleLoss (1 / 4000000) cutoff he ha
      (RuntimeWorld.factory_failure I label hinj hT R hR phase root)
      (fun bits hb hg => hfront phase hpg bits hb hg) (hwork phase) (hpositive phase)
    calc
      1 - loss = 1 - sampleLoss - 1 / 4000000 - (ordinary : ℝ) / (W + 1 : ℕ) -
          (positive : ℝ) / cutoff - Real.exp (cutoff - (D : ℝ) / (2 * (k + 1))) := by
            simp only [loss, sub_add_eq_sub_sub]
      _ ≤ _ := hex
  have hout := ProbabilityAccounting.expect_of_good FinitePhase.law PhaseGood
    (fun phase => Code.valueProbability I.weight Code.emptyBits
      (atTables (parameters n (k + 1)) label root W D frontend
        (PublicTerminals.inverseResult label root).value
        (RuntimeGrids.result (k + 1) (by omega) R hR phase).value) P)
    loss hloss (fun _ => Code.valueProbability_nonneg _ _ _ _) hgood
  calc
    _ = 1 - loss - phaseLoss := by
      simp only [loss, sub_eq_add_neg, neg_add, add_assoc, add_comm, add_left_comm]
    _ ≤ 1 - loss - FinitePhase.law.prob PhaseGoodᶜ := sub_le_sub_left hphase _
    _ ≤ _ := hout
    _ = _ := (prepared_probability label root W D frontend R hR I.weight P).symm

end SteinerUpperBound.EstimatorBootstrap

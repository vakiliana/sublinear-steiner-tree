module

public import SteinerUpperBound.Matching.Padded.Bayes

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace FiniteLaw

variable {A : Type*} [Fintype A]

theorem eq_of_expect (μ ν : Law A) (h : ∀ f : A → ℝ, μ.expect f = ν.expect f) : μ = ν := by
  apply LawOperations.ext_mass
  intro a
  simpa [Law.expect] using h (fun b => if b = a then 1 else 0)

variable {E B : Type*} [Fintype E] [Fintype B]

/-- Product posterior factorization, derived from the coordinate joint laws. -/
theorem pi_joint (μ : E → Law A) (observe : E → A → B) (ν : E → Law B)
    (posterior : E → B → Law A)
    (h : ∀ e, (μ e).map (fun a => (observe e a, a)) =
      (ν e).bind (fun b => (posterior e b).map (fun a => (b, a)))) :
    (Law.pi μ).map (fun ranks => ((fun e => observe e (ranks e)), ranks)) =
      (Law.pi ν).bind (fun obs => (Law.pi fun e => posterior e (obs e)).map
        (fun ranks => (obs, ranks))) := by
  let split : (E → B × A) → (E → B) × (E → A) := fun w =>
    ((fun e => (w e).1), (fun e => (w e).2))
  calc
    _ = ((Law.pi μ).map (fun w e => (observe e (w e), w e))).map split := by
      rw [LawOperations.map_comp]
    _ = (Law.pi fun e => (μ e).map (fun a => (observe e a, a))).map split := by
      exact congrArg (fun κ : Law (E → B × A) => κ.map split)
        (LawOperations.pi_map μ (fun e a => (observe e a, a)))
    _ = (Law.pi fun e => (ν e).bind fun b => (posterior e b).map (fun a => (b, a))).map split := by
      exact congrArg (fun κ : E → Law (B × A) => (Law.pi κ).map split) (funext h)
    _ = ((Law.pi ν).bind fun obs =>
        Law.pi fun e => (posterior e (obs e)).map (fun a => (obs e, a))).map split := by
      rw [LawOperations.pi_bind]
    _ = _ := by
      rw [LawOperations.map_bind]
      congr 1
      funext obs
      rw [← LawOperations.pi_map (fun e => posterior e (obs e)) (fun e a => (obs e, a))]
      rw [LawOperations.map_comp]

end FiniteLaw

namespace Observation

def sample (Q : ℕ) (hQ : 0 < Q) (a b : ℕ) : Program ℕ (Option (Fin Q)) :=
  (IntegerCoin.sample (Range.probability Q a b)).bind fun hit =>
    match hit with
    | true => (Range.sample Q hQ a b).bind fun r => .ret (some r)
    | false => .ret none

noncomputable def law (Q : ℕ) (hQ : 0 < Q) (a b : ℕ) : Law (Option (Fin Q)) :=
  (sample Q hQ a b).law.map (sample Q hQ a b).output

noncomputable def posterior (Q : ℕ) (hQ : 0 < Q) (b : ℕ) : Option (Fin Q) → Law (Fin Q)
  | none => Range.law Q hQ b Q
  | some r => Law.pure r

theorem expect_law (Q : ℕ) (hQ : 0 < Q) (a b : ℕ) (f : Option (Fin Q) → ℝ) :
    (law Q hQ a b).expect f = (sample Q hQ a b).expect f := Law.expect_map _ _ _

theorem joint_law (Q : ℕ) (hQ : 0 < Q) (a b : ℕ) (hab : a < b) (hbQ : b ≤ Q) :
    (Range.law Q hQ a Q).map (fun r => (if r.val < b then some r else none, r)) =
      (law Q hQ a b).bind (fun obs => (posterior Q hQ b obs).map (fun r => (obs, r))) := by
  apply FiniteLaw.eq_of_expect
  intro f
  simp only [Law.expect_map, Law.expect_bind, expect_law]
  unfold sample
  simp only [Program.expect_bind]
  have hh := Range.reveal_identity Q hQ a b hab hbQ (fun tag r => f (tag, r))
  rw [hh]
  congr 1
  funext hit
  cases hit <;> simp only [posterior, Program.expect_bind, Program.expect_ret, Law.expect_pure]

end Observation

namespace DecisionTree

variable {Q A R C : Type*}

def program (sampler : Q → Program C A) : SteinerLowerBound.DecisionTree Q A R → Program C R
  | .leaf r => .ret r
  | .query q next => (sampler q).bind fun a => program sampler (next a)

theorem deferred [Fintype Q] [Fintype A] (μ : Q → Law A) (sampler : Q → Program C A)
    (hs : ∀ q f, (sampler q).expect f = (μ q).expect f)
    (t : SteinerLowerBound.DecisionTree Q A R) (ht : t.NoRepeats) (f : R → ℝ) :
    (program sampler t).expect f = (Law.pi μ).expect (fun w => f (t.output w)) := by
  induction t with
  | leaf r => simp [program, SteinerLowerBound.DecisionTree.output]
  | query q next ih =>
    calc
      _ = (μ q).expect (fun a => (program sampler (next a)).expect f) := by
        rw [program, Program.expect_bind, hs]
      _ = (μ q).expect (fun a => (Law.pi μ).expect (fun w => f ((next a).output w))) := by
        congr 1
        funext a
        exact ih a (ht.1 a)
      _ = (Law.pi μ).expect (fun w =>
          f ((SteinerLowerBound.DecisionTree.query q next).output w)) :=
        (Law.expect_adaptive_coordinate μ q (fun a w => f ((next a).output w))
          (fun a w b => by
            rw [SteinerLowerBound.DecisionTree.output_update _ _ _ _ (ht.2 a)])).symm

theorem deferred_on [Fintype Q] [Fintype A] (μ : Q → Law A) (sampler : Q → Program C A)
    (t : SteinerLowerBound.DecisionTree Q A R) (ht : t.NoRepeats)
    (hs : ∀ q ∈ t.used, ∀ f, (sampler q).expect f = (μ q).expect f) (f : R → ℝ) :
    (program sampler t).expect f = (Law.pi μ).expect (fun w => f (t.output w)) := by
  induction t with
  | leaf r => simp [program, SteinerLowerBound.DecisionTree.output]
  | query q next ih =>
    have hq : q ∈ (SteinerLowerBound.DecisionTree.query q next).used :=
      Finset.mem_insert_self _ _
    have hn (a : A) (q' : Q) (hq' : q' ∈ (next a).used) :
        q' ∈ (SteinerLowerBound.DecisionTree.query q next).used :=
      Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hq'⟩)
    calc
      _ = (μ q).expect (fun a => (program sampler (next a)).expect f) := by
        rw [program, Program.expect_bind, hs q hq]
      _ = (μ q).expect (fun a => (Law.pi μ).expect (fun w => f ((next a).output w))) := by
        congr 1
        funext a
        exact ih a (ht.1 a) (fun q' hq' => hs q' (hn a q' hq'))
      _ = (Law.pi μ).expect (fun w =>
          f ((SteinerLowerBound.DecisionTree.query q next).output w)) :=
        (Law.expect_adaptive_coordinate μ q (fun a w => f ((next a).output w))
          (fun a w b => by
            rw [SteinerLowerBound.DecisionTree.output_update _ _ _ _ (ht.2 a)])).symm

end DecisionTree

end SteinerUpperBound.Matching.Padded

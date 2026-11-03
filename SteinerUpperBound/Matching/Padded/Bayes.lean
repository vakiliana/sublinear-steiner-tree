module

public import SteinerUpperBound.Matching.Padded.Range
public import SteinerLowerBound.DeferredSampling

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Bayes

open SteinerLowerBound
open scoped Classical BigOperators

variable {E A : Type*} [Fintype E] [Fintype A]

theorem expect_pi_update (μ : E → Law A) (e : E) (ν : Law A) (f : (E → A) → ℝ) :
    (Law.pi (Function.update μ e ν)).expect f =
      ∑ a, ν.mass a *
        ∑ others : {d // d ≠ e} → A,
          (∏ d : {d // d ≠ e}, (μ d.val).mass (others d)) *
            f ((Law.splitAt e).symm (a, others)) := by
  rw [Law.expect_pi_split _ e f]
  simp only [Function.update_self]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro others _
  congr 1
  apply Finset.prod_congr rfl
  intro d _
  rw [Function.update_of_ne d.property]

theorem expect_pi_pure_update (μ : E → Law A) (e : E) (a : A) (f : (E → A) → ℝ) :
    (Law.pi (Function.update μ e (Law.pure a))).expect f =
      ∑ others : {d // d ≠ e} → A,
        (∏ d : {d // d ≠ e}, (μ d.val).mass (others d)) *
          f ((Law.splitAt e).symm (a, others)) := by
  rw [expect_pi_update]
  simp [Law.pure]

variable (Q : ℕ) (hQ : 0 < Q)

/-- Exact joint posterior after one eligible copy's threshold test. -/
theorem reveal_coordinate (μ : E → Law (Fin Q)) (e : E) (a b : ℕ)
    (hab : a < b) (hbQ : b ≤ Q) (hμ : μ e = Range.law Q hQ a Q)
    (f : Option (Fin Q) → (E → Fin Q) → ℝ) :
    (Law.pi μ).expect (fun ranks =>
      f (if (ranks e).val < b then some (ranks e) else none) ranks) =
      (IntegerCoin.sample (Range.probability Q a b)).expect (fun hit =>
        match hit with
        | true => (Range.sample Q hQ a b).expect (fun r =>
            (Law.pi (Function.update μ e (Law.pure r))).expect (f (some r)))
        | false => (Law.pi (Function.update μ e (Range.law Q hQ b Q))).expect (f none)) := by
  classical
  let g : Option (Fin Q) → Fin Q → ℝ := fun tag r =>
    ∑ others : {d // d ≠ e} → Fin Q,
      (∏ d : {d // d ≠ e}, (μ d.val).mass (others d)) *
        f tag ((Law.splitAt e).symm (r, others))
  have hleft :
      (Law.pi μ).expect (fun ranks =>
        f (if (ranks e).val < b then some (ranks e) else none) ranks) =
      (Range.law Q hQ a Q).expect
        (fun r => g (if r.val < b then some r else none) r) := by
    rw [Law.expect_pi_split μ e]
    simp only [Law.splitAt_same]
    rw [hμ]
    rfl
  rw [hleft, Range.reveal_identity Q hQ a b hab hbQ g]
  apply congrArg
  funext hit
  cases hit <;> dsimp only
  · rw [expect_pi_update]
    rfl
  · apply congrArg
    funext r
    rw [expect_pi_pure_update]

end SteinerUpperBound.Matching.Padded.Bayes

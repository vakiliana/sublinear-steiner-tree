module

public import SteinerUpperBound.Matching.Padded.CausalContract
public import SteinerUpperBound.Covers.OracleProgramMeanBasic

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram.Support

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical

variable {M Q R S : Type*}

theorem ensures_pure (m : M → ℝ) (bits : Q → Bool) (r : R) (P : R → Prop) (hr : P r) :
    Causal.Ensures m bits (.pure r) P := by
  intro F hF
  exact hF r hr

theorem ensures_tick (m : M → ℝ) (bits : Q → Bool) (cost : ℕ)
    (p : Code M Q R) (P : R → Prop) (h : Causal.Ensures m bits p P) :
    Causal.Ensures m bits (.tick cost p) P := h

theorem ensures_bind (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) (P : R → Prop) (T : S → Prop)
    (hp : Causal.Ensures m bits p P)
    (hk : ∀ r, P r → Causal.Ensures m bits (next r) T) :
    Causal.Ensures m bits (p.bind next) T := by
  intro F hF
  rw [Causal.expect_bind]
  exact hp _ (fun r hr => hk r hr F hF)

theorem ensures_bind_evaluates (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (next : R → Code M Q S) (o : Outcome R)
    (hp : Code.Evaluates m bits p o) (T : S → Prop)
    (hk : Causal.Ensures m bits (next o.value) T) :
    Causal.Ensures m bits (p.bind next) T := by
  intro F hF
  rw [Causal.expect_bind, Causal.expect, hp]
  exact hk F hF

theorem ensures_coin (m : M → ℝ) (bits : Q → Bool) (r : Rate)
    (next : Bool → Code M Q R) (P : R → Prop)
    (h : ∀ b, Causal.Ensures m bits (next b) P) :
    Causal.Ensures m bits (.coin r next) P := by
  intro F hF
  change (CategoricalCoupling.bernoulli r).expect
    (fun b => Causal.expect m bits (next b) F) = 0
  have he : (fun b => Causal.expect m bits (next b) F) = fun _ => 0 := by
    funext b
    exact h b F hF
  rw [he, Law.expect_const]

theorem ensures_of_runs (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (P : R → Prop) (h : ∀ o, Runs m bits p o → P o.value) :
    Causal.Ensures m bits p P := by
  intro F hF
  unfold Causal.expect
  exact (Mean.evaluate_congr_runs m bits p _ (fun _ => 0)
    (fun o ho => hF o.value (h o ho))).trans (Code.evaluate_const m bits p 0)

theorem ensures_mono (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (P T : R → Prop) (h : Causal.Ensures m bits p P) (hPT : ∀ r, P r → T r) :
    Causal.Ensures m bits p T := by
  intro F hF
  exact h F (fun r hr => hF r (hPT r hr))

/-- Comparisons need hold only on actual positive support, not on zero-mass
counterfactual branches of `Runs`. -/
theorem expect_mono (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (P : R → Prop) (hP : Causal.Ensures m bits p P) (F G : R → ℝ)
    (h : ∀ r, P r → F r ≤ G r) :
    Causal.expect m bits p F ≤ Causal.expect m bits p G := by
  let e := fun r => max (F r - G r) 0
  have hz := hP e (fun r hr => max_eq_right (sub_nonpos.mpr (h r hr)))
  have hh := Code.evaluate_mono m bits p
    (F := fun o => F o.value) (G := fun o => G o.value + e o.value)
    (fun o => by
      have he : F o.value - G o.value ≤ e o.value := le_max_left _ _
      linarith)
  rw [Code.evaluate_add] at hh
  change Causal.expect m bits p F ≤ Causal.expect m bits p G + Causal.expect m bits p e at hh
  linarith

theorem expect_close (m : M → ℝ) (bits : Q → Bool) (p : Code M Q R)
    (P : R → Prop) (hP : Causal.Ensures m bits p P) (F G : R → ℝ) (delta : ℝ)
    (h : ∀ r, P r → |F r - G r| ≤ delta) :
    |Causal.expect m bits p F - Causal.expect m bits p G| ≤ delta := by
  have hhi := expect_mono m bits p P hP F (fun r => G r + delta)
    (fun r hr => by linarith [(abs_le.mp (h r hr)).2])
  have hlo := expect_mono m bits p P hP G (fun r => F r + delta)
    (fun r hr => by linarith [(abs_le.mp (h r hr)).1])
  dsimp only [Causal.expect] at hhi hlo ⊢
  rw [Code.evaluate_add, Code.evaluate_const] at hhi hlo
  rw [abs_le]
  constructor <;> linarith

end SteinerUpperBound.LargeCoverProgram.Support

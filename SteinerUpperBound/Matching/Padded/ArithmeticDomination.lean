module

public import SteinerUpperBound.Matching.Padded.Domination
public import SteinerUpperBound.Matching.Padded.Commands

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Causal

open scoped Classical

variable {V E M T A : Type*} {G : Graph V E} {S : Slots G}

theorem compile_dominates (m : M → ℝ) (b : T → Bool) (counter : Counter)
    (account : Account S) (hrate : account.rate = counter.work) (p : Program ℕ A) :
    Dominates m b counter (Command.charge account) account.rate
      (Command.liftArithmetic (S := S) p) (compile p) Eq := by
  induction p with
  | ret a => exact Dominates.ret m b counter _ _ a a Eq rfl
  | tick n p ih =>
    exact Dominates.spend m b counter _ _ (.arithmetic n) n _ _ Eq
      (by simp only [Command.charge, hrate, le_refl]) ih
  | draw n hn next ih =>
    cases n with
    | zero => omega
    | succ n =>
      exact Dominates.uniform m b counter _ _ n _ _ Eq (le_of_eq hrate.symm) ih

theorem ensures_holds_of_evaluates (m : M → ℝ) (b : T → Bool) (code : Code M T A)
    (P : A → Prop) (h : Ensures m b code P) (o : Outcome A) (he : code.Evaluates m b o) :
    P o.value := by
  classical
  by_contra hn
  have hz := h (fun a => if P a then 0 else 1) (fun a ha => by simp [ha])
  unfold expect at hz
  rw [he] at hz
  simp only [hn, ↓reduceIte, one_ne_zero] at hz

end SteinerUpperBound.Matching.Padded.Causal

module

public import SteinerUpperBound.ComponentExplore
public import SteinerUpperBound.Covers.OracleProgramMeanCache
public import SteinerUpperBound.BandEvaluation.Compiled

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram Covers.OracleProgram
open scoped Classical

variable {M Q R S : Type*}

def NoRandom : Code M Q R → Prop
  | .pure _ => True
  | .metric _ next => ∀ x, NoRandom (next x)
  | .retained _ next => ∀ x, NoRandom (next x)
  | .tick _ next => NoRandom next
  | _ => False

theorem noRandom_bind (p : Code M Q R) (next : R → Code M Q S)
    (hp : NoRandom p) (hn : ∀ r, NoRandom (next r)) : NoRandom (p.bind next) := by
  induction p with
  | pure r => exact hn r
  | metric q next ih => exact fun x => ih x (hp x)
  | retained q next ih => exact fun x => ih x (hp x)
  | tick n next ih => exact ih hp
  | uniform n next ih => exact hp.elim
  | coin p next ih => exact hp.elim

theorem noRandom_foldList {A : Type*} (body : S → A → Code M Q S)
    (hbody : ∀ s a, NoRandom (body s a)) (l : List A) (s : S) :
    NoRandom (Code.foldList body l s) := by
  induction l generalizing s with
  | nil => trivial
  | cons a l ih => exact noRandom_bind _ _ (hbody s a) ih

theorem metricOnly_noRandom (p : Code M Q R) (h : SmallCoverProgram.MetricOnly p) : NoRandom p := by
  induction p with
  | pure r => trivial
  | metric q next ih => exact fun x => ih x (h x)
  | retained q next ih => exact h.elim
  | tick n next ih => exact ih h
  | uniform n next ih => exact h.elim
  | coin p next ih => exact h.elim

theorem runs_evaluates {m : M → ℝ} {b : Q → Bool} {p : Code M Q R} {o : Outcome R}
    (hr : Runs m b p o) (hp : NoRandom p) : Code.Evaluates m b p o := by
  revert hp
  induction hr with
  | pure r => intro _; exact Code.evaluates_pure _ _ _
  | @metric q next o hr ih =>
      intro hp F
      exact ih (hp (m q)) (fun o => F (o.add 1 1 0 0))
  | @retained q next o hr ih =>
      intro hp F
      exact ih (hp (b q)) (fun o => F (o.add 1 0 1 (if b q then 1 else 0)))
  | @tick n next o hr ih =>
      intro hp F
      exact ih hp (fun o => F (o.add (n + 1) 0 0 0))
  | uniform a hr ih => intro hp; exact hp.elim
  | coin a hr ih => intro hp; exact hp.elim

theorem runs_eq_of_evaluates (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) (hp : NoRandom p)
    (o : Outcome R) (he : Code.Evaluates m b p o) (r : Outcome R) (hr : Runs m b p r) : r = o := by
  classical
  have h := runs_evaluates hr hp (fun r => if r = o then (1 : ℝ) else 0)
  rw [he] at h
  by_contra hn
  simp [hn] at h

variable {V : Type*}

private theorem explore_member_noRandom (x : V) (l : List V) :
    NoRandom (ComponentExplore.member (M := M) (Q := Q) x l) := by
  induction l with
  | nil => trivial
  | cons y l ih =>
      unfold ComponentExplore.member
      split_ifs
      · trivial
      · exact ih

private theorem pending_noRandom (found done l : List V) :
    NoRandom (ComponentExplore.pendingProgram (M := M) (Q := Q) found done l) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
      apply noRandom_bind _ _ (explore_member_noRandom x found)
      intro hf
      cases hf
      · exact ih
      · apply noRandom_bind _ _ (explore_member_noRandom x done)
        intro hd
        cases hd
        · trivial
        · exact ih

theorem resolve_noRandom (q : Q) (c : Cache Q) : NoRandom (Cache.resolve (M := M) q c) := by
  unfold Cache.resolve
  cases c q
  · intro _
    trivial
  · trivial

private theorem explore_step_noRandom (key : V → Q) (a : ℝ) (B : ℕ) (x : V)
    (s : ComponentExplore.Memory V Q) (y : V) :
    NoRandom (ComponentExplore.stepProgram key a B x s y) := by
  unfold ComponentExplore.stepProgram
  split_ifs
  · trivial
  · apply noRandom_bind _ _ (explore_member_noRandom y s.points)
    intro seen
    cases seen
    · intro d
      dsimp only
      split_ifs
      · exact noRandom_bind _ _ (resolve_noRandom (key y) s.cache) (fun _ => trivial)
      · trivial
    · trivial

private theorem explore_loop_noRandom (key : V → Q) (a : ℝ) (B : ℕ) (l : List V)
    (fuel : ℕ) (s : ComponentExplore.Memory V Q) :
    NoRandom (ComponentExplore.loopProgram key a B l fuel s) := by
  induction fuel generalizing s with
  | zero =>
      unfold ComponentExplore.loopProgram
      split_ifs
      · trivial
      · exact noRandom_bind _ _ (pending_noRandom _ _ _) (fun _ => trivial)
  | succ fuel ih =>
      unfold ComponentExplore.loopProgram
      split_ifs
      · trivial
      · apply noRandom_bind _ _ (pending_noRandom _ _ _)
        intro p
        cases p with
        | none => trivial
        | some x =>
            apply noRandom_bind
            · exact noRandom_foldList _ (explore_step_noRandom key a B x) _ _
            · exact ih

theorem explore_noRandom (key : V → Q) (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) :
    NoRandom (ComponentExplore.program key a B l root c) :=
  explore_loop_noRandom key a B l (B + 1) (ComponentExplore.initial root c)

end SteinerUpperBound.BandEvaluation

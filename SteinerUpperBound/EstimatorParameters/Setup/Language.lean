module

public import SteinerUpperBound.EstimatorParameters.Setup.IntegerLoops

@[expose] public section

namespace SteinerUpperBound.EstimatorParameters.Setup

open QueryProgram

inductive Expr
  | atom : ℕ → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | log : Expr → Expr
  | sqrt : Expr → Expr

namespace Expr

def value : Expr → ℕ
  | .atom n => n
  | .add a b => a.value + b.value
  | .mul a b => a.value * b.value
  | .log a => Nat.log2 a.value
  | .sqrt a => Nat.sqrt a.value

def work : Expr → ℕ
  | .atom _ => 1
  | .add a b => a.work + b.work + 1
  | .mul a b => a.work + b.work + 1
  | .log a => a.work + (6 * Nat.log2 a.value + 4)
  | .sqrt a => a.work + integerSqrtWork a.value

def program {M Q : Type*} : Expr → Code M Q ℕ
  | .atom n => .tick 0 (.pure n)
  | .add a b => a.program.bind (fun x => b.program.bind (fun y => .tick 0 (.pure (x + y))))
  | .mul a b => a.program.bind (fun x => b.program.bind (fun y => .tick 0 (.pure (x * y))))
  | .log a => a.program.bind logCode
  | .sqrt a => a.program.bind integerSqrt

theorem evaluates {M Q : Type*} (m : M → ℝ) (bits : Q → Bool) (e : Expr) :
    Code.Evaluates m bits e.program ⟨e.value, e.work, 0, 0, 0⟩ := by
  induction e with
  | atom n => intro F; rfl
  | add a b iha ihb =>
    intro F
    simp only [program, Code.evaluate_bind]
    rw [iha, ihb]
    simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, value, work]
    congr 2 <;> omega
  | mul a b iha ihb =>
    intro F
    simp only [program, Code.evaluate_bind]
    rw [iha, ihb]
    simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, value, work]
    congr 2 <;> omega
  | log a ih =>
    intro F
    rw [program, Code.evaluate_bind, ih, logCode_evaluates]
    simp only [Outcome.combine, Outcome.pure, value, work]
  | sqrt a ih =>
    intro F
    rw [program, Code.evaluate_bind, ih, integerSqrt_evaluates]
    simp only [Outcome.combine, Outcome.pure, value, work]

end Expr

inductive Plan (Out : Type*)
  | emit : Out → Plan Out
  | step : Expr → (ℕ → Plan Out) → Plan Out

namespace Plan

def bind {A B : Type*} : Plan A → (A → Plan B) → Plan B
  | .emit a, next => next a
  | .step e next, tail => .step e (fun x => (next x).bind tail)

instance : Monad Plan where
  pure := .emit
  bind := bind

def value {Out : Type*} : Plan Out → Out
  | .emit r => r
  | .step e next => (next e.value).value

def work {Out : Type*} : Plan Out → ℕ
  | .emit _ => 23
  | .step e next => e.work + 1 + (next e.value).work

def program {M Q Out : Type*} : Plan Out → Code M Q Out
  | .emit r => .tick 22 (.pure r)
  | .step e next => e.program.bind (fun x => .tick 0 (next x).program)

theorem evaluates {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool) (p : Plan Out) :
    Code.Evaluates m bits p.program ⟨p.value, p.work, 0, 0, 0⟩ := by
  induction p with
  | emit r => intro F; rfl
  | step e next ih =>
    intro F
    rw [program, Code.evaluate_bind, Expr.evaluates]
    simp only [Code.evaluate]
    rw [ih]
    simp only [Outcome.combine, Outcome.add, Outcome.pure, value, work]
    congr 2 <;> omega

end Plan

def add (a b : ℕ) : Plan ℕ := .step (.add (.atom a) (.atom b)) .emit
def mul (a b : ℕ) : Plan ℕ := .step (.mul (.atom a) (.atom b)) .emit
def log (a : ℕ) : Plan ℕ := .step (.log (.atom a)) .emit
def sqrt (a : ℕ) : Plan ℕ := .step (.sqrt (.atom a)) .emit

/-- Every arithmetic field below is a literal instruction on inputs, constants, or
previous registers. The final emission only copies the 22 already-computed fields. -/
def setupPlan (n k : ℕ) : Plan PublicParameters := do
  let n2 ← add n 2
  let ln ← log n2
  let ell ← add 1 ln
  let sn ← sqrt n
  let tn ← add sn 1
  let heights ← mul heightFactor ell
  let hp ← add heights 1
  let hsquare ← mul hp hp
  let hcube ← mul hsquare hp
  let D ← mul 1000000 hcube
  let np ← add n 1
  let arg0 ← mul 8 np
  let arg ← mul arg0 D
  let lc ← log arg
  let clock ← add lc 1
  let trials ← mul 2 clock
  let privateClock ← mul k clock
  let trials1 ← add 1 trials
  let hc0 ← mul 3 trials1
  let hc ← add hc0 clock
  let mass0 ← mul heights trials
  let mass ← mul mass0 ell
  let a0 ← mul 505 hc
  let a1 ← mul 60000000000 mass
  let a2 ← add 1 a0
  let a ← add a2 a1
  let am0 ← mul 5000000000000005 hc
  let am1 ← mul 600000000000000000 mass
  let am2 ← add 1 am0
  let am ← add am2 am1
  let eps ← mul 1000000000 a
  let small ← mul 10 eps
  let band ← mul 400 a
  let mst ← mul 1000000000000000 am
  let xs ← mul 100 eps
  let xb ← mul 100000000 a
  let arg10 ← mul 512 tn
  let arg1 ← mul arg10 D
  let l1 ← log arg1
  let lb ← add l1 2
  let arg20 ← mul 128 np
  let arg21 ← mul arg20 tn
  let arg2 ← mul arg21 D
  let l2 ← log arg2
  let mb ← add l2 2
  let pool0 ← mul 512 tn
  let pool1 ← mul pool0 lb
  let pool ← mul pool1 mb
  let base ← mul 256 D
  let xs2 ← mul xs xs
  let ss ← mul base xs2
  let xb2 ← mul xb xb
  let sb ← mul base xb2
  let xm2 ← mul mst mst
  let sm ← mul base xm2
  let ps0 ← mul 16 ss
  let ps1 ← mul ps0 D
  let ps2 ← mul ps1 xs
  let ps ← add ps2 1
  let pls ← log ps
  let pcs ← add pls 1
  let caps ← mul k pcs
  let pb0 ← mul 16 sb
  let pb1 ← mul pb0 D
  let pb2 ← mul pb1 xb
  let pb ← add pb2 1
  let plb ← log pb
  let pcb ← add plb 1
  let capb ← mul k pcb
  let pm0 ← mul 16 sm
  let pm1 ← mul pm0 D
  let pm2 ← mul pm1 mst
  let pm ← add pm2 1
  let plm ← log pm
  let pcm ← add plm 1
  let capm ← mul k pcm
  pure ⟨tn, heights, D, trials, privateClock, clock, ell, a, am, small, band, mst, xs, xb, mst,
    pool, ss, sb, sm, caps, capb, capm⟩

end SteinerUpperBound.EstimatorParameters.Setup

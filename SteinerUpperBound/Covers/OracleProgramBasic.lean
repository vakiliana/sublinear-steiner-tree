module

public import SteinerUpperBound.QueryProgram.Loops
public import SteinerUpperBound.Covers.GlobalCap
public import SteinerUpperBound.Covers.ProposalCap

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V Q R M : Type*}

/-- Public array data. `Fin (k+1)` is the public terminal enumeration, not a
latent retained set. No instance or unknown metric callback occurs here. -/
structure Config (V Q : Type*) (k : ℕ) where
  label : Fin (k + 1) → V
  target : Q → Fin (k + 1)
  radius : Q → ℝ
  caps : Q → ℕ
  trials : Q → ℕ

structure State (Q : Type*) where
  cache : Q → Option Bool
  remaining : Option ℕ
  draws : ℕ
  newPositive : ℕ
  frontPositive : ℕ

namespace State

def initial (cache : Q → Option Bool) (D : ℕ) : State Q :=
  ⟨cache, some D, 0, 0, 0⟩

def draw (s : State Q) : State Q :=
  { s with remaining := s.remaining.map Nat.pred, draws := s.draws + 1 }

noncomputable def reply (s : State Q) (q : Q) (v : Bool) : State Q :=
  match s.cache q with
  | some _ => { s with frontPositive := s.frontPositive + if v then 1 else 0 }
  | none =>
      { s with
        cache := Function.update s.cache q (some v)
        newPositive := s.newPositive + if v then 1 else 0
        frontPositive := s.frontPositive + if v then 1 else 0 }

theorem reply_positive (s : State Q) (q : Q) (v : Bool)
    (h : s.newPositive ≤ s.frontPositive) :
    (s.reply q v).newPositive ≤ (s.reply q v).frontPositive := by
  classical
  cases he : s.cache q <;> simp only [reply, he] <;> omega

end State

structure Result (Q R : Type*) where
  value : Option R
  state : State Q

namespace Result

def done (r : R) (s : State Q) : Result Q R := ⟨some r, s⟩
def abort (s : State Q) : Result Q R := ⟨none, s⟩

end Result

/-- One private, on-demand scan. Every proposal is a fresh `uniform` node.
Bookkeeping ticks charge loop control, array access, comparisons, and updates.
Only the resolved bit is passed to the frontend continuation. -/
noncomputable def scan {k : ℕ} (cfg : Config V Q k) (q : Q) :
    ℕ → ℕ → State Q →
      (Bool → State Q → Code (Sym2 V) Q R) →
      (State Q → Code (Sym2 V) Q R) → Code (Sym2 V) Q R
  | 0, _, s, next, _ => .tick 1 (next false s)
  | _ + 1, 0, s, next, _ => .tick 1 (next false s)
  | B + 1, ψ + 1, s, next, abort =>
      .tick 7 (if s.remaining = some 0 then abort s else
        .uniform k (fun y => .tick 3
          (if y = cfg.target q then next true s.draw else
            .metric (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) (fun d =>
              .tick 3 (scan cfg q B (if d ≤ cfg.radius q then ψ else ψ + 1)
                s.draw next abort)))))

/-- The actual metric-query handler. Frontend metric, uniform, and coin nodes
remain in causal order; private draws never become frontend answers. -/
noncomputable def resolve {k : ℕ} (cfg : Config V Q k) :
    Code (Sym2 V) Q R → State Q → Code (Sym2 V) Q (Result Q R)
  | .pure r, s => .tick 0 (.pure (.done r s))
  | .metric q next, s => .tick 3 (.metric q (fun a => resolve cfg (next a) s))
  | .retained q next, s => .tick 3 (match s.cache q with
      | some v => .tick 3 (resolve cfg (next v) (s.reply q v))
      | none => scan cfg q (cfg.caps q) (cfg.trials q) s
          (fun v t => .tick 3 (resolve cfg (next v) (t.reply q v)))
          (fun t => .pure (.abort t)))
  | .uniform n next, s => .tick 3 (.uniform n (fun a => resolve cfg (next a) s))
  | .coin rate next, s => .tick 3 (.coin rate (fun a => resolve cfg (next a) s))
  | .tick n next, s => .tick n (.tick 3 (resolve cfg next s))

noncomputable def factory {k : ℕ} (cfg : Config V Q k) (cache : Q → Option Bool)
    (W D : ℕ) (p : Code (Sym2 V) Q R) :
    Code (Sym2 V) Q (Result Q (Option R)) :=
  resolve cfg (p.cap W) (State.initial cache D)

/-- Operational support, including zero-mass coin branches. This relation
accounts for the actual `Code` primitives and has no cost assumptions. -/
inductive Runs (m : M → ℝ) (b : Q → Bool) : Code M Q R → Outcome R → Prop
  | pure (r : R) : Runs m b (.pure r) (.pure r)
  | metric {q : M} {next : ℝ → Code M Q R} {o : Outcome R} :
      Runs m b (next (m q)) o → Runs m b (.metric q next) (o.add 1 1 0 0)
  | retained {q : Q} {next : Bool → Code M Q R} {o : Outcome R} :
      Runs m b (next (b q)) o →
        Runs m b (.retained q next) (o.add 1 0 1 (if b q then 1 else 0))
  | uniform {n : ℕ} {next : Fin (n + 1) → Code M Q R} {o : Outcome R}
      (a : Fin (n + 1)) :
      Runs m b (next a) o → Runs m b (.uniform n next) (o.add 1 0 0 0)
  | coin {rate : Rate} {next : Bool → Code M Q R} {o : Outcome R} (a : Bool) :
      Runs m b (next a) o → Runs m b (.coin rate next) (o.add 2 0 0 0)
  | tick {n : ℕ} {next : Code M Q R} {o : Outcome R} :
      Runs m b next o → Runs m b (.tick n next) (o.add (n + 1) 0 0 0)

theorem runs_compile (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) :
    ∀ s : (p.compile m).Seed, Runs m b p (((p.compile m).tree s).output b) := by
  induction p with
  | pure r =>
    intro _
    exact Runs.pure r
  | metric q next ih =>
    intro s
    simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using
      Runs.metric (ih (m q) s)
  | retained q next ih =>
    intro s
    cases hb : b q with
    | false =>
      have hr : Runs m b (.retained q next)
          (((((next false).compile m).tree s.1).output b).add 1 0 1 (if b q then 1 else 0)) := by
        apply Runs.retained
        simpa only [hb] using ih false s.1
      simpa only [Code.compile, Compiled.query, DecisionTree.output, hb, Bool.false_eq_true,
        ite_false, Compiled.map, DecisionTree.output_map] using hr
    | true =>
      have hr : Runs m b (.retained q next)
          (((((next true).compile m).tree s.2).output b).add 1 0 1 (if b q then 1 else 0)) := by
        apply Runs.retained
        simpa only [hb] using ih true s.2
      simpa only [Code.compile, Compiled.query, DecisionTree.output, hb, ite_true,
        Compiled.map, DecisionTree.output_map] using hr
  | uniform n next ih =>
    intro s
    simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
      Runs.uniform s.1 (ih s.1 s.2)
  | coin rate next ih =>
    intro s
    simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
      Runs.coin s.1 (ih s.1 s.2)
  | tick n next ih =>
    intro s
    simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using Runs.tick (ih s)

end SteinerUpperBound.Covers.OracleProgram

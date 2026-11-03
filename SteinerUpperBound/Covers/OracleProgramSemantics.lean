module

public import SteinerUpperBound.Covers.OracleProgramResources

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V Q R S : Type*} {k : ℕ}

namespace Result

def map (f : R → S) (r : Result Q R) : Result Q S := ⟨r.value.map f, r.state⟩

@[simp] theorem map_done (f : R → S) (r : R) (s : State Q) :
    (done r s).map f = done (f r) s := rfl

@[simp] theorem map_abort (f : R → S) (s : State Q) :
    (abort s : Result Q R).map f = abort s := rfl

theorem map_outcome_add (r : Result Q (Outcome R)) (w m q z : ℕ) :
    (r.map (Outcome.add w m q z)).map Outcome.value = r.map Outcome.value := by
  rcases r with ⟨value, state⟩
  cases value <;> rfl

end Result

/-- Analysis-only closure of actual metric query answers. This function is not
an input of the runtime code. -/
def relation (cfg : Config V Q k) (m : Sym2 V → ℝ) (q : Q)
    (x y : Fin (k + 1)) : Prop :=
  m (Sym2.mk (cfg.label x) (cfg.label y)) ≤ cfg.radius q

noncomputable def scanValue (cfg : Config V Q k) (m : Sym2 V → ℝ) (q : Q) :
    ℕ → ℕ → State Q → (Bool → State Q → ℝ) → (State Q → ℝ) → ℝ
  | 0, _, s, next, _ => next false s
  | _ + 1, 0, s, next, _ => next false s
  | B + 1, ψ + 1, s, next, abort =>
      if s.remaining = some 0 then abort s else
        (Law.uniform (Fin (k + 1))).expect (fun y =>
          if y = cfg.target q then next true s.draw else
            scanValue cfg m q B
              (if m (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) ≤ cfg.radius q
                then ψ else ψ + 1) s.draw next abort)

theorem scan_evaluate (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (q : Q) (B ψ : ℕ) (s : State Q)
    (next : Bool → State Q → Code (Sym2 V) Q R)
    (abort : State Q → Code (Sym2 V) Q R) (F : R → ℝ) :
    (scan cfg q B ψ s next abort).evaluate m b (fun o => F o.value) =
      scanValue cfg m q B ψ s
        (fun v t => (next v t).evaluate m b (fun o => F o.value))
        (fun t => (abort t).evaluate m b (fun o => F o.value)) := by
  induction B generalizing ψ s with
  | zero => rfl
  | succ B ih =>
    cases ψ with
    | zero => rfl
    | succ ψ =>
      by_cases hs : s.remaining = some 0
      · simp only [scan, scanValue, hs, ite_true, Code.evaluate, Outcome.add]
      · simp only [scan, scanValue, hs, ite_false, Code.evaluate, Outcome.add]
        apply congrArg (Law.uniform (Fin (k + 1))).expect
        funext y
        by_cases hy : y = cfg.target q
        · simp only [hy, ite_true]
        · simp only [hy, ite_false, Code.evaluate, Outcome.add]
          exact ih _ s.draw

noncomputable def treeValue (cfg : Config V Q k) (m : Sym2 V → ℝ) :
    DecisionTree Q Bool R → State Q → (Result Q R → ℝ) → ℝ
  | .leaf r, s, F => F (.done r s)
  | .query q next, s, F =>
      match s.cache q with
      | some v => treeValue cfg m (next v) (s.reply q v) F
      | none => scanValue cfg m q (cfg.caps q) (cfg.trials q) s
          (fun v t => treeValue cfg m (next v) (t.reply q v) F)
          (fun t => F (.abort t))

noncomputable def codeValue (cfg : Config V Q k) (m : Sym2 V → ℝ) :
    Code (Sym2 V) Q R → State Q → (Result Q R → ℝ) → ℝ
  | .pure r, s, F => F (.done r s)
  | .metric q next, s, F => codeValue cfg m (next (m q)) s F
  | .retained q next, s, F =>
      match s.cache q with
      | some v => codeValue cfg m (next v) (s.reply q v) F
      | none => scanValue cfg m q (cfg.caps q) (cfg.trials q) s
          (fun v t => codeValue cfg m (next v) (t.reply q v) F)
          (fun t => F (.abort t))
  | .uniform n next, s, F =>
      (Law.uniform (Fin (n + 1))).expect (fun a => codeValue cfg m (next a) s F)
  | .coin rate next, s, F =>
      (CategoricalCoupling.bernoulli rate).expect (fun a => codeValue cfg m (next a) s F)
  | .tick _ next, s, F => codeValue cfg m next s F

theorem resolve_evaluate (cfg : Config V Q k) (m : Sym2 V → ℝ) (b : Q → Bool)
    (p : Code (Sym2 V) Q R) (s : State Q) (F : Result Q R → ℝ) :
    (resolve cfg p s).evaluate m b (fun o => F o.value) = codeValue cfg m p s F := by
  induction p generalizing s with
  | pure => rfl
  | metric q next ih => exact ih (m q) s
  | retained q next ih =>
    simp only [resolve, Code.evaluate, Outcome.add, codeValue]
    cases he : s.cache q with
    | some v =>
      simpa only [he, Code.evaluate, Outcome.add] using ih v (s.reply q v)
    | none =>
      simp only [he]
      rw [scan_evaluate]
      have hnext :
          (fun (v : Bool) (t : State Q) => (Code.tick 3 (resolve cfg (next v) (t.reply q v))).evaluate m b
            (fun o => F o.value)) =
          (fun (v : Bool) (t : State Q) => codeValue cfg m (next v) (t.reply q v) F) := by
        funext v t
        exact ih v (t.reply q v)
      rw [hnext]
      rfl
  | uniform n next ih =>
    apply congrArg (Law.uniform (Fin (n + 1))).expect
    funext a
    exact ih a s
  | coin rate next ih =>
    simp only [resolve, Code.evaluate, Outcome.add, codeValue]
    apply congrArg (CategoricalCoupling.bernoulli rate).expect
    funext a
    exact ih a s
  | tick n next ih => exact ih s

theorem expect_comm {A B : Type*} [Fintype A] [Fintype B]
    (μ : Law A) (ν : Law B) (F : A → B → ℝ) :
    μ.expect (fun a => ν.expect (F a)) = ν.expect (fun b => μ.expect (fun a => F a b)) := by
  simp only [Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scanValue_expect {A : Type} [Fintype A]
    (cfg : Config V Q k) (m : Sym2 V → ℝ) (q : Q) (B ψ : ℕ) (s : State Q)
    (μ : Law A) (next : A → Bool → State Q → ℝ) (abort : A → State Q → ℝ) :
    μ.expect (fun a => scanValue cfg m q B ψ s (next a) (abort a)) =
      scanValue cfg m q B ψ s (fun v t => μ.expect (fun a => next a v t))
        (fun t => μ.expect (fun a => abort a t)) := by
  induction B generalizing ψ s with
  | zero => rfl
  | succ B ih =>
    cases ψ with
    | zero => rfl
    | succ ψ =>
      by_cases hs : s.remaining = some 0
      · simp only [scanValue, hs, ite_true]
      · simp only [scanValue, hs, ite_false]
        rw [expect_comm]
        apply congrArg (Law.uniform (Fin (k + 1))).expect
        funext y
        by_cases hy : y = cfg.target q
        · simp only [hy, ite_true]
        · simp only [hy, ite_false]
          exact ih _ s.draw

theorem treeValue_map (cfg : Config V Q k) (m : Sym2 V → ℝ) (t : DecisionTree Q Bool R)
    (f : R → S) (s : State Q) (F : Result Q S → ℝ) :
    treeValue cfg m (t.map f) s F =
      treeValue cfg m t s (fun r => F (r.map f)) := by
  induction t generalizing s with
  | leaf => rfl
  | query q next ih =>
    simp only [DecisionTree.map, treeValue]
    cases he : s.cache q with
    | some v => simpa only [he] using ih v (s.reply q v)
    | none =>
      simp only [he]
      congr 1
      funext v t
      exact ih v (t.reply q v)

noncomputable def compiledValue (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (c : Compiled Q R) (s : State Q) (F : Result Q R → ℝ) : ℝ :=
  c.law.expect (fun seed => treeValue cfg m (c.tree seed) s F)

theorem compiledValue_map (cfg : Config V Q k) (m : Sym2 V → ℝ) (c : Compiled Q R)
    (f : R → S) (s : State Q) (F : Result Q S → ℝ) :
    compiledValue cfg m (c.map f) s F =
      compiledValue cfg m c s (fun r => F (r.map f)) := by
  unfold compiledValue
  apply congrArg c.law.expect
  funext seed
  exact treeValue_map cfg m _ f s F

theorem compiledValue_choose {A : Type} [Fintype A]
    (cfg : Config V Q k) (m : Sym2 V → ℝ) (μ : Law A) (c : A → Compiled Q R)
    (s : State Q) (F : Result Q R → ℝ) :
    compiledValue cfg m (Compiled.choose μ c) s F =
      μ.expect (fun a => compiledValue cfg m (c a) s F) := by
  exact Seeds.expect_dependent μ (fun a => (c a).law)
    (fun seed => treeValue cfg m ((c seed.1).tree seed.2) s F)

theorem compiledValue_query (cfg : Config V Q k) (m : Sym2 V → ℝ) (q : Q)
    (c : Bool → Compiled Q R) (s : State Q) (F : Result Q R → ℝ) :
    compiledValue cfg m (Compiled.query q (c false) (c true)) s F =
      match s.cache q with
      | some v => compiledValue cfg m (c v) (s.reply q v) F
      | none => scanValue cfg m q (cfg.caps q) (cfg.trials q) s
          (fun v t => compiledValue cfg m (c v) (t.reply q v) F)
          (fun t => F (.abort t)) := by
  classical
  have hbranch (v : Bool) (t : State Q) :
      (Seeds.product (c false).law (c true).law).expect (fun seed =>
        treeValue cfg m (if v then (c true).tree seed.2 else (c false).tree seed.1)
          (t.reply q v) F) =
        compiledValue cfg m (c v) (t.reply q v) F := by
    cases v <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals rw [Seeds.expect_product]
    all_goals simp only [Law.expect_const, compiledValue]
  unfold compiledValue
  simp only [Compiled.query, treeValue]
  cases he : s.cache q with
  | some v =>
    simpa only [he, compiledValue] using hbranch v s
  | none =>
    simp only [he]
    rw [scanValue_expect]
    have hn :
        (fun (v : Bool) (t : State Q) => (Seeds.product (c false).law (c true).law).expect (fun seed =>
          treeValue cfg m (if v then (c true).tree seed.2 else (c false).tree seed.1)
            (t.reply q v) F)) =
        (fun (v : Bool) (t : State Q) => compiledValue cfg m (c v) (t.reply q v) F) := by
      funext v t
      exact hbranch v t
    rw [hn]
    congr 1
    funext t
    exact Law.expect_const _ _

/-- Finite frontend seeds can be fixed only in analysis. Their law includes all
adaptive coin branches and is independent of the unresolved retention vector.
The actual runtime still samples each frontend and factory draw on demand. -/
theorem compile_handler (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (p : Code (Sym2 V) Q R) (s : State Q) (F : Result Q R → ℝ) :
    compiledValue cfg m (p.compile m) s (fun r => F (r.map Outcome.value)) =
      codeValue cfg m p s F := by
  induction p generalizing s with
  | pure r =>
    exact Law.expect_const _ _
  | metric q next ih =>
    rw [Code.compile, compiledValue_map]
    simp_rw [Result.map_outcome_add]
    exact ih (m q) s
  | retained q next ih =>
    let c : Bool → Compiled Q (Outcome R) := fun v =>
      ((next v).compile m).map (Outcome.add 1 0 1 (if v then 1 else 0))
    have hc (v : Bool) (t : State Q) :
        compiledValue cfg m (c v) t (fun r => F (r.map Outcome.value)) =
          codeValue cfg m (next v) t F := by
      rw [show c v = ((next v).compile m).map (Outcome.add 1 0 1 (if v then 1 else 0)) from rfl,
        compiledValue_map]
      simp_rw [Result.map_outcome_add]
      exact ih v t
    change compiledValue cfg m (Compiled.query q (c false) (c true)) s _ = _
    rw [compiledValue_query]
    simp only [codeValue]
    cases he : s.cache q with
    | some v => simpa only [he] using hc v (s.reply q v)
    | none =>
      simp only [he]
      have hn : (fun (v : Bool) (t : State Q) => compiledValue cfg m (c v) (t.reply q v)
          (fun r => F (r.map Outcome.value))) =
          (fun (v : Bool) (t : State Q) => codeValue cfg m (next v) (t.reply q v) F) := by
        funext v t
        exact hc v (t.reply q v)
      rw [hn]
      rfl
  | uniform n next ih =>
    rw [Code.compile, compiledValue_map]
    simp_rw [Result.map_outcome_add]
    rw [compiledValue_choose]
    apply congrArg (Law.uniform (Fin (n + 1))).expect
    funext a
    exact ih a s
  | coin rate next ih =>
    rw [Code.compile, compiledValue_map]
    simp_rw [Result.map_outcome_add]
    rw [compiledValue_choose]
    apply congrArg (CategoricalCoupling.bernoulli rate).expect
    funext a
    exact ih a s
  | tick n next ih =>
    rw [Code.compile, compiledValue_map]
    simp_rw [Result.map_outcome_add]
    exact ih s

end SteinerUpperBound.Covers.OracleProgram

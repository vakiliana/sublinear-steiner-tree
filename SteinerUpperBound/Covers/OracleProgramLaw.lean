module

public import SteinerUpperBound.Covers.OracleProgramTail

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {V Q R : Type*} {k : ℕ}

/-- Exact law of the actual causal code, averaged over the frontend's checked
finite seed law. The seed compilation is an analysis device, not runtime tape
generation. This equation permits arbitrary real-valued tests and outputs. -/
theorem factory_compiled_evaluate (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (F : Result Q (Option R) → ℝ) :
    (factory cfg cache W D p).evaluate m b (fun o => F o.value) =
      ((p.cap W).compile m).law.expect (fun seed =>
        treeValue cfg m ((((p.cap W).compile m).tree seed).map Outcome.value)
          (State.initial cache D) F) := by
  rw [show factory cfg cache W D p = resolve cfg (p.cap W) (State.initial cache D) from rfl,
    resolve_evaluate, ← compile_handler]
  unfold compiledValue
  apply congrArg ((p.cap W).compile m).law.expect
  funext seed
  exact (treeValue_map cfg m _ Outcome.value _ F).symm

theorem tree_boolean_close [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (D : ℕ) (test : R → Bool) :
    |treeValue cfg m t (State.initial cache D)
        (fun r => if r.value.map test = some true then 1 else 0) -
      (bits cfg m cache).prob {oracle | test (t.output oracle) = true}| ≤
      treeValue cfg m t (State.initial cache D) (fun r => if r.value = none then 1 else 0) := by
  classical
  let t' := t.map test
  let start : Factory.State Q (Fin (k + 1)) Bool :=
    (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t' cache),
      Factory.initiallyRetained cache)
  have hc := Factory.global_capped_law_close cfg.target (relation cfg m) cfg.caps cfg.trials
    t' cache D
  have ha :
      treeValue cfg m t' (State.initial cache D)
        (fun r => if r.value = some true then 1 else 0) =
      ((tape (Law.uniform (Fin (k + 1))) D).map
        (fun w => Factory.output (Factory.run cfg.target D start w))).prob {some true} := by
    rw [treeValue_capped_law cfg m t' cache D
      (fun value _ => if value = some true then 1 else 0), Law.prob_map, Law.prob_eq_expect]
    apply congrArg (tape (Law.uniform (Fin (k + 1))) D).expect
    funext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, start]
  have hr :
      ((bits cfg m cache).map (fun oracle => some (t'.output oracle))).prob {some true} =
        (bits cfg m cache).prob {oracle | test (t.output oracle) = true} := by
    rw [Law.prob_map]
    apply congrArg (bits cfg m cache).prob
    ext oracle
    simp [t', DecisionTree.output_map]
  have hp :
      treeValue cfg m t' (State.initial cache D) (fun r => if r.value = none then 1 else 0) =
        (tape (Law.uniform (Fin (k + 1))) D).prob
          {w | Factory.Pending (Factory.run cfg.target D start w)} := by
    rw [treeValue_capped_law cfg m t' cache D (fun value _ => if value = none then 1 else 0),
      Law.prob_eq_expect]
    apply congrArg (tape (Law.uniform (Fin (k + 1))) D).expect
    funext w
    simp only [Set.mem_ofPred_eq, Factory.output_none_iff, start]
  have h := hc ({some true} : Set (Option Bool))
  change |((tape (Law.uniform (Fin (k + 1))) D).map
      (fun w => Factory.output (Factory.run cfg.target D start w))).prob {some true} -
    ((bits cfg m cache).map (fun oracle => some (t'.output oracle))).prob {some true}| ≤ _ at h
  rw [← ha, hr, ← hp] at h
  rw [treeValue_map] at h
  have hp' :
      (fun r : Result Q R => if (r.map test).value = none then (1 : ℝ) else 0) =
      (fun r => if r.value = none then 1 else 0) := by
    funext r
    cases he : r.value <;> simp [Result.map, he]
  rw [treeValue_map, hp'] at h
  exact h

/-- Boolean-observable total-variation formulation. It avoids any `Fintype`
assumption on frontend outputs, including `ℝ`. All adaptive frontend randomness
is integrated through its real runtime evaluation. -/
theorem factory_boolean_close [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (test : Option R → Bool) :
    |(factory cfg cache W D p).evaluate m b
        (fun o => if o.value.value.map test = some true then 1 else 0) -
      (bits cfg m cache).expect (fun oracle =>
        (p.cap W).evaluate m oracle (fun o => if test o.value = true then 1 else 0))| ≤
      (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then 1 else 0) := by
  classical
  let c := (p.cap W).compile m
  let f := fun seed : c.Seed => treeValue cfg m ((c.tree seed).map Outcome.value)
    (State.initial cache D) (fun r => if r.value.map test = some true then (1 : ℝ) else 0)
  let g := fun seed : c.Seed => (bits cfg m cache).prob
    {oracle | test (((c.tree seed).output oracle).value) = true}
  let h := fun seed : c.Seed => treeValue cfg m ((c.tree seed).map Outcome.value)
    (State.initial cache D) (fun r => if r.value = none then (1 : ℝ) else 0)
  have hfg : ∀ seed, |f seed - g seed| ≤ h seed := by
    intro seed
    simpa only [f, g, h, DecisionTree.output_map] using
      tree_boolean_close cfg m ((c.tree seed).map Outcome.value) cache D test
  have ha : (factory cfg cache W D p).evaluate m b
      (fun o => if o.value.value.map test = some true then 1 else 0) = c.law.expect f :=
    factory_compiled_evaluate cfg m b cache W D p
      (fun r => if r.value.map test = some true then 1 else 0)
  have hp : (factory cfg cache W D p).evaluate m b
      (fun o => if o.value.value = none then 1 else 0) = c.law.expect h :=
    factory_compiled_evaluate cfg m b cache W D p (fun r => if r.value = none then 1 else 0)
  have hr : (bits cfg m cache).expect (fun oracle =>
        (p.cap W).evaluate m oracle (fun o => if test o.value = true then 1 else 0)) =
      c.law.expect g := by
    unfold g
    simp_rw [Law.prob_eq_expect]
    rw [expect_comm]
    apply congrArg (bits cfg m cache).expect
    funext oracle
    calc
      _ = c.expect oracle (fun o => if test o.value = true then 1 else 0) :=
        (Code.compile_expect m oracle (p.cap W) _).symm
      _ = _ := by
        unfold Compiled.expect
        apply congrArg c.law.expect
        funext seed
        by_cases ht : test ((c.tree seed).output oracle).value = true <;>
          simp only [Set.mem_ofPred_eq, ht, ite_true, ite_false]
  rw [ha, hr, hp, ← Law.expect_sub]
  exact (c.law.abs_expect_le _).trans (c.law.expect_mono hfg)

theorem evaluate_boolean_not {M : Type*} (m : M → ℝ) (b : Q → Bool)
    (p : Code M Q R) (test : Outcome R → Bool) :
    p.evaluate m b (fun o => if (!test o) = true then (1 : ℝ) else 0) =
      1 - p.evaluate m b (fun o => if test o = true then 1 else 0) := by
  have hf :
      (fun o => if (!test o) = true then (1 : ℝ) else 0) =
        (fun o => 1 - if test o = true then 1 else 0) := by
    funext o
    cases test o <;> norm_num
  rw [hf, ← Code.compile_expect, ← Code.compile_expect]
  unfold Compiled.expect
  rw [Law.expect_sub, Law.expect_const]

/-- Total output-law comparison, including events that count global abort as
true. The reference result has one extra `some`, since it never globally aborts.
No finiteness assumption is imposed on frontend outputs. -/
theorem factory_option_boolean_close [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (test : Option (Option R) → Bool) :
    |(factory cfg cache W D p).evaluate m b
        (fun o => if test o.value.value = true then 1 else 0) -
      (bits cfg m cache).expect (fun oracle =>
        (p.cap W).evaluate m oracle (fun o => if test (some o.value) = true then 1 else 0))| ≤
      (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then 1 else 0) := by
  classical
  have hfalse (f : Option (Option R) → Bool) (hf : f none = false) :
      |(factory cfg cache W D p).evaluate m b
          (fun o => if f o.value.value = true then (1 : ℝ) else 0) -
        (bits cfg m cache).expect (fun oracle =>
          (p.cap W).evaluate m oracle (fun o => if f (some o.value) = true then 1 else 0))| ≤
        (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then 1 else 0) := by
    have h := factory_boolean_close cfg m b cache W D p (fun r => f (some r))
    have he :
        (fun o : Outcome (Result Q (Option R)) =>
          if o.value.value.map (fun r => f (some r)) = some true then (1 : ℝ) else 0) =
        (fun o => if f o.value.value = true then 1 else 0) := by
      funext o
      cases hv : o.value.value with
      | none => simp [hv, hf]
      | some r => cases hr : f (some r) <;> simp [hv, hr]
    rw [he] at h
    exact h
  cases hnone : test none with
  | false => exact hfalse test hnone
  | true =>
    have h := hfalse (fun r => !test r) (by simp [hnone])
    have ha := evaluate_boolean_not m b (factory cfg cache W D p)
      (fun o => test o.value.value)
    have hr :
        (bits cfg m cache).expect (fun oracle =>
          (p.cap W).evaluate m oracle (fun o => if (!test (some o.value)) = true then (1 : ℝ) else 0)) =
        1 - (bits cfg m cache).expect (fun oracle =>
          (p.cap W).evaluate m oracle (fun o => if test (some o.value) = true then 1 else 0)) := by
      simp_rw [evaluate_boolean_not]
      rw [Law.expect_sub, Law.expect_const]
    rw [ha, hr] at h
    have he (x y : ℝ) : (1 - x) - (1 - y) = -(x - y) := by ring
    simpa only [he, abs_neg] using h

/-- Both abort kinds can be flattened into `none` while preserving the same
total-variation error, not twice that error. -/
theorem factory_output_boolean_close [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ) (p : Code (Sym2 V) Q R)
    (test : Option R → Bool) :
    |(factory cfg cache W D p).evaluate m b
        (fun o => if test o.value.value.join = true then 1 else 0) -
      (bits cfg m cache).expect (fun oracle =>
        (p.cap W).evaluate m oracle (fun o => if test o.value = true then 1 else 0))| ≤
      (factory cfg cache W D p).evaluate m b (fun o => if o.value.value = none then 1 else 0) :=
  factory_option_boolean_close cfg m b cache W D p (fun r => test r.join)

end SteinerUpperBound.Covers.OracleProgram

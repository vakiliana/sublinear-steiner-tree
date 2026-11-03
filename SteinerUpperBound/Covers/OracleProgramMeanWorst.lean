module

public import SteinerUpperBound.Covers.OracleProgramMeanResources

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram.Mean

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q R U A : Type*}

theorem compiled_nonempty (c : Compiled Q R) : Nonempty c.Seed := by
  have h : ∃ seed, 0 < c.law.mass seed := by
    by_contra hn
    push Not at hn
    have hs : (∑ seed, c.law.mass seed) ≤ 0 := Finset.sum_nonpos (fun seed _ => hn seed)
    rw [c.law.total] at hs
    norm_num at hs
  exact ⟨h.choose⟩

/-- Operational bounds and refinements can be supplied using the parent's
usual every-compiled-seed interfaces, including zero-mass coin branches. -/
theorem runs_compiled_seed (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (o : Outcome R) (ho : Runs m b p o) :
    ∃ seed : (p.compile m).Seed, ((p.compile m).tree seed).output b = o := by
  induction p generalizing o with
  | pure r =>
    cases ho
    exact ⟨(), rfl⟩
  | metric q next ih =>
    cases ho with
    | metric ho =>
      obtain ⟨seed, hs⟩ := ih (m q) _ ho
      exact ⟨seed, by simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using
        (congrArg (Outcome.add 1 1 0 0) hs)⟩
  | retained q next ih =>
    cases ho with
    | retained ho =>
      cases hb : b q with
      | false =>
        rw [hb] at ho
        obtain ⟨seed, hs⟩ := ih false _ ho
        let other := Classical.choice (compiled_nonempty ((next true).compile m))
        refine ⟨(seed, other), ?_⟩
        simpa only [Code.compile, Compiled.query, DecisionTree.output, hb, Bool.false_eq_true,
          ite_false, Compiled.map, DecisionTree.output_map] using
          (congrArg (Outcome.add 1 0 1 0) hs)
      | true =>
        rw [hb] at ho
        obtain ⟨seed, hs⟩ := ih true _ ho
        let other := Classical.choice (compiled_nonempty ((next false).compile m))
        refine ⟨(other, seed), ?_⟩
        simpa only [Code.compile, Compiled.query, DecisionTree.output, hb, ite_true,
          Compiled.map, DecisionTree.output_map] using congrArg (Outcome.add 1 0 1 1) hs
  | uniform n next ih =>
    cases ho with
    | uniform u ho =>
      obtain ⟨seed, hs⟩ := ih u _ ho
      exact ⟨⟨u, seed⟩, by
        simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
          (congrArg (Outcome.add 1 0 0 0) hs)⟩
  | coin rate next ih =>
    cases ho with
    | coin u ho =>
      obtain ⟨seed, hs⟩ := ih u _ ho
      exact ⟨⟨u, seed⟩, by
        simpa only [Code.compile, Compiled.map, Compiled.choose, DecisionTree.output_map] using
          (congrArg (Outcome.add 2 0 0 0) hs)⟩
  | tick n next ih =>
    cases ho with
    | tick ho =>
      obtain ⟨seed, hs⟩ := ih _ ho
      exact ⟨seed, by simpa only [Code.compile, Compiled.map, DecisionTree.output_map] using
        (congrArg (Outcome.add (n + 1) 0 0 0) hs)⟩

theorem runs_of_compiled (m : M → ℝ) (b : Q → Bool) (p : Code M Q R)
    (P : Outcome R → Prop) (h : ∀ seed, P (((p.compile m).tree seed).output b)) :
    ∀ o, Runs m b p o → P o := by
  intro o ho
  obtain ⟨seed, rfl⟩ := runs_compiled_seed m b p o ho
  exact h seed

theorem KernelSpec.of_compiled [Fintype A] (callback : Callback M Q U)
    (m : M → ℝ) (b : Q → Bool) (kernel : U → Law A) (score : U → A → ℝ)
    (hcache : ∀ u c, Cache.Correct b c → ∀ seed,
      Cache.Correct b ((((callback u c).compile m).tree seed).output b).value.2)
    (hlaw : ∀ u c, Cache.Correct b c → ∀ F : ℝ → ℝ,
      (callback u c).evaluate m b (fun o => F o.value.1) =
        (kernel u).expect (fun a => F (score u a))) :
    KernelSpec callback m b kernel score :=
  ⟨fun u c hc => runs_of_compiled m b (callback u c)
    (fun o => Cache.Correct b o.value.2) (hcache u c hc), hlaw⟩

theorem KernelSpec.of_deterministic_compiled (callback : Callback M Q U)
    (m : M → ℝ) (b : Q → Bool) (score : U → ℝ)
    (hcache : ∀ u c, Cache.Correct b c → ∀ seed,
      Cache.Correct b ((((callback u c).compile m).tree seed).output b).value.2)
    (hlaw : ∀ u c, Cache.Correct b c → ∀ F : ℝ → ℝ,
      (callback u c).evaluate m b (fun o => F o.value.1) = F (score u)) :
    KernelSpec callback m b (fun _ => Law.pure ()) (fun u _ => score u) :=
  KernelSpec.of_deterministic callback m b score
    (fun u c hc => runs_of_compiled m b (callback u c)
      (fun o => Cache.Correct b o.value.2) (hcache u c hc)) hlaw

theorem scores_worst [Fintype A] {callback : Callback M Q U}
    {m : M → ℝ} {b : Q → Bool} {kernel : U → Law A} {score : U → A → ℝ}
    (h : KernelSpec callback m b kernel score) (W P : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.work ≤ W)
    (hp : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.positiveReplies ≤ P)
    (s : ℕ) (labels : Fin s → U) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs m b (scores callback s labels c) o →
      o.work ≤ (W + 6) * s + 2 ∧ o.positiveReplies ≤ P * s := by
  induction s generalizing c with
  | zero =>
    intro o ho
    rw [scores] at ho
    cases ho with
    | tick ho => cases ho; simp [Outcome.add, Outcome.pure]
  | succ s ih =>
    intro o ho
    rw [scores] at ho
    cases ho with
    | tick ho =>
      obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (callback (labels 0) c) _ _ ho
      have haw := hw (labels 0) c hc a ha
      have hap := hp (labels 0) c hc a ha
      have hac := h.cache_correct (labels 0) c hc a ha
      obtain ⟨a', z', ha', hz', rfl⟩ := runs_bind_inv m b
        (scores callback s (Fin.tail labels) a.value.2) _ _ hz
      have ht := ih (Fin.tail labels) a.value.2 hac a' ha'
      cases hz' with
      | tick hz' =>
        cases hz'
        simp only [Outcome.add, Outcome.combine, Outcome.pure] at *
        constructor <;> nlinarith

theorem afterSample_worst [Fintype A] {k s : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score) (W P : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.work ≤ W)
    (hp : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.positiveReplies ≤ P)
    (ξ : ℝ) (r : Sampler.Records Q k s) (hc : Cache.Correct b r.store.cache) :
    ∀ o, Runs m b (afterSample ξ callback r) o →
      o.work ≤ (W + 6) * s + 42 ∧ o.positiveReplies ≤ P * s := by
  intro o ho
  rw [afterSample] at ho
  cases ho with
  | tick ho =>
    cases he : r.labels with
    | none =>
      simp only [he] at ho
      cases ho with
      | tick ho => cases ho; simp [Outcome.add, Outcome.pure]
    | some labels =>
      simp only [he] at ho
      cases hs : r.successful with
      | false =>
        simp only [hs, Bool.false_eq_true, ite_false] at ho
        cases ho with
        | tick ho => cases ho; simp [Outcome.add, Outcome.pure]
      | true =>
        simp only [hs, ite_true] at ho
        obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (scores callback s labels r.store.cache) _ _ ho
        have hres := scores_worst h W P hw hp s labels r.store.cache hc a ha
        cases hz with
        | tick hz =>
          cases hz
          simp only [Outcome.add, Outcome.combine, Outcome.pure] at *
          omega

/-- Deterministic worst-case accounts include actual proposals, callback
invocations, arithmetic, and fresh positive replies on every execution. -/
theorem program_worst [Fintype A] {k : ℕ} {callback : Callback M Q (Fin (k + 1))}
    {m : M → ℝ} {b : Q → Bool} {kernel : Fin (k + 1) → Law A}
    {score : Fin (k + 1) → A → ℝ} (h : KernelSpec callback m b kernel score)
    (W P : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.work ≤ W)
    (hp : ∀ u c, Cache.Correct b c → ∀ o, Runs m b (callback u c) o → o.positiveReplies ≤ P)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c) (ξ : ℝ) :
    ∀ o, Runs m b (program query root C s B c ξ callback) o →
      o.work ≤ 64 * (o.value.sample.store.proposals + s + 1) + W * s ∧
      o.positiveReplies ≤ (P + 1) * s ∧ o.value.sample.store.proposals ≤ B := by
  intro o ho
  obtain ⟨a, z, ha, hz, rfl⟩ := runs_bind_inv m b (Sampler.program query root C s B c) _ _ ho
  have hsamp := Sampler.pool_resources m b query root C s (Sampler.Store.initial c B) a ha
  have hc' := sampler_cache_correct m b query root C s B c hc a ha
  have hscore := afterSample_worst h W P hw hp ξ a.value hc' z hz
  have hfields := afterSample_fields m b ξ callback a.value z hz
  simp only [Sampler.Store.initial, Nat.sub_zero, Nat.zero_add] at hsamp
  simp only [Outcome.combine, hfields.1]
  constructor
  · nlinarith [hsamp.2.2.2.2.1, hscore.1]
  constructor
  · nlinarith [hsamp.2.2.2.1, hscore.2]
  · omega

theorem program_compiled_worst [Fintype A] {k : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score) (W P : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ seed,
      ((((callback u c).compile m).tree seed).output b).work ≤ W)
    (hp : ∀ u c, Cache.Correct b c → ∀ seed,
      ((((callback u c).compile m).tree seed).output b).positiveReplies ≤ P)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c) (ξ : ℝ)
    (seed : ((program query root C s B c ξ callback).compile m).Seed) :
    let o := (((program query root C s B c ξ callback).compile m).tree seed).output b
    o.work ≤ 64 * (B + s + 1) + W * s ∧ o.positiveReplies ≤ (P + 1) * s := by
  have hr := program_worst h W P
    (fun u c hc => runs_of_compiled m b (callback u c) (fun o => o.work ≤ W) (hw u c hc))
    (fun u c hc => runs_of_compiled m b (callback u c) (fun o => o.positiveReplies ≤ P) (hp u c hc))
    query root C s B c hc ξ _ (runs_compile m b (program query root C s B c ξ callback) seed)
  dsimp only
  constructor
  · omega
  · exact hr.2.1

theorem program_compiled_work [Fintype A] {k : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score) (W : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ seed,
      ((((callback u c).compile m).tree seed).output b).work ≤ W)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c) (ξ : ℝ)
    (seed : ((program query root C s B c ξ callback).compile m).Seed) :
    ((((program query root C s B c ξ callback).compile m).tree seed).output b).work ≤
      64 * (B + s + 1) + W * s := by
  have hp : ∀ u c, Cache.Correct b c → ∀ seed,
      ((((callback u c).compile m).tree seed).output b).positiveReplies ≤ W := by
    intro u c hc seed
    have ha := Code.accounted m b (callback u c) seed
    have hb := hw u c hc seed
    omega
  exact (program_compiled_worst h W W hw hp query root C s B c hc ξ seed).1

theorem program_cap_evaluate [Fintype A] {k : ℕ}
    {callback : Callback M Q (Fin (k + 1))} {m : M → ℝ} {b : Q → Bool}
    {kernel : Fin (k + 1) → Law A} {score : Fin (k + 1) → A → ℝ}
    (h : KernelSpec callback m b kernel score) (W : ℕ)
    (hw : ∀ u c, Cache.Correct b c → ∀ seed,
      ((((callback u c).compile m).tree seed).output b).work ≤ W)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ)
    (c : Cache Q) (hc : Cache.Correct b c) (ξ : ℝ) (F : Result Q k s → ℝ) :
    ((program query root C s B c ξ callback).cap (64 * (B + s + 1) + W * s)).evaluate m b
        (fun o => o.value.elim 0 F) =
      (program query root C s B c ξ callback).evaluate m b (fun o => F o.value) := by
  rw [Code.cap_expect, ← Code.compile_expect, ← Code.compile_expect]
  unfold Compiled.expect
  apply congrArg ((program query root C s B c ξ callback).compile m).law.expect
  funext seed
  have hw' := program_compiled_work h W hw query root C s B c hc ξ seed
  simp only [hw', ite_true]

end SteinerUpperBound.Covers.OracleProgram.Mean

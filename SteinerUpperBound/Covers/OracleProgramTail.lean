module

public import SteinerUpperBound.Covers.OracleProgramCoupling

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open RetentionTree

variable {V Q R : Type*} {k : ℕ}

def ofTree {M : Type*} : DecisionTree Q Bool R → Code M Q R
  | .leaf r => .pure r
  | .query q next => .retained q (fun v => ofTree (next v))

theorem codeValue_ofTree (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (s : State Q) (F : Result Q R → ℝ) :
    codeValue cfg m (ofTree t) s F = treeValue cfg m t s F := by
  induction t generalizing s with
  | leaf => rfl
  | query q next ih =>
    simp only [ofTree, codeValue, treeValue]
    cases he : s.cache q with
    | some v => simpa only [he] using ih v (s.reply q v)
    | none =>
      simp only [he]
      congr 1
      funext v u
      exact ih v (u.reply q v)

theorem treeValue_mono (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (s : State Q) (F G : Result Q R → ℝ)
    (h : ∀ r, F r ≤ G r) : treeValue cfg m t s F ≤ treeValue cfg m t s G := by
  rw [← codeValue_ofTree cfg m t s F, ← codeValue_ofTree cfg m t s G,
    ← resolve_evaluate cfg m (fun _ => false) (ofTree t) s F,
    ← resolve_evaluate cfg m (fun _ => false) (ofTree t) s G]
  exact Code.evaluate_mono _ _ _ (fun o => h o.value)

theorem treeValue_add (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (s : State Q) (F G : Result Q R → ℝ) :
    treeValue cfg m t s (fun r => F r + G r) = treeValue cfg m t s F + treeValue cfg m t s G := by
  rw [← codeValue_ofTree cfg m t s (fun r => F r + G r),
    ← codeValue_ofTree cfg m t s F, ← codeValue_ofTree cfg m t s G,
    ← resolve_evaluate cfg m (fun _ => false) (ofTree t) s (fun r => F r + G r),
    ← resolve_evaluate cfg m (fun _ => false) (ofTree t) s F,
    ← resolve_evaluate cfg m (fun _ => false) (ofTree t) s G]
  exact Code.evaluate_add _ _ _ _ _

def Stable (s t : State Q) : Prop :=
  t.cache = s.cache ∧ t.newPositive = s.newPositive ∧ t.frontPositive = s.frontPositive

theorem scanValue_le_full (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (q : Q) (B ψ : ℕ) (s : State Q) (next : Bool → State Q → ℝ)
    (abort : State Q → ℝ) (K : Bool → ℝ)
    (hn : ∀ v t, Stable s t → next v t ≤ K v)
    (ha : ∀ v t, Stable s t → abort t ≤ K v) :
    scanValue cfg m q B ψ s next abort ≤
      (Factory.bitLaw (relation cfg m q) (cfg.target q) B ψ).expect K := by
  induction B generalizing ψ s with
  | zero =>
    rw [Factory.bitLaw_cap_zero, Law.expect_pure]
    exact hn false s ⟨rfl, rfl, rfl⟩
  | succ B ih =>
    cases ψ with
    | zero =>
      rw [Factory.bitLaw_zero, Law.expect_pure]
      exact hn false s ⟨rfl, rfl, rfl⟩
    | succ ψ =>
      by_cases hs : s.remaining = some 0
      · simp only [scanValue, hs, ite_true]
        calc
          _ = (Factory.bitLaw (relation cfg m q) (cfg.target q) (B + 1) (ψ + 1)).expect
              (fun _ => abort s) := (Law.expect_const _ _).symm
          _ ≤ _ := Law.expect_mono _ (fun v => ha v s ⟨rfl, rfl, rfl⟩)
      · rw [Factory.bitLaw_succ, Law.expect_bind]
        simp only [scanValue, hs, ite_false]
        apply (Law.uniform (Fin (k + 1))).expect_mono
        intro y
        by_cases hy : y = cfg.target q
        · simpa only [hy, ite_true, Law.expect_pure] using hn true s.draw ⟨rfl, rfl, rfl⟩
        · by_cases hr : m (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) ≤ cfg.radius q
          · simpa only [hy, ite_false, relation, hr, ite_true] using ih ψ s.draw hn ha
          · simpa only [hy, ite_false, relation, hr] using ih (ψ + 1) s.draw hn ha

noncomputable def fullPositive (cfg : Config V Q k) (m : Sym2 V → ℝ) :
    DecisionTree Q Bool R → (Q → Option Bool) → ℕ → (ℕ → ℝ) → ℝ
  | .leaf _, _, Z, F => F Z
  | .query q next, cache, Z, F =>
      match cache q with
      | some v => fullPositive cfg m (next v) cache (Z + if v then 1 else 0) F
      | none => (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials q).expect
          (fun v => fullPositive cfg m (next v) (Function.update cache q (some v))
            (Z + if v then 1 else 0) F)

theorem fullPositive_floor (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (Z : ℕ)
    (F : ℕ → ℝ) (hF : Monotone F) : F Z ≤ fullPositive cfg m t cache Z F := by
  induction t generalizing cache Z with
  | leaf => rfl
  | query q next ih =>
    simp only [fullPositive]
    cases he : cache q with
    | some v =>
      exact (hF (Nat.le_add_right _ _)).trans (ih v cache _)
    | none =>
      simp only [he]
      calc
        _ = (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials q).expect
            (fun _ => F Z) := (Law.expect_const _ _).symm
        _ ≤ _ := Law.expect_mono _ (fun v =>
          (hF (Nat.le_add_right _ _)).trans (ih v _ _))

/-- Prefix domination against completion, without conditioning on a future
good event. Every private abort is replaced by a normalized continuation whose
future positive count can only increase. -/
theorem tree_prefix_positive (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (s : State Q) (hAZ : s.newPositive ≤ s.frontPositive)
    (F : ℕ → ℝ) (hF : Monotone F) :
    treeValue cfg m t s (fun r => F r.state.newPositive) ≤
      fullPositive cfg m t s.cache s.frontPositive F := by
  classical
  induction t generalizing s with
  | leaf => exact hF hAZ
  | query q next ih =>
    simp only [treeValue, fullPositive]
    cases he : s.cache q with
    | some v =>
      have h := ih v (s.reply q v) (State.reply_positive s q v hAZ)
      simpa only [he, State.reply] using h
    | none =>
      simp only [he]
      apply scanValue_le_full cfg m q _ _ s _ _
        (fun v => fullPositive cfg m (next v) (Function.update s.cache q (some v))
          (s.frontPositive + if v then 1 else 0) F)
      · intro v u hu
        have hun : u.cache q = none := by rw [hu.1, he]
        have hAZu : u.newPositive ≤ u.frontPositive := by rw [hu.2.1, hu.2.2]; exact hAZ
        have h := ih v (u.reply q v) (State.reply_positive u q v hAZu)
        simpa only [State.reply, hun, hu.1, hu.2.2] using h
      · intro v u hu
        calc
          _ = F s.newPositive := by change F u.newPositive = _; rw [hu.2.1]
          _ ≤ F (s.frontPositive + if v then 1 else 0) :=
            hF (hAZ.trans (Nat.le_add_right _ _))
          _ ≤ _ := fullPositive_floor cfg m (next v) _ _ F hF

noncomputable def threshold (a : ℝ) (n : ℕ) : ℝ := if a < (n : ℝ) then 1 else 0

theorem threshold_monotone (a : ℝ) : Monotone (threshold a) := by
  intro n l hnl
  have hnlR : (n : ℝ) ≤ l := by exact_mod_cast hnl
  by_cases hn : a < (n : ℝ)
  · have hl : a < (l : ℝ) := hn.trans_le hnlR
    simp [threshold, hn, hl]
  · by_cases hl : a < (l : ℝ) <;> simp [threshold, hn, hl]

noncomputable def positiveTree (a : ℝ) :
    DecisionTree Q Bool R → ℕ → DecisionTree Q Bool Bool
  | .leaf _, Z => .leaf (decide (a < (Z : ℝ)))
  | .query q next, Z => .query q (fun v => positiveTree a (next v) (Z + if v then 1 else 0))

theorem positiveTree_output (a : ℝ) (t : DecisionTree Q Bool R) (Z : ℕ) (b : Q → Bool) :
    (positiveTree a t Z).output b = decide (a < ((Z + RetentionTree.positives t b : ℕ) : ℝ)) := by
  induction t generalizing Z with
  | leaf => simp [positiveTree, RetentionTree.positives, DecisionTree.output, DecisionTree.transcript]
  | query q next ih =>
    simp only [positiveTree, DecisionTree.output, ih, RetentionTree.positives_query, Nat.add_assoc]

noncomputable def bits [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (cache : Q → Option Bool) : Law (Q → Bool) :=
  Law.pi (Factory.cachedKernel cache
    (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials))

theorem fullPositive_runLaw (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (Z : ℕ) (a : ℝ) :
    fullPositive cfg m t cache Z (threshold a) =
      ((cached (positiveTree a t Z) cache).runLaw
        (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials)).prob {true} := by
  classical
  induction t generalizing cache Z with
  | leaf =>
    simp [fullPositive, threshold, positiveTree, cached, Caching.compile,
      DecisionTree.runLaw, Law.prob_pure]
  | query q next ih =>
    simp only [fullPositive, positiveTree, cached, Caching.compile, id_eq]
    cases he : cache q with
    | some v => simpa only [he, cached] using ih v cache (Z + if v then 1 else 0)
    | none =>
      simp only [he, DecisionTree.runLaw, Law.prob_bind]
      apply congrArg (Factory.coordinateLaw cfg.target (relation cfg m) cfg.caps cfg.trials q).expect
      funext v
      exact ih v (Function.update cache q (some v)) (Z + if v then 1 else 0)

theorem fullPositive_bits [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (Z : ℕ) (a : ℝ) :
    fullPositive cfg m t cache Z (threshold a) =
      (bits cfg m cache).expect (fun b => threshold a (Z + RetentionTree.positives t b)) := by
  classical
  rw [fullPositive_runLaw]
  have he := Factory.expanded_cached_law cfg.target (relation cfg m) cfg.caps cfg.trials
    (positiveTree a t Z) cache
  rw [Factory.expanded_runLaw] at he
  rw [he, Law.prob_map, Law.prob_eq_expect]
  apply congrArg (bits cfg m cache).expect
  funext b
  simp [positiveTree_output, threshold]

theorem compile_positive_eq {M : Type*} (m : M → ℝ) (b : Q → Bool) (p : Code M Q R) :
    ∀ seed : (p.compile m).Seed,
      RetentionTree.positives ((p.compile m).tree seed) b =
        (((p.compile m).tree seed).output b).positiveReplies := by
  induction p with
  | pure r => intro _; rfl
  | metric q next ih =>
    intro seed
    simpa only [Code.compile, Compiled.map, RetentionTree.positives_map,
      DecisionTree.output_map, Outcome.add, Nat.zero_add] using ih (m q) seed
  | retained q next ih =>
    intro seed
    cases hb : b q with
    | false =>
      simpa only [Code.compile, Compiled.query, RetentionTree.positives_query, hb,
        Bool.false_eq_true, ite_false, Nat.zero_add, Compiled.map, RetentionTree.positives_map,
        DecisionTree.output, DecisionTree.output_map, Outcome.add] using ih false seed.1
    | true =>
      simpa only [Code.compile, Compiled.query, RetentionTree.positives_query, hb,
        ite_true, Compiled.map, RetentionTree.positives_map, DecisionTree.output,
        DecisionTree.output_map, Outcome.add] using congrArg (fun n => 1 + n) (ih true seed.2)
  | uniform n next ih =>
    intro seed
    simpa only [Code.compile, Compiled.map, Compiled.choose, RetentionTree.positives_map,
      DecisionTree.output_map, Outcome.add, Nat.zero_add] using ih seed.1 seed.2
  | coin rate next ih =>
    intro seed
    simpa only [Code.compile, Compiled.map, Compiled.choose, RetentionTree.positives_map,
      DecisionTree.output_map, Outcome.add, Nat.zero_add] using ih seed.1 seed.2
  | tick n next ih =>
    intro seed
    simpa only [Code.compile, Compiled.map, RetentionTree.positives_map,
      DecisionTree.output_map, Outcome.add, Nat.zero_add] using ih seed

theorem tree_pending_bound [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (D : ℕ) (a : ℝ) :
    treeValue cfg m t (State.initial cache D) (fun r => if r.value = none then 1 else 0) ≤
      (bits cfg m cache).expect (fun b => threshold a (RetentionTree.positives t b)) +
        Real.exp (a - (D : ℝ) / (2 * (k + 1))) := by
  classical
  have hp := treeValue_mono cfg m t (State.initial cache D)
    (fun r => if r.value = none then 1 else 0)
    (fun r => (if r.value = none ∧ (r.state.newPositive : ℝ) ≤ a then 1 else 0) +
      threshold a r.state.newPositive) (by
        intro r
        by_cases hr : r.value = none <;> by_cases ha : (r.state.newPositive : ℝ) ≤ a <;>
          simp [hr, ha, threshold, not_lt_of_ge, lt_of_not_ge])
  rw [treeValue_add] at hp
  have hj := tree_joint_pending_tail cfg m t cache D a
  have hz := tree_prefix_positive cfg m t (State.initial cache D) (Nat.le_refl 0)
    (threshold a) (threshold_monotone a)
  change treeValue cfg m t (State.initial cache D) (fun r => threshold a r.state.newPositive) ≤
    fullPositive cfg m t cache 0 (threshold a) at hz
  rw [fullPositive_bits] at hz
  simp only [Nat.zero_add] at hz
  exact hp.trans ((add_le_add hj hz).trans_eq (add_comm _ _))

/-- The complete pending bound for the actual runtime. The first term is the
uncapped frontend's positive-reply tail under actual per-coordinate capped
factory bits. Adaptive coins remain inside the frontend evaluation. -/
theorem factory_pending_bound [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ)
    (p : Code (Sym2 V) Q R) (a : ℝ) :
    (factory cfg cache W D p).probability m b {o | o.value.value = none} ≤
      (bits cfg m cache).expect (fun oracle =>
        p.evaluate m oracle (fun o => threshold a o.positiveReplies)) +
        Real.exp (a - (D : ℝ) / (2 * (k + 1))) := by
  classical
  let F : Result Q (Option R) → ℝ := fun r => if r.value = none then 1 else 0
  have hstart :
      (factory cfg cache W D p).probability m b {o | o.value.value = none} =
        compiledValue cfg m ((p.cap W).compile m) (State.initial cache D)
          (fun r => F (r.map Outcome.value)) := by
    unfold Code.probability factory
    calc
      _ = (resolve cfg (p.cap W) (State.initial cache D)).evaluate m b (fun o => F o.value) := by
        apply congrArg ((resolve cfg (p.cap W) (State.initial cache D)).evaluate m b)
        funext o
        by_cases h : o.value.value = none <;> simp [F, h]
      _ = _ := (resolve_evaluate cfg m b _ _ F).trans (compile_handler cfg m _ _ F).symm
  rw [hstart]
  unfold compiledValue
  have hseed :
      ∀ seed : ((p.cap W).compile m).Seed,
        treeValue cfg m (((p.cap W).compile m).tree seed) (State.initial cache D)
          (fun r => F (r.map Outcome.value)) ≤
        (bits cfg m cache).expect (fun oracle =>
          threshold a ((((p.cap W).compile m).tree seed).output oracle).positiveReplies) +
          Real.exp (a - (D : ℝ) / (2 * (k + 1))) := by
    intro seed
    rw [← treeValue_map cfg m (((p.cap W).compile m).tree seed) Outcome.value (State.initial cache D) F]
    have h := tree_pending_bound cfg m ((((p.cap W).compile m).tree seed).map Outcome.value) cache D a
    simpa only [RetentionTree.positives_map, compile_positive_eq, F] using h
  apply (Law.expect_mono _ (fun seed => hseed seed)).trans
  rw [Law.expect_add, Law.expect_const,
    expect_comm ((p.cap W).compile m).law (bits cfg m cache)
      (fun seed oracle => threshold a ((((p.cap W).compile m).tree seed).output oracle).positiveReplies)]
  apply add_le_add _ le_rfl
  apply (bits cfg m cache).expect_mono
  intro oracle
  have he := Code.compile_expect m oracle (p.cap W) (fun o => threshold a o.positiveReplies)
  change (((p.cap W).compile m).expect oracle (fun o => threshold a o.positiveReplies)) ≤ _
  rw [he]
  exact Code.cap_positive_mono m oracle p W (threshold a) (threshold_monotone a)

theorem factory_clock_exp_le (k D : ℕ) (a ε : ℝ) (hε : 0 < ε)
    (hD : 2 * ((k + 1 : ℕ) : ℝ) * (a + Real.log (1 / ε)) ≤ D) :
    Real.exp (a - (D : ℝ) / (2 * (k + 1))) ≤ ε := by
  have hc : (0 : ℝ) < 2 * (k + 1) := by positivity
  have hl : Real.log (1 / ε) = -Real.log ε := by simp
  have ha : a - Real.log ε ≤ (D : ℝ) / (2 * (k + 1)) := by
    apply (le_div_iff₀ hc).mpr
    rw [hl] at hD
    push_cast at hD
    nlinarith
  apply (Real.exp_le_exp.mpr (by linarith : a - (D : ℝ) / (2 * (k + 1)) ≤ Real.log ε)).trans_eq
  exact Real.exp_log hε

theorem factory_pending_budget [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ)
    (p : Code (Sym2 V) Q R) (a ε : ℝ) (hε : 0 < ε)
    (hD : 2 * ((k + 1 : ℕ) : ℝ) * (a + Real.log (1 / ε)) ≤ D) :
    (factory cfg cache W D p).probability m b {o | o.value.value = none} ≤
      (bits cfg m cache).expect (fun oracle =>
        p.evaluate m oracle (fun o => threshold a o.positiveReplies)) + ε :=
  (factory_pending_bound cfg m b cache W D p a).trans
    (add_le_add le_rfl (factory_clock_exp_le k D a ε hε hD))

theorem factory_positive_tail_le [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ)
    (p : Code (Sym2 V) Q R) (a : ℝ) :
    (factory cfg cache W D p).evaluate m b (fun o => threshold a o.value.state.newPositive) ≤
      (bits cfg m cache).expect (fun oracle =>
        p.evaluate m oracle (fun o => threshold a o.positiveReplies)) := by
  have he := resolve_evaluate cfg m b (p.cap W) (State.initial cache D)
    (fun r => threshold a r.state.newPositive)
  have hc := compile_handler cfg m (p.cap W) (State.initial cache D)
    (fun r => threshold a r.state.newPositive)
  change (resolve cfg (p.cap W) (State.initial cache D)).evaluate m b _ ≤ _
  rw [he, ← hc]
  unfold compiledValue
  have hseed :
      ∀ seed : ((p.cap W).compile m).Seed,
        treeValue cfg m (((p.cap W).compile m).tree seed) (State.initial cache D)
          (fun r => threshold a (r.map Outcome.value).state.newPositive) ≤
          (bits cfg m cache).expect (fun oracle =>
            threshold a ((((p.cap W).compile m).tree seed).output oracle).positiveReplies) := by
    intro seed
    have h := tree_prefix_positive cfg m (((p.cap W).compile m).tree seed)
      (State.initial cache D) (Nat.le_refl 0) (threshold a) (threshold_monotone a)
    change treeValue cfg m (((p.cap W).compile m).tree seed) (State.initial cache D)
      (fun r => threshold a r.state.newPositive) ≤
      fullPositive cfg m (((p.cap W).compile m).tree seed) cache 0 (threshold a) at h
    rw [fullPositive_bits] at h
    simpa only [Nat.zero_add, compile_positive_eq, Result.map] using h
  apply (Law.expect_mono _ hseed).trans
  rw [expect_comm ((p.cap W).compile m).law (bits cfg m cache)
    (fun seed oracle => threshold a ((((p.cap W).compile m).tree seed).output oracle).positiveReplies)]
  apply (bits cfg m cache).expect_mono
  intro oracle
  change (((p.cap W).compile m).expect oracle (fun o => threshold a o.positiveReplies)) ≤ _
  rw [Code.compile_expect]
  exact Code.cap_positive_mono m oracle p W (threshold a) (threshold_monotone a)

end SteinerUpperBound.Covers.OracleProgram

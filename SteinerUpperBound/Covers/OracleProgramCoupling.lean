module

public import SteinerUpperBound.Covers.OracleProgramSemantics

@[expose] public section

namespace SteinerUpperBound.Covers.OracleProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {V Q R : Type*} {k : ℕ}

noncomputable def rawValue (target : Q → Fin (k + 1)) :
    ℕ → DecisionTree Q (Fin (k + 1)) R → ℕ → (Option R → ℕ → ℝ) → ℝ
  | 0, t, A, F =>
      F (match t with | .leaf r => some r | .query _ _ => none) A
  | _ + 1, .leaf r, A, F => F (some r) A
  | D + 1, .query q next, A, F =>
      (Law.uniform (Fin (k + 1))).expect (fun y =>
        rawValue target D (next y) (A + if y = target q then 1 else 0) F)

theorem scanValue_raw (cfg : Config V Q k) (m : Sym2 V → ℝ) (q : Q)
    (B ψ : ℕ) (s : State Q) (D : ℕ) (hD : s.remaining = some D)
    (next : Bool → State Q → ℝ) (trees : Bool → DecisionTree Q (Fin (k + 1)) R)
    (F : Option R → ℕ → ℝ)
    (hn : ∀ v t d, t.cache = s.cache → t.newPositive = s.newPositive →
      t.remaining = some d →
      next v t = rawValue cfg.target d (trees v) (s.newPositive + if v then 1 else 0) F) :
    scanValue cfg m q B ψ s next (fun t => F none t.newPositive) =
      rawValue cfg.target D (Factory.inner cfg.target (relation cfg m) q B ψ trees)
        s.newPositive F := by
  induction B generalizing ψ s D with
  | zero =>
    simpa only [scanValue, Factory.inner, Bool.false_eq_true, ite_false, Nat.add_zero] using
      hn false s D rfl rfl hD
  | succ B ih =>
    cases ψ with
    | zero =>
      simpa only [scanValue, Factory.inner, Bool.false_eq_true, ite_false, Nat.add_zero] using
        hn false s D rfl rfl hD
    | succ ψ =>
      cases D with
      | zero => simp [scanValue, hD, Factory.inner, rawValue]
      | succ D =>
        have hne : s.remaining ≠ some 0 := by rw [hD]; simp
        simp only [scanValue, hne, ite_false, Factory.inner, rawValue]
        apply congrArg (Law.uniform (Fin (k + 1))).expect
        funext y
        have hd : s.draw.remaining = some D := by simp [State.draw, hD]
        by_cases hy : y = cfg.target q
        · simp only [hy, ite_true]
          exact hn true s.draw D rfl rfl hd
        · simp only [hy, ite_false, Nat.add_zero]
          have h := ih
            (if m (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) ≤ cfg.radius q
              then ψ else ψ + 1) s.draw D hd hn
          by_cases hnear : m (Sym2.mk (cfg.label (cfg.target q)) (cfg.label y)) ≤ cfg.radius q
          · simpa only [relation, hnear, ite_true, State.draw] using h
          · simpa only [relation, hnear, ite_false, State.draw] using h

theorem treeValue_raw (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (s : State Q) (D : ℕ) (hD : s.remaining = some D)
    (F : Option R → ℕ → ℝ) :
    treeValue cfg m t s (fun r => F r.value r.state.newPositive) =
      rawValue cfg.target D
        (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t s.cache))
        s.newPositive F := by
  classical
  induction t generalizing s D with
  | leaf r => cases D <;> rfl
  | query q next ih =>
    simp only [treeValue]
    cases he : s.cache q with
    | some v =>
      have hr := ih v (s.reply q v) D (by rwa [reply_remaining])
      simpa only [he, State.reply, cached, Caching.compile, id_eq] using hr
    | none =>
      simp only [he]
      change scanValue cfg m q (cfg.caps q) (cfg.trials q) s
        (fun v u => treeValue cfg m (next v) (u.reply q v)
          (fun r => F r.value r.state.newPositive)) (fun u => F none u.newPositive) = _
      rw [scanValue_raw cfg m q _ _ s D hD _
        (fun v => Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials
          (cached (next v) (Function.update s.cache q (some v)))) F]
      · simp only [cached, Caching.compile, id_eq, he, Factory.expanded]
      · intro v u d hcache hA hd
        have hun : u.cache q = none := by rw [hcache, he]
        have hr := ih v (u.reply q v) d (by rwa [reply_remaining])
        simpa only [State.reply, hun, hcache, hA] using hr

def activeHits (target : Q → Fin (k + 1)) :
    (D : ℕ) → DecisionTree Q (Fin (k + 1)) R → (Fin D → Fin (k + 1)) → ℕ
  | 0, _, _ => 0
  | _ + 1, .leaf _, _ => 0
  | D + 1, .query q next, w =>
      (if w 0 = target q then 1 else 0) + activeHits target D (next (w 0)) (Fin.tail w)

theorem rawValue_tape (target : Q → Fin (k + 1)) (D : ℕ)
    (t : DecisionTree Q (Fin (k + 1)) R) (A : ℕ) (F : Option R → ℕ → ℝ) :
    rawValue target D t A F =
      (tape (Law.uniform (Fin (k + 1))) D).expect
        (fun w => F (Factory.evaluate D t w) (A + activeHits target D t w)) := by
  induction D generalizing t A with
  | zero => cases t <;> simp [rawValue, tape, Factory.evaluate, activeHits]
  | succ D ih =>
    cases t with
    | leaf r => simp [rawValue, Factory.evaluate, activeHits, Law.expect_const]
    | query q next =>
      rw [expect_tape_succ, rawValue]
      apply congrArg (Law.uniform (Fin (k + 1))).expect
      funext y
      rw [ih]
      apply congrArg (tape (Law.uniform (Fin (k + 1))) D).expect
      funext w
      simp only [Factory.evaluate, activeHits, Fin.cons_zero, Fin.tail_cons, Nat.add_assoc]

theorem activeHits_disclosures (target : Q → Fin (k + 1)) (D : ℕ)
    (t : DecisionTree Q (Fin (k + 1)) R) (S : Finset Q) (w : Fin D → Fin (k + 1))
    (hf : Factory.Fresh target S t) :
    activeHits target D t w + S.card = (Factory.run target D (t, S) w).2.card := by
  classical
  induction D generalizing t S with
  | zero => simp [activeHits, Factory.run]
  | succ D ih =>
    cases t with
    | leaf r => rw [Factory.run_leaf]; simp [activeHits]
    | query q next =>
      by_cases hy : w 0 = target q
      · have hf' : Factory.Fresh target (insert q S) (next (w 0)) := by
          simpa only [hy, ite_true] using hf.2 (w 0)
        have h := ih (next (w 0)) (insert q S) (Fin.tail w) hf'
        have hc : (insert q S).card = S.card + 1 := Finset.card_insert_of_notMem hf.1
        rw [hc] at h
        simp only [hy] at h
        simp only [activeHits, Factory.run, Factory.step, hy, ite_true]
        omega
      · have hf' : Factory.Fresh target S (next (w 0)) := by
          simpa only [hy, ite_false] using hf.2 (w 0)
        have h := ih (next (w 0)) S (Fin.tail w) hf'
        simpa only [activeHits, Factory.run, Factory.step, hy, ite_false, Nat.zero_add] using h

/-- Exact operational law for each fixed finite frontend seed. The finite tape
is used only in this analysis equation; the runtime samples no unused suffix. -/
theorem treeValue_capped_law [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (D : ℕ)
    (F : Option R → ℕ → ℝ) :
    treeValue cfg m t (State.initial cache D) (fun r => F r.value r.state.newPositive) =
      let start : Factory.State Q (Fin (k + 1)) R :=
        (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t cache),
          Factory.initiallyRetained cache)
      (tape (Law.uniform (Fin (k + 1))) D).expect (fun w =>
        F (Factory.output (Factory.run cfg.target D start w))
          ((Factory.run cfg.target D start w).2.card - start.2.card)) := by
  classical
  rw [treeValue_raw cfg m t _ D rfl, rawValue_tape]
  dsimp only [State.initial]
  apply congrArg (tape (Law.uniform (Fin (k + 1))) D).expect
  funext w
  have hf := Factory.expanded_cached_fresh cfg.target (relation cfg m) cfg.caps cfg.trials t cache
  have h := activeHits_disclosures cfg.target D
    (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t cache))
    (Factory.initiallyRetained cache) w hf
  have he : activeHits cfg.target D
      (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t cache)) w =
      (Factory.run cfg.target D
        (Factory.expanded cfg.target (relation cfg m) cfg.caps cfg.trials (cached t cache),
          Factory.initiallyRetained cache) w).2.card - (Factory.initiallyRetained cache).card := by omega
  rw [he, ← Factory.run_output cfg.target D _ (Factory.initiallyRetained cache) w]
  simp only [Nat.zero_add]

theorem tree_joint_pending_tail [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (D : ℕ) (a : ℝ) :
    treeValue cfg m t (State.initial cache D)
      (fun r => if r.value = none ∧ (r.state.newPositive : ℝ) ≤ a then 1 else 0) ≤
      Real.exp (a - (D : ℝ) / (2 * (k + 1))) := by
  classical
  rw [treeValue_capped_law cfg m t cache D
    (fun value A => if value = none ∧ (A : ℝ) ≤ a then 1 else 0)]
  have hb := Factory.cached_factory_cap_tail (0 : Fin (k + 1)) cfg.target
    (relation cfg m) cfg.caps cfg.trials t cache D a
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hb
  rw [Law.prob_eq_expect] at hb
  convert hb using 1
  apply congrArg (tape (Law.uniform (Fin (k + 1))) D).expect
  funext w
  simp only [Set.mem_ofPred_eq, Factory.output_none_iff]
  split_ifs <;> rfl

/-- Uniformly over adaptive frontend seeds, the actual code has the checked
fixed-horizon factory tail. Real-valued frontend outputs need no `Fintype`. -/
theorem factory_joint_pending_tail [Fintype Q] (cfg : Config V Q k) (m : Sym2 V → ℝ)
    (b : Q → Bool) (cache : Q → Option Bool) (W D : ℕ)
    (p : Code (Sym2 V) Q R) (a : ℝ) :
    (factory cfg cache W D p).probability m b
      {o | o.value.value = none ∧ (o.value.state.newPositive : ℝ) ≤ a} ≤
        Real.exp (a - (D : ℝ) / (2 * (k + 1))) := by
  classical
  unfold Code.probability factory
  simp only [Set.mem_ofPred_eq]
  let F : Result Q (Option R) → ℝ :=
    fun r => if r.value = none ∧ (r.state.newPositive : ℝ) ≤ a then 1 else 0
  calc
    _ = (resolve cfg (p.cap W) (State.initial cache D)).evaluate m b (fun o => F o.value) := by
      apply congrArg ((resolve cfg (p.cap W) (State.initial cache D)).evaluate m b)
      funext o
      dsimp only [F]
      split_ifs <;> rfl
    _ = codeValue cfg m (p.cap W) (State.initial cache D) F := resolve_evaluate _ _ _ _ _ _
    _ = compiledValue cfg m ((p.cap W).compile m) (State.initial cache D)
        (fun r => F (r.map Outcome.value)) := (compile_handler _ _ _ _ _).symm
    _ ≤ _ := by
      unfold compiledValue
      apply (Law.expect_mono _ (fun seed => ?_)).trans (Law.expect_const _ _).le
      rw [← treeValue_map cfg m (((p.cap W).compile m).tree seed) Outcome.value
        (State.initial cache D) F]
      exact tree_joint_pending_tail cfg m _ cache D a

end SteinerUpperBound.Covers.OracleProgram

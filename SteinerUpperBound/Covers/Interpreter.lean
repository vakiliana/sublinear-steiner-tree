module

public import SteinerUpperBound.Covers.SamplingTree

@[expose] public section

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {Q U R : Type*}

/-- Internal draws are invisible to the Boolean continuation. A target hit
resolves the current bit immediately; exhaustion resolves it to `false`. -/
noncomputable def inner (target : Q → U) (rel : Q → U → U → Prop) (q : Q) :
    ℕ → ℕ → (Bool → DecisionTree Q U R) → DecisionTree Q U R
  | 0, _, next => next false
  | _ + 1, 0, next => next false
  | B + 1, ψ + 1, next => .query q (fun y =>
      if y = target q then next true
      else if rel q (target q) y then inner target rel q B ψ next
      else inner target rel q B (ψ + 1) next)

noncomputable def expanded (target : Q → U) (rel : Q → U → U → Prop)
    (caps trials : Q → ℕ) : DecisionTree Q Bool R → DecisionTree Q U R
  | .leaf r => .leaf r
  | .query q next => inner target rel q (caps q) (trials q)
      (fun b => expanded target rel caps trials (next b))

noncomputable def coordinateLaw [Fintype U] [Nonempty U]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ) (q : Q) :
    Law Bool :=
  bitLaw (rel q) (target q) (caps q) (trials q)

theorem pure_bind {A B : Type*} [Fintype A] [Fintype B] (a : A) (k : A → Law B) :
    (Law.pure a).bind k = k a := by
  apply LawOperations.ext_mass
  intro b
  exact Law.expect_pure _ _

theorem map_pure {A B : Type*} [Fintype A] [Fintype B] (a : A) (f : A → B) :
    (Law.pure a).map f = Law.pure (f a) := by
  apply LawOperations.ext_prob
  intro E
  simp [Law.prob_map, Law.prob_pure]

theorem bitLaw_cap_zero [Fintype U] [Nonempty U]
    (rel : U → U → Prop) (x : U) (ψ : ℕ) :
    bitLaw rel x 0 ψ = Law.pure false := by
  cases ψ <;> simp only [bitLaw, law, map_pure, Option.getD_none, Option.getD_some]

theorem inner_runLaw [Fintype U] [Nonempty U] [Fintype R]
    (target : Q → U) (rel : Q → U → U → Prop) (q : Q) (B ψ : ℕ)
    (next : Bool → DecisionTree Q U R) :
    (inner target rel q B ψ next).runLaw (fun _ => Law.uniform U) =
      (bitLaw (rel q) (target q) B ψ).bind
        (fun b => (next b).runLaw (fun _ => Law.uniform U)) := by
  classical
  induction B generalizing ψ with
  | zero => rw [inner, bitLaw_cap_zero, pure_bind]
  | succ B ih =>
    cases ψ with
    | zero => rw [inner, bitLaw_zero, pure_bind]
    | succ ψ =>
      rw [inner, DecisionTree.runLaw, bitLaw_succ, LawOperations.bind_assoc]
      congr 1
      funext y
      by_cases hy : y = target q
      · simp only [hy, ↓reduceIte, pure_bind]
      · by_cases hr : rel q (target q) y
        · simpa only [hy, hr, ↓reduceIte] using ih ψ
        · simpa only [hy, hr, ↓reduceIte] using ih (ψ + 1)

theorem expanded_runLaw [Fintype U] [Nonempty U] [Fintype R]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) :
    (expanded target rel caps trials t).runLaw (fun _ => Law.uniform U) =
      t.runLaw (coordinateLaw target rel caps trials) := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    rw [expanded, inner_runLaw, DecisionTree.runLaw]
    congr 1
    funext b
    exact ih b

theorem runLaw_agree_used {A B : Type*} [Fintype A] [Fintype B]
    (μ ν : Q → Law A) (t : DecisionTree Q A B)
    (h : ∀ q ∈ t.used, μ q = ν q) : t.runLaw μ = t.runLaw ν := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    simp only [DecisionTree.runLaw]
    rw [h q (Finset.mem_insert_self _ _)]
    congr 1
    funext a
    exact ih a (fun q' hq' => h q' (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hq'⟩)))

noncomputable def cachedKernel (cache : Q → Option Bool) (μ : Q → Law Bool) (q : Q) :
    Law Bool :=
  match cache q with
  | none => μ q
  | some b => Law.pure b

theorem cachedKernel_consistent [Fintype Q] (cache : Q → Option Bool)
    (μ : Q → Law Bool) (b : Q → Bool)
    (hb : 0 < (Law.pi (cachedKernel cache μ)).mass b) :
    Caching.Consistent cache b := by
  intro q v hq
  have hp := Law.pi_mass_positive (cachedKernel cache μ) b hb q
  simp only [cachedKernel, hq, Law.pure] at hp
  by_contra hn
  simp [hn] at hp

/-- Exact reference law for the actual cached factory with private finite
randomness. Initial cache entries, including designated fixed terminals, are
forced rather than resampled. -/
theorem expanded_cached_law [Fintype Q] [Fintype U] [Nonempty U] [Fintype R]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) :
    (expanded target rel caps trials (cached t cache)).runLaw (fun _ => Law.uniform U) =
      (Law.pi (cachedKernel cache (coordinateLaw target rel caps trials))).map
        (fun b => t.output b) := by
  classical
  let μ := coordinateLaw target rel caps trials
  let ν := cachedKernel cache μ
  let tc := cached t cache
  have hagree : ∀ q ∈ tc.used, μ q = ν q := by
    intro q hq
    have hn : cache q = none := by
      by_contra h
      exact Caching.used_avoids_cache id (fun _ b => b) t cache q h hq
    simp [ν, cachedKernel, hn]
  have hnr : tc.NoRepeats := Caching.compile_no_repeats _ _ _ _
  rw [expanded_runLaw, runLaw_agree_used μ ν tc hagree]
  apply LawOperations.ext_prob
  intro E
  rw [Law.prob_map, ← DecisionTree.deferred_sampling ν tc hnr E]
  apply le_antisymm
  · apply Law.prob_mono_support
    intro b hb he
    have hc := cachedKernel_consistent cache μ b hb
    have hout := Caching.output_compile id (fun _ v => v) t cache b hc
    have hout' : tc.output b = t.output b := by simpa only [tc, cached, id_eq] using hout
    change tc.output b ∈ E at he
    change t.output b ∈ E
    rwa [hout'] at he
  · apply Law.prob_mono_support
    intro b hb he
    have hc := cachedKernel_consistent cache μ b hb
    have hout := Caching.output_compile id (fun _ v => v) t cache b hc
    have hout' : tc.output b = t.output b := by simpa only [tc, cached, id_eq] using hout
    change t.output b ∈ E at he
    change tc.output b ∈ E
    rwa [hout']

/-- A structural invariant of the actual expanded cached program, proved below,
not an assumed stochastic certificate. -/
def Fresh [Fintype U] (target : Q → U) :
    Finset Q → DecisionTree Q U R → Prop
  | _, .leaf _ => True
  | S, .query q next => q ∉ S ∧ ∀ y, Fresh target
      (if y = target q then insert q S else S) (next y)

theorem inner_fresh [Fintype U] (target : Q → U) (rel : Q → U → U → Prop)
    (q : Q) (B ψ : ℕ) (next : Bool → DecisionTree Q U R) (S : Finset Q)
    (hq : q ∉ S) (hfalse : Fresh target S (next false))
    (htrue : Fresh target (insert q S) (next true)) :
    Fresh target S (inner target rel q B ψ next) := by
  classical
  induction B generalizing ψ with
  | zero => exact hfalse
  | succ B ih =>
    cases ψ with
    | zero => exact hfalse
    | succ ψ =>
      refine ⟨hq, fun y => ?_⟩
      by_cases hy : y = target q
      · simpa only [hy, ↓reduceIte] using htrue
      · by_cases hr : rel q (target q) y
        · simpa only [hy, hr, ↓reduceIte] using ih ψ
        · simpa only [hy, hr, ↓reduceIte] using ih (ψ + 1)

theorem expanded_fresh [Fintype U] (target : Q → U) (rel : Q → U → U → Prop)
    (caps trials : Q → ℕ) (t : DecisionTree Q Bool R) (ht : t.NoRepeats)
    (S : Finset Q) (hS : ∀ q ∈ S, q ∉ t.used) :
    Fresh target S (expanded target rel caps trials t) := by
  classical
  induction t generalizing S with
  | leaf => trivial
  | query q next ih =>
    have hq : q ∉ S := fun hq => hS q hq (Finset.mem_insert_self _ _)
    apply inner_fresh _ _ _ _ _ _ _ hq
    · apply ih false (ht.1 false) S
      intro q' hq' hu
      exact hS q' hq' (Finset.mem_insert_of_mem
        (Finset.mem_biUnion.mpr ⟨false, Finset.mem_univ _, hu⟩))
    · apply ih true (ht.1 true) (insert q S)
      intro q' hq' hu
      rcases Finset.mem_insert.mp hq' with rfl | hq'
      · exact ht.2 true hu
      · exact hS q' hq' (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨true, Finset.mem_univ _, hu⟩))

noncomputable def initiallyRetained [Fintype Q] (cache : Q → Option Bool) : Finset Q :=
  Finset.univ.filter (fun q => cache q = some true)

theorem expanded_cached_fresh [Fintype Q] [Fintype U]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) :
    Fresh target (initiallyRetained cache)
      (expanded target rel caps trials (cached t cache)) := by
  apply expanded_fresh _ _ _ _ _ (Caching.compile_no_repeats _ _ _ _)
  intro q hq
  apply Caching.used_avoids_cache id (fun _ b => b) t cache q
  simp only [initiallyRetained, Finset.mem_filter] at hq
  rw [hq.2]
  simp

abbrev State (Q U R : Type*) := DecisionTree Q U R × Finset Q

noncomputable def step (target : Q → U) (s : State Q U R) (y : U) : State Q U R :=
  match s.1 with
  | .leaf _ => s
  | .query q next => (next y, if y = target q then insert q s.2 else s.2)

def currentTarget (dummy : U) (target : Q → U) (s : State Q U R) : U :=
  match s.1 with
  | .leaf _ => dummy
  | .query q _ => target q

def Pending (s : State Q U R) : Prop :=
  match s.1 with
  | .leaf _ => False
  | .query _ _ => True

noncomputable def run (target : Q → U) :
    (B : ℕ) → State Q U R → (Fin B → U) → State Q U R
  | 0, s, _ => s
  | B + 1, s, w => run target B (step target s (w 0)) (Fin.tail w)

def output (s : State Q U R) : Option R :=
  match s.1 with
  | .leaf r => some r
  | .query _ _ => none

noncomputable def work (target : Q → U) :
    (B : ℕ) → State Q U R → (Fin B → U) → ℕ
  | 0, _, _ => 0
  | B + 1, s, w =>
      match s.1 with
      | .leaf _ => 0
      | .query _ _ => 1 + work target B (step target s (w 0)) (Fin.tail w)

theorem work_le (target : Q → U) (B : ℕ) (s : State Q U R) (w : Fin B → U) :
    work target B s w ≤ B := by
  induction B generalizing s with
  | zero => simp [work]
  | succ B ih =>
    rcases s with ⟨t, S⟩
    cases t with
    | leaf => simp [work]
    | query q next =>
      have h := ih (step target (.query q next, S) (w 0)) (Fin.tail w)
      simpa only [work, Nat.add_comm] using Nat.add_le_add_left h 1

theorem run_leaf (target : Q → U) (B : ℕ) (r : R) (S : Finset Q) (w : Fin B → U) :
    run target B (.leaf r, S) w = (.leaf r, S) := by
  induction B with
  | zero => rfl
  | succ B ih => exact ih (Fin.tail w)

theorem hit_count_eq_disclosures [Fintype U] (dummy : U) (target : Q → U)
    (B : ℕ) (s : State Q U R) (w : Fin B → U) (hf : Fresh target s.2 s.1)
    (hp : Pending (run target B s w)) :
    hits (currentTarget dummy target) (step target) B s w + s.2.card =
      (run target B s w).2.card := by
  classical
  induction B generalizing s with
  | zero => simp [hits, run]
  | succ B ih =>
    rcases s with ⟨t, S⟩
    cases t with
    | leaf r =>
      rw [run_leaf] at hp
      exact hp.elim
    | query q next =>
      have hnext := hf.2 (w 0)
      have hi := ih (step target (.query q next, S) (w 0)) (Fin.tail w) hnext hp
      by_cases hy : w 0 = target q
      · have hc : (insert q S).card = S.card + 1 := Finset.card_insert_of_notMem hf.1
        simp only [hits, currentTarget, hy, ↓reduceIte, step, run, hc] at hi ⊢
        omega
      · simpa only [hits, currentTarget, hy, ↓reduceIte, step, run, zero_add] using hi

theorem pending_work_eq (target : Q → U) (B : ℕ) (s : State Q U R) (w : Fin B → U)
    (hp : Pending (run target B s w)) : work target B s w = B := by
  induction B generalizing s with
  | zero => rfl
  | succ B ih =>
    rcases s with ⟨t, S⟩
    cases t with
    | leaf r =>
      rw [run_leaf] at hp
      exact hp.elim
    | query q next =>
      have hi := ih (step target (.query q next, S) (w 0)) (Fin.tail w) hp
      simp only [work, hi]
      omega

/-- Fixed-horizon work tail for the actual cached interpreter. The event bounds
the actual number of newly disclosed retained coordinates, not a future-good
conditional expectation. -/
theorem cached_factory_cap_tail [Fintype Q] [Fintype U] [Nonempty U]
    (dummy : U) (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) (a : ℝ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (tape (Law.uniform U) B).prob
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ a} ≤
      Real.exp (a - (B : ℝ) / (2 * Fintype.card U)) := by
  classical
  dsimp only
  let s : State Q U R :=
    (expanded target rel caps trials (cached t cache), initiallyRetained cache)
  have hf : Fresh target s.2 s.1 := expanded_cached_fresh _ _ _ _ _ _
  have hsub :
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ a} ⊆
      {w | (hits (currentTarget dummy target) (step target) B s w : ℝ) ≤ a} := by
    intro w hw
    have hcount := hit_count_eq_disclosures dummy target B s w hf hw.1
    have he : hits (currentTarget dummy target) (step target) B s w =
        (run target B s w).2.card - s.2.card := by omega
    change (hits (currentTarget dummy target) (step target) B s w : ℝ) ≤ a
    rw [he]
    exact hw.2
  exact (Law.prob_mono _ hsub).trans
    (hit_lower_tail (currentTarget dummy target) (step target) B s a)

end SteinerUpperBound.Covers.Factory

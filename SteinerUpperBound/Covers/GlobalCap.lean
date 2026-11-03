module

public import SteinerUpperBound.Covers.Interpreter

@[expose] public section

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {Q U R : Type*}

def evaluate : (B : ℕ) → DecisionTree Q U R → (Fin B → U) → Option R
  | 0, .leaf r, _ => some r
  | 0, .query _ _, _ => none
  | _ + 1, .leaf r, _ => some r
  | B + 1, .query _ next, w => evaluate B (next (w 0)) (Fin.tail w)

theorem run_output (target : Q → U) (B : ℕ) (t : DecisionTree Q U R)
    (S : Finset Q) (w : Fin B → U) :
    output (run target B (t, S) w) = evaluate B t w := by
  induction B generalizing t S with
  | zero => cases t <;> rfl
  | succ B ih =>
    cases t with
    | leaf r => rw [run_leaf]; rfl
    | query q next =>
      exact ih (next (w 0)) (if w 0 = target q then insert q S else S) (Fin.tail w)

theorem output_none_iff (s : State Q U R) : output s = none ↔ Pending s := by
  rcases s with ⟨t, S⟩
  cases t <;> simp [output, Pending]

theorem evaluate_law [Fintype U] [Fintype R] (μ : Law U)
    (B : ℕ) (t : DecisionTree Q U R) :
    (tape μ B).map (evaluate B t) = (t.truncate B).runLaw (fun _ => μ) := by
  induction B generalizing t with
  | zero =>
    cases t <;> simp only [evaluate, DecisionTree.truncate, DecisionTree.runLaw] <;>
      exact map_const _ _
  | succ B ih =>
    cases t with
    | leaf r => simpa only [evaluate, DecisionTree.truncate, DecisionTree.runLaw] using
        map_const (tape μ (B + 1)) (some r)
    | query q next =>
      rw [map_tape_succ]
      simp only [DecisionTree.truncate, DecisionTree.runLaw]
      congr 1
      funext y
      simpa only [evaluate, Fin.cons_zero, Fin.tail_cons] using ih (next y)

theorem truncate_law_close [Fintype U] [Fintype R]
    (μ : Q → Law U) (B : ℕ) (t : DecisionTree Q U R) :
    Law.Close ((t.truncate B).runLaw μ) ((t.runLaw μ).map some)
      (((t.truncate B).runLaw μ).prob {none}) := by
  induction B generalizing t with
  | zero =>
    cases t with
    | leaf r =>
      simp only [DecisionTree.truncate, DecisionTree.runLaw, map_pure]
      simpa only [Law.prob_pure, Set.mem_singleton_iff, Option.some_ne_none, ↓reduceIte] using
        Law.close_refl (Law.pure (some r))
    | query q next =>
      simpa only [DecisionTree.truncate, DecisionTree.runLaw, Law.prob_pure,
        Set.mem_singleton_iff, ↓reduceIte] using
          Law.close_one (Law.pure (none : Option R))
            (((DecisionTree.query q next).runLaw μ).map some)
  | succ B ih =>
    cases t with
    | leaf r =>
      simp only [DecisionTree.truncate, DecisionTree.runLaw, map_pure]
      simpa only [Law.prob_pure, Set.mem_singleton_iff, Option.some_ne_none, ↓reduceIte] using
        Law.close_refl (Law.pure (some r))
    | query q next =>
      simp only [DecisionTree.truncate, DecisionTree.runLaw, LawOperations.map_bind,
        Law.prob_bind]
      exact Law.Close.bind_same (μ q)
        (fun y => ((next y).truncate B).runLaw μ)
        (fun y => ((next y).runLaw μ).map some)
        (fun y => (((next y).truncate B).runLaw μ).prob {none}) (fun y => ih (next y))

theorem global_capped_law_close [Fintype Q] [Fintype U] [Nonempty U] [Fintype R]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    Law.Close
      ((tape (Law.uniform U) B).map (fun w => output (run target B s w)))
      ((Law.pi (cachedKernel cache (coordinateLaw target rel caps trials))).map
        (fun b => some (t.output b)))
      ((tape (Law.uniform U) B).prob {w | Pending (run target B s w)}) := by
  classical
  dsimp only
  let t' := expanded target rel caps trials (cached t cache)
  let S := initiallyRetained cache
  have hc := truncate_law_close (fun _ : Q => Law.uniform U) B t'
  rw [← evaluate_law (Law.uniform U) B t',
    expanded_cached_law target rel caps trials t cache, LawOperations.map_comp] at hc
  have he : (evaluate B t') = fun w => output (run target B (t', S) w) := by
    funext w
    exact (run_output target B t' S w).symm
  rw [he, Law.prob_map] at hc
  have hset : (fun w => output (run target B (t', S) w)) ⁻¹' ({none} : Set (Option R)) =
      {w | Pending (run target B (t', S) w)} := by
    ext w
    exact output_none_iff _
  rw [hset] at hc
  exact hc

noncomputable def globalDrawBudget (k : ℕ) (a β : ℝ) : ℕ :=
  ⌈2 * (k : ℝ) * (a + Real.log (1 / β))⌉₊

theorem cached_factory_cap_budget [Fintype Q] [Fintype U] [Nonempty U]
    (dummy : U) (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (a β : ℝ) (hβ : 0 < β) :
    let B := globalDrawBudget (Fintype.card U) a β
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (tape (Law.uniform U) B).prob
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ a} ≤ β := by
  dsimp only
  apply (cached_factory_cap_tail dummy target rel caps trials t cache _ a).trans
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hB := Nat.le_ceil (2 * (Fintype.card U : ℝ) * (a + Real.log (1 / β)))
  calc
    _ ≤ Real.exp (-Real.log (1 / β)) := by
      apply Real.exp_le_exp.mpr
      have hd : a + Real.log (1 / β) ≤
          (globalDrawBudget (Fintype.card U) a β : ℝ) / (2 * Fintype.card U) :=
        (le_div_iff₀ (by positivity)).mpr (by
          dsimp [globalDrawBudget]
          nlinarith)
      linarith
    _ = β := by rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / β)]; simp

theorem cached_bits_ideal_close [Fintype Q] [Fintype U] [Nonempty U]
    (target : Q → U) (rel : Q → U → U → Prop) (hrefl : ∀ q x, rel q x x)
    (caps trials : Q → ℕ) (cache : Q → Option Bool) (B₀ : ℕ)
    (hcap : ∀ q, B₀ ≤ caps q) :
    Law.Close (Law.pi (cachedKernel cache (coordinateLaw target rel caps trials)))
      (Law.pi (cachedKernel cache (fun q =>
        CategoricalCoupling.bernoulli
          (ClosedRelation.retentionRate (rel q) (hrefl q) (trials q) (target q)))))
      ((Fintype.card Q : ℝ) * Real.exp (-(B₀ : ℝ) / Fintype.card U)) := by
  classical
  apply product_close _ _ _ (Real.exp_pos _).le
  intro q
  cases hq : cache q with
  | some b =>
    simp only [cachedKernel, hq]
    exact (Law.close_refl _).mono (Real.exp_pos _).le
  | none =>
    simp only [cachedKernel, hq, coordinateLaw]
    apply (bitLaw_close_exp (rel q) (hrefl q) (target q) (caps q) (trials q)).mono
    apply Real.exp_le_exp.mpr
    have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
    exact div_le_div_of_nonneg_right
      (neg_le_neg (by exact_mod_cast hcap q)) hk.le

end SteinerUpperBound.Covers.Factory

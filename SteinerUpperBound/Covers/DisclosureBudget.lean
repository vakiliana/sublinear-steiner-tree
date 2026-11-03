module

public import SteinerUpperBound.Covers.GlobalCap

@[expose] public section

namespace SteinerUpperBound.Covers.RetentionTree

open SteinerLowerBound
open scoped Classical

variable {Q A B : Type*}

def positiveHeight : DecisionTree Q Bool A → ℕ
  | .leaf _ => 0
  | .query _ next => max (positiveHeight (next false)) (1 + positiveHeight (next true))

theorem positiveHeight_map (t : DecisionTree Q Bool A) (f : A → B) :
    positiveHeight (t.map f) = positiveHeight t := by
  induction t with
  | leaf => rfl
  | query q next ih => simp only [DecisionTree.map, positiveHeight, ih]

theorem positiveHeight_bind (t : DecisionTree Q Bool A) (k : A → DecisionTree Q Bool B)
    (b : ℕ) (hk : ∀ a, positiveHeight (k a) ≤ b) :
    positiveHeight (bind t k) ≤ positiveHeight t + b := by
  induction t with
  | leaf a => simpa [bind, positiveHeight] using hk a
  | query q next ih =>
    simp only [bind, positiveHeight]
    have hf := ih false
    have ht := ih true
    omega

theorem cached_positiveHeight (t : DecisionTree Q Bool A) (cache : Q → Option Bool) :
    positiveHeight (cached t cache) ≤ positiveHeight t := by
  classical
  induction t generalizing cache with
  | leaf => rfl
  | query q next ih =>
    cases he : cache q with
    | none =>
      simp only [cached, Caching.compile, id_eq, he, positiveHeight]
      exact max_le_max (ih false _) (Nat.add_le_add_left (ih true _) 1)
    | some b =>
      simp only [cached, Caching.compile, id_eq, he, positiveHeight]
      have hi := ih b cache
      dsimp only [cached] at hi
      cases b <;> omega

end SteinerUpperBound.Covers.RetentionTree

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open RetentionTree

variable {U : Type*} [Fintype U]

theorem rowTree_positiveHeight (C : ℕ) (w : Fin C → U) :
    positiveHeight (rowTree C w) ≤ 1 := by
  induction C with
  | zero => simp [rowTree, positiveHeight]
  | succ C ih =>
    simpa only [rowTree, positiveHeight, Bool.false_eq_true, Bool.true_eq,
      ↓reduceIte, Nat.add_zero, max_le_iff] using And.intro (ih (Fin.tail w)) (le_refl 1)

theorem sampleTree_positiveHeight (C s : ℕ) (rows : Fin s → Fin C → U) :
    positiveHeight (sampleTree C s rows) ≤ s := by
  induction s with
  | zero => simp [sampleTree, positiveHeight]
  | succ s ih =>
    let k : Option U → DecisionTree U Bool (Fin (s + 1) → Option U) :=
      fun result => (sampleTree C s (Fin.tail rows)).map
        (fun out : Fin s → Option U => Fin.cons result out)
    have hk : ∀ result, positiveHeight (k result) ≤ s := by
      intro result
      dsimp only [k]
      rw [positiveHeight_map]
      exact ih _
    have h := positiveHeight_bind (rowTree C (rows 0))
      k s hk
    have hrow := rowTree_positiveHeight C (rows 0)
    exact h.trans (by omega)

theorem labelsTree_positiveHeight (root : U) (C s : ℕ) (rows : Fin s → Fin C → U) :
    positiveHeight (labelsTree root C s rows) ≤ s := by
  rw [labelsTree, positiveHeight_map]
  exact sampleTree_positiveHeight C s rows

end SteinerUpperBound.Covers.Rejection

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {Q U R : Type*} [Fintype U]

noncomputable def hitHeight (target : Q → U) : DecisionTree Q U R → ℕ
  | .leaf _ => 0
  | .query q next => Finset.univ.sup
      (fun y => (if y = target q then 1 else 0) + hitHeight target (next y))

theorem inner_hitHeight (target : Q → U) (rel : Q → U → U → Prop)
    (q : Q) (B ψ : ℕ) (next : Bool → DecisionTree Q U R) :
    hitHeight target (inner target rel q B ψ next) ≤
      max (hitHeight target (next false)) (1 + hitHeight target (next true)) := by
  classical
  induction B generalizing ψ with
  | zero => exact le_max_left _ _
  | succ B ih =>
    cases ψ with
    | zero => exact le_max_left _ _
    | succ ψ =>
      apply Finset.sup_le
      intro y _
      by_cases hy : y = target q
      · simpa only [hy, ↓reduceIte] using
          (le_max_right (hitHeight target (next false)) (1 + hitHeight target (next true)))
      · by_cases hr : rel q (target q) y
        · simpa only [hy, hr, ↓reduceIte, zero_add] using ih ψ
        · simpa only [hy, hr, ↓reduceIte, zero_add] using ih (ψ + 1)

theorem expanded_hitHeight (target : Q → U) (rel : Q → U → U → Prop)
    (caps trials : Q → ℕ) (t : DecisionTree Q Bool R) :
    hitHeight target (expanded target rel caps trials t) ≤ positiveHeight t := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    exact (inner_hitHeight target rel q (caps q) (trials q) _).trans
      (max_le_max (ih false) (Nat.add_le_add_left (ih true) 1))

theorem run_retained_potential (target : Q → U) (B : ℕ) (s : State Q U R)
    (w : Fin B → U) (hf : Fresh target s.2 s.1) :
    (run target B s w).2.card + hitHeight target (run target B s w).1 ≤
      s.2.card + hitHeight target s.1 := by
  classical
  induction B generalizing s with
  | zero => rfl
  | succ B ih =>
    rcases s with ⟨t, S⟩
    cases t with
    | leaf r => rw [run_leaf]
    | query q next =>
      have hi := ih (step target (.query q next, S) (w 0)) (Fin.tail w) (hf.2 (w 0))
      have hs := Finset.le_sup
        (f := fun y => (if y = target q then 1 else 0) + hitHeight target (next y))
        (Finset.mem_univ (w 0))
      by_cases hy : w 0 = target q
      · have hc : (insert q S).card = S.card + 1 := Finset.card_insert_of_notMem hf.1
        simp only [step, hy, ↓reduceIte, hc] at hi
        simp only [hy, ↓reduceIte] at hs
        simp only [run, step, hy, ↓reduceIte, hitHeight]
        omega
      · simp only [step, hy, ↓reduceIte] at hi
        simp only [hy, ↓reduceIte, zero_add] at hs
        simp only [run, step, hy, ↓reduceIte, hitHeight]
        omega

theorem new_disclosures_le_positiveHeight [Fintype Q]
    (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) (w : Fin B → U) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (run target B s w).2.card - s.2.card ≤ positiveHeight t := by
  dsimp only
  let s : State Q U R :=
    (expanded target rel caps trials (cached t cache), initiallyRetained cache)
  have hp := run_retained_potential target B s w (expanded_cached_fresh _ _ _ _ _ _)
  have hh := (expanded_hitHeight target rel caps trials (cached t cache)).trans
    (cached_positiveHeight t cache)
  change hitHeight target s.1 ≤ positiveHeight t at hh
  change (run target B s w).2.card - s.2.card ≤ positiveHeight t
  omega

theorem cached_factory_cap_probability [Fintype Q] [Nonempty U]
    (dummy : U) (target : Q → U) (rel : Q → U → U → Prop) (caps trials : Q → ℕ)
    (t : DecisionTree Q Bool R) (cache : Q → Option Bool) (B : ℕ) :
    let s : State Q U R :=
      (expanded target rel caps trials (cached t cache), initiallyRetained cache)
    (tape (Law.uniform U) B).prob {w | Pending (run target B s w)} ≤
      Real.exp ((positiveHeight t : ℝ) - (B : ℝ) / (2 * Fintype.card U)) := by
  dsimp only
  let s : State Q U R :=
    (expanded target rel caps trials (cached t cache), initiallyRetained cache)
  have hsub : {w | Pending (run target B s w)} ⊆
      {w | Pending (run target B s w) ∧
        (((run target B s w).2.card - s.2.card : ℕ) : ℝ) ≤ positiveHeight t} := by
    intro w hw
    refine ⟨hw, ?_⟩
    exact_mod_cast new_disclosures_le_positiveHeight target rel caps trials t cache B w
  exact (Law.prob_mono _ hsub).trans
    (cached_factory_cap_tail dummy target rel caps trials t cache B (positiveHeight t))

theorem sampler_factory_cap_budget {U : Type*} [Fintype U] [Nonempty U]
    (root : U) (target : U → U) (rel : U → U → U → Prop) (caps trials : U → ℕ)
    (C s : ℕ) (rows : Fin s → Fin C → U) (cache : U → Option Bool)
    (β : ℝ) (hβ : 0 < β) :
    let B := globalDrawBudget (Fintype.card U) s β
    let start : State U U (Fin s → U) :=
      (expanded target rel caps trials (cached (Rejection.labelsTree root C s rows) cache),
        initiallyRetained cache)
    (tape (Law.uniform U) B).prob {w | Pending (run target B start w)} ≤ β := by
  dsimp only
  let B := globalDrawBudget (Fintype.card U) s β
  let t := Rejection.labelsTree root C s rows
  let start : State U U (Fin s → U) :=
    (expanded target rel caps trials (cached t cache), initiallyRetained cache)
  have hheight : positiveHeight t ≤ s := Rejection.labelsTree_positiveHeight _ _ _ _
  have hsub : {w | Pending (run target B start w)} ⊆
      {w | Pending (run target B start w) ∧
        (((run target B start w).2.card - start.2.card : ℕ) : ℝ) ≤ s} := by
    intro w hw
    refine ⟨hw, ?_⟩
    exact_mod_cast (new_disclosures_le_positiveHeight target rel caps trials t cache B w).trans hheight
  exact (Law.prob_mono _ hsub).trans
    (cached_factory_cap_budget root target rel caps trials t cache s β hβ)

end SteinerUpperBound.Covers.Factory

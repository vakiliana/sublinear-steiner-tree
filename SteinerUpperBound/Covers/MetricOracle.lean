module

public import SteinerUpperBound.Covers.GlobalCap
public import SteinerUpperBound.Covers.Actual

@[expose] public section

namespace SteinerUpperBound.Covers.Factory

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {V : Type*}

/-- The executable oracle-facing version of one fixed private terminal tape.
Only non-target proposals require a metric query. -/
noncomputable def distanceTree (I : Instance V) (r : ℝ) (x : Terminal I) :
    (B : ℕ) → ℕ → (Fin B → Terminal I) → DecisionTree (Sym2 V) ℝ Bool
  | 0, _, _ => .leaf false
  | _ + 1, 0, _ => .leaf false
  | B + 1, ψ + 1, w =>
      if w 0 = x then .leaf true
      else .query (Sym2.mk x.val (w 0).val) (fun d =>
        if d ≤ r then distanceTree I r x B ψ (Fin.tail w)
        else distanceTree I r x B (ψ + 1) (Fin.tail w))

theorem distanceTree_output (I : Instance V) (r : ℝ) (x : Terminal I)
    (B ψ : ℕ) (w : Fin B → Terminal I) :
    (distanceTree I r x B ψ w).output I.weight =
      (scan (near I r) x B ψ w).getD false := by
  classical
  induction B generalizing ψ with
  | zero => cases ψ <;> rfl
  | succ B ih =>
    cases ψ with
    | zero => rfl
    | succ ψ =>
      by_cases hx : w 0 = x
      · simp [distanceTree, scan, hx, DecisionTree.output]
      · by_cases hr : I.distance x.val (w 0).val ≤ r
        · simpa only [distanceTree, scan, hx, near, hr, ↓reduceIte,
            DecisionTree.output, I.weight_mk] using ih ψ (Fin.tail w)
        · simpa only [distanceTree, scan, hx, near, hr, ↓reduceIte,
            DecisionTree.output, I.weight_mk] using ih (ψ + 1) (Fin.tail w)

theorem distanceTree_queries_le_draws (I : Instance V) (r : ℝ) (x : Terminal I)
    (B ψ : ℕ) (w : Fin B → Terminal I) :
    (distanceTree I r x B ψ w).queries I.weight ≤ draws (near I r) x B ψ w := by
  classical
  induction B generalizing ψ with
  | zero => cases ψ <;> simp [distanceTree, draws, DecisionTree.queries, DecisionTree.transcript]
  | succ B ih =>
    cases ψ with
    | zero => simp [distanceTree, draws, DecisionTree.queries, DecisionTree.transcript]
    | succ ψ =>
      by_cases hx : w 0 = x
      · simp [distanceTree, draws, hx, DecisionTree.queries, DecisionTree.transcript]
      · by_cases hr : I.distance x.val (w 0).val ≤ r
        · have hi := ih ψ (Fin.tail w)
          simpa only [distanceTree, draws, hx, near, hr, ↓reduceIte,
            DecisionTree.queries, DecisionTree.transcript, I.weight_mk,
            List.length_cons, Nat.add_comm] using Nat.add_le_add_right hi 1
        · have hi := ih (ψ + 1) (Fin.tail w)
          simpa only [distanceTree, draws, hx, near, hr, ↓reduceIte,
            DecisionTree.queries, DecisionTree.transcript, I.weight_mk,
            List.length_cons, Nat.add_comm] using Nat.add_le_add_right hi 1

theorem distanceTree_queries_le (I : Instance V) (r : ℝ) (x : Terminal I)
    (B ψ : ℕ) (w : Fin B → Terminal I) :
    (distanceTree I r x B ψ w).queries I.weight ≤ B := by
  letI : Nonempty (Terminal I) := ⟨x⟩
  exact (distanceTree_queries_le_draws I r x B ψ w).trans (draws_le _ _ _ _ _)

theorem family_private_tapes {Q U : Type*} [Fintype Q] [Fintype U] [Nonempty U]
    (target : Q → U) (rel : Q → U → U → Prop) (trials : Q → ℕ)
    (cache : Q → Option Bool) (B : ℕ) :
    ((tape (Law.uniform U) B).iid Q).map
      (fun tapes q => match cache q with
        | some b => b
        | none => (scan (rel q) (target q) B (trials q) (tapes q)).getD false) =
      Law.pi (cachedKernel cache (coordinateLaw target rel (fun _ => B) trials)) := by
  classical
  calc
    _ = Law.pi (fun q : Q => (tape (Law.uniform U) B).map (fun w =>
        match cache q with
        | some b => b
        | none => (scan (rel q) (target q) B (trials q) w).getD false)) :=
      LawOperations.pi_map (fun _ : Q => tape (Law.uniform U) B)
        (fun q w => match cache q with
          | some b => b
          | none => (scan (rel q) (target q) B (trials q) w).getD false)
    _ = _ := by
      congr 1
      funext q
      cases hq : cache q with
      | some b =>
        simp only [cachedKernel, hq]
        exact map_const _ _
      | none =>
        simp only [cachedKernel, hq, coordinateLaw, bitLaw]
        rw [← scan_law, LawOperations.map_comp]

end SteinerUpperBound.Covers.Factory

namespace SteinerUpperBound.Covers.ClosedRelation

open SteinerLowerBound
open scoped Classical BigOperators

variable {U : Type*} [Fintype U]

noncomputable def otherDegree (R : U → U → Prop) (x : U) : ℕ :=
  ((neighborhood R x).erase x).card

theorem degree_eq_other_add_one (R : U → U → Prop) (hrefl : ∀ x, R x x) (x : U) :
    degree R x = otherDegree R x + 1 := by
  classical
  exact (Finset.card_erase_add_one (by simp [neighborhood, hrefl])).symm

theorem retentionRate_otherDegree (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (ψ : ℕ) (x : U) :
    (retentionRate R hrefl ψ x : ℝ) =
      1 - ((otherDegree R x : ℝ) / ((otherDegree R x : ℝ) + 1)) ^ ψ := by
  dsimp [retentionRate, reciprocalRate]
  rw [degree_eq_other_add_one R hrefl x, Nat.cast_add, Nat.cast_one]
  have hd : (otherDegree R x : ℝ) + 1 ≠ 0 := by positivity
  congr 2
  field_simp
  ring

end SteinerUpperBound.Covers.ClosedRelation

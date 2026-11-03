module

public import SteinerUpperBound.Matching.Padded.RankTails

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.UniformOrder

open SteinerLowerBound
open scoped Classical BigOperators

variable {E : Type*} [Fintype E]

/-- This order is used only in the coupling proof, never by the padded program. -/
noncomputable def order {Q : ℕ} (ranks : E → Fin Q) : Rank E :=
  if h : Function.Injective ranks then
    letI : LinearOrder E := LinearOrder.lift' ranks h
    (Fintype.orderIsoFinOfCardEq E rfl).symm.toEquiv
  else Fintype.equivFin E

theorem order_lt {Q : ℕ} (ranks : E → Fin Q) (h : Function.Injective ranks) (e f : E) :
    order ranks e < order ranks f ↔ ranks e < ranks f := by
  rw [order, dite_eq_left h]
  letI : LinearOrder E := LinearOrder.lift' ranks h
  exact (Fintype.orderIsoFinOfCardEq E rfl).symm.lt_iff_lt

theorem rank_ext (ρ σ : Rank E)
    (h : ∀ e f, ρ e < ρ f ↔ σ e < σ f) : ρ = σ := by
  let δ : Fin (Fintype.card E) ≃o Fin (Fintype.card E) :=
    { toEquiv := ρ.symm.trans σ
      map_rel_iff' := by
        intro i j
        have hh := (not_congr (h (ρ.symm j) (ρ.symm i))).symm
        simpa only [Equiv.apply_symm_apply, not_lt, Equiv.trans_apply] using hh }
  have hd : δ = OrderIso.refl (Fin (Fintype.card E)) := Subsingleton.elim _ _
  ext e
  have he := congrArg (fun q : Fin (Fintype.card E) ≃o Fin (Fintype.card E) => q (ρ e)) hd
  simpa [δ] using congrArg Fin.val he.symm

def reindex {Q : ℕ} (g : Equiv.Perm E) : (E → Fin Q) ≃ (E → Fin Q) where
  toFun r e := r (g e)
  invFun r e := r (g.symm e)
  left_inv r := by funext e; simp
  right_inv r := by funext e; simp

theorem injective_reindex {Q : ℕ} (g : Equiv.Perm E) (r : E → Fin Q) :
    Function.Injective (reindex g r) ↔ Function.Injective r := by
  constructor
  · intro h e f hef
    have hh : reindex g r (g.symm e) = reindex g r (g.symm f) := by simpa [reindex] using hef
    have he := h hh
    exact g.symm.injective he
  · exact fun h => h.comp g.injective

theorem order_reindex {Q : ℕ} (g : Equiv.Perm E) (r : E → Fin Q)
    (hr : Function.Injective r) : order (reindex g r) = g.trans (order r) := by
  apply rank_ext
  intro e f
  rw [order_lt _ ((injective_reindex g r).mpr hr), Equiv.trans_apply, Equiv.trans_apply,
    order_lt r hr]
  rfl

def postEquiv (κ : Equiv.Perm (Fin (Fintype.card E))) : Rank E ≃ Rank E where
  toFun ρ := ρ.trans κ
  invFun ρ := ρ.trans κ.symm
  left_inv ρ := by ext e; simp
  right_inv ρ := by ext e; simp

theorem expect_commute {A B : Type*} [Fintype A] [Fintype B] (μ : Law A) (ν : Law B)
    (f : A → B → ℝ) :
    μ.expect (fun a => ν.expect (f a)) = ν.expect (fun b => μ.expect (fun a => f a b)) := by
  unfold Law.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable (Q : ℕ) (hQ : 0 < Q)

theorem reindex_expect (g : Equiv.Perm E) (f : (E → Fin Q) → ℝ) :
    (UniformRanks.law Q hQ (E := E)).expect (fun r => f (reindex g r)) =
      (UniformRanks.law Q hQ (E := E)).expect f := by
  have hm (r : E → Fin Q) :
      (UniformRanks.law Q hQ (E := E)).mass r = ((Q : ℝ)⁻¹) ^ Fintype.card E := by
    simp [UniformRanks.law, Law.pi, UniformRanks.mass]
  unfold Law.expect
  simp only [hm]
  exact (reindex g).sum_comp (fun r => ((Q : ℝ)⁻¹) ^ Fintype.card E * f r)

/-- Conditional on no ties, the induced priority order is exactly uniform. -/
theorem no_tie_expect (f : Rank E → ℝ) :
    (UniformRanks.law Q hQ (E := E)).expect
      (fun r => if Function.Injective r then f (order r) else 0) =
        (UniformRanks.law Q hQ (E := E)).prob {r | Function.Injective r} *
          (Rank.uniform (E := E)).expect f := by
  classical
  let μ := UniformRanks.law Q hQ (E := E)
  let β : Rank E := Fintype.equivFin E
  let Φ : (E → Fin Q) → ℝ := fun r => if Function.Injective r then f (order r) else 0
  have hinv (g : Equiv.Perm E) :
      μ.expect (fun r => if Function.Injective r then f (g.trans (order r)) else 0) = μ.expect Φ := by
    rw [← reindex_expect Q hQ g Φ]
    congr 1
    funext r
    by_cases hr : Function.Injective r
    · have hgr := (injective_reindex g r).mpr hr
      simp only [Φ, hr, hgr, ↓reduceIte, order_reindex g r hr]
    · have hgr : ¬ Function.Injective (reindex g r) := fun h => hr ((injective_reindex g r).mp h)
      simp only [Φ, hr, hgr, ↓reduceIte]
  have hinner (r : E → Fin Q) :
      (Rank.uniform (E := E)).expect
        (fun τ => if Function.Injective r then f ((τ.trans β.symm).trans (order r)) else 0) =
          if Function.Injective r then (Rank.uniform (E := E)).expect f else 0 := by
    by_cases hr : Function.Injective r
    · simp only [hr, ↓reduceIte, Equiv.trans_assoc]
      exact FiniteAveraging.uniform_expect_equiv (postEquiv (β.symm.trans (order r))) f
    · simp only [hr, ↓reduceIte, Law.expect_const]
  calc
    _ = (Rank.uniform (E := E)).expect (fun τ => μ.expect
        (fun r => if Function.Injective r then f ((τ.trans β.symm).trans (order r)) else 0)) := by
      simp_rw [hinv]
      exact (Law.expect_const _ _).symm
    _ = μ.expect (fun r => (Rank.uniform (E := E)).expect
        (fun τ => if Function.Injective r then f ((τ.trans β.symm).trans (order r)) else 0)) :=
      expect_commute _ _ _
    _ = μ.expect (fun r => if Function.Injective r then (Rank.uniform (E := E)).expect f else 0) := by
      simp_rw [hinner]
    _ = _ := by
      have he (r : E → Fin Q) :
          (if Function.Injective r then (Rank.uniform (E := E)).expect f else 0) =
            (if Function.Injective r then (1 : ℝ) else 0) * (Rank.uniform (E := E)).expect f := by
        split_ifs <;> simp
      simp_rw [he]
      have hp : μ.expect (fun r => if Function.Injective r then 1 else 0) =
          μ.prob {r | Function.Injective r} := by
        rw [Law.prob_eq_expect]
        apply congrArg μ.expect
        funext r
        by_cases hr : Function.Injective r <;> simp [hr]
      rw [Law.expect_mul_const, hp]

end SteinerUpperBound.Matching.Padded.UniformOrder

module

public import SteinerUpperBound.Matching.Residual
public import SteinerLowerBound.IndependentTrials

@[expose] public section

namespace SteinerUpperBound.Matching

open SteinerLowerBound
open scoped Classical BigOperators

namespace FiniteAveraging

variable {Ω A : Type*} [Fintype Ω]

noncomputable def indicator (P : Ω → Prop) (ω : Ω) : ℝ := if P ω then 1 else 0

theorem expect_indicator (μ : Law Ω) (P : Ω → Prop) :
    μ.expect (indicator P) = μ.prob {ω | P ω} := by
  classical
  unfold Law.expect Law.prob indicator
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem expect_sum (μ : Law Ω) (s : Finset A) (f : A → Ω → ℝ) :
    μ.expect (fun ω => ∑ a ∈ s, f a ω) = ∑ a ∈ s, μ.expect (f a) := by
  simp only [Law.expect, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem uniform_expect_equiv [Nonempty Ω] (e : Ω ≃ Ω) (f : Ω → ℝ) :
    (Law.uniform Ω).expect (fun ω => f (e ω)) = (Law.uniform Ω).expect f := by
  unfold Law.expect Law.uniform
  exact e.sum_comp (fun ω => (Fintype.card Ω : ℝ)⁻¹ * f ω)

theorem card_filter_indicator (s : Finset A) (P : A → Prop) :
    ((s.filter P).card : ℝ) = ∑ a ∈ s, indicator P a := by
  classical
  rw [Finset.card_filter]
  push_cast
  rfl

end FiniteAveraging

variable {E : Type*} [Fintype E]

namespace Rank

noncomputable def suffix (E : Type*) [Fintype E] (k : ℕ) :
    Finset (Fin (Fintype.card E)) := Finset.univ.filter fun i => k ≤ i.val

@[simp] theorem mem_suffix (k : ℕ) (i : Fin (Fintype.card E)) :
    i ∈ suffix E k ↔ k ≤ i.val := by simp [suffix]

@[simp] theorem card_suffix (k : ℕ) :
    (suffix E k).card = Fintype.card E - k := by
  classical
  by_cases hk : k < Fintype.card E
  · have heq : suffix E k = Finset.Ici (⟨k, hk⟩ : Fin (Fintype.card E)) := by
      ext i
      simp [Fin.le_def]
    rw [heq, Fin.card_Ici]
  · have heq : suffix E k = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hki : k ≤ i.val := (mem_suffix k i).mp hi
      omega
    simp [heq, Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hk)]

end Rank

end SteinerUpperBound.Matching

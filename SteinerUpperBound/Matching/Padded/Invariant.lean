module

public import SteinerUpperBound.Matching.Padded.Batch

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace FiniteLaw

theorem expect_zero_on_support {A : Type*} [Fintype A] (μ : Law A) (f : A → ℝ)
    (h : ∀ a, 0 < μ.mass a → f a = 0) : μ.expect f = 0 := by
  unfold Law.expect
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : 0 < μ.mass a
  · simp [h a ha]
  · have hz := le_antisymm (le_of_not_gt ha) (μ.nonneg a)
    simp [hz]

end FiniteLaw

namespace Program

theorem supported_of_zero_bad {C A : Type*} (p : Program C A) (P : A → Prop)
    (h : p.expect (fun a => if P a then 0 else 1) = 0) : p.Supported P := by
  classical
  intro x
  by_contra hx
  have hsingle : p.mass x ≤ p.expect (fun a => if P a then 0 else 1) := by
    change p.mass x ≤ ∑ y, p.mass y * (if P (p.output y) then 0 else 1)
    calc
      p.mass x = p.mass x * (if P (p.output x) then 0 else 1) := by simp [hx]
      _ ≤ _ := Finset.single_le_sum
        (f := fun y => p.mass y * (if P (p.output y) then (0 : ℝ) else 1))
        (fun y _ => mul_nonneg (p.mass_nonneg y) (by split_ifs <;> norm_num))
        (Finset.mem_univ x)
  rw [h] at hsingle
  exact (not_le_of_gt (p.mass_pos x)) hsingle

end Program

namespace Cache

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

structure Invariant (s : Cache S Q) : Prop where
  legal : Legal S Q s
  records : Records S Q s
  ready : Ready S Q s

theorem empty_invariant (hQ : 0 < Q) : Invariant S Q (empty S Q) :=
  ⟨empty_legal S Q hQ, empty_records S Q, empty_ready S Q⟩

theorem extend_invariant [Fintype E] (hQ : 0 < Q) (height : ℕ) (s : Cache S Q) (v : V)
    (hs : Invariant S Q s) (hlen : Fintype.card E ≤ 2 ^ height) :
    (extend S Q hQ height v s).Supported (Invariant S Q) := by
  classical
  by_cases hb : Buckets.bound (s.level v + 1) ≤ Q
  · apply Program.supported_of_zero_bad
    have hj := Posterior.extension_joint S Q hQ height s v hb
      (fun t _ => if Invariant S Q t then (0 : ℝ) else 1)
    simp only [Law.expect_const] at hj
    rw [← hj]
    apply FiniteLaw.expect_zero_on_support
    intro ranks hm
    have hc := completion_consistent S Q hQ s hs.legal ranks hm
    have hl := Posterior.ideal_legal S Q height s v ranks hs.legal hc hb
    have hr := Posterior.ideal_records_ready S Q height s v ranks hc hs.records hs.ready hlen
    simp only [show Invariant S Q (Posterior.ideal S Q height s v ranks) from
      ⟨hl, hr.1, hr.2⟩, ↓reduceIte]
  · simpa only [extend, hb, ↓reduceIte] using Program.supported_ret
      (C := Command S) s (Invariant S Q) hs

end Cache

end SteinerUpperBound.Matching.Padded

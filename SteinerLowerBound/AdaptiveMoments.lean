module

public import SteinerLowerBound.AdaptiveProposals

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace ProposalTree

variable {U R : Type*}

noncomputable def budget (u : U) : ProposalTree U R → ℝ
  | .leaf _ => 0
  | .coin _ yes no => max (yes.budget u) (no.budget u)
  | .inspect H p no reject retain =>
      (if u ∈ H then (p : ℝ) else 0) +
        max (no.budget u) (max (reject.budget u) (retain.budget u))

theorem budget_nonneg (t : ProposalTree U R) (u : U) : 0 ≤ t.budget u := by
  induction t with
  | leaf => simp [budget]
  | coin p yes no hy hn => exact le_max_of_le_left hy
  | inspect H p no reject retain hn hr ht =>
      apply add_nonneg
      · split_ifs <;> simp_all [p.property.1]
      · exact le_max_of_le_left hn

noncomputable def moment (w : U → Rate) (u : U) (k j : ℕ) :
    ProposalTree U R → ℝ
  | .leaf _ => (k.choose j : ℝ)
  | .coin p yes no =>
      (p : ℝ) * yes.moment w u k j + (1 - (p : ℝ)) * no.moment w u k j
  | .inspect H p no reject retain =>
      let a := (retention H w : ℝ)
      let k' := k + if u ∈ H then 1 else 0
      (p : ℝ) * (a * retain.moment w u k' j + (1 - a) * reject.moment w u k' j) +
        (1 - (p : ℝ)) * no.moment w u k j

theorem moment_zero (t : ProposalTree U R) (w : U → Rate) (u : U) (k : ℕ) :
    t.moment w u k 0 = 1 := by
  induction t generalizing k with
  | leaf => simp [moment]
  | coin p yes no hy hn => simp only [moment, hy, hn]; ring
  | inspect H p no reject retain hn hr ht => simp only [moment, hn, hr, ht]; ring

theorem moment_pascal (t : ProposalTree U R) (w : U → Rate) (u : U) (k j : ℕ) :
    t.moment w u (k + 1) (j + 1) =
      t.moment w u k (j + 1) + t.moment w u k j := by
  induction t generalizing k with
  | leaf => simp [moment, Nat.choose_succ_succ, add_comm]
  | coin p yes no hy hn => simp only [moment, hy, hn]; ring
  | inspect H p no reject retain hn hr ht =>
      simp only [moment]
      have hshift : k + 1 + (if u ∈ H then 1 else 0) =
          (k + if u ∈ H then 1 else 0) + 1 := by omega
      rw [hshift, ht, hr, hn]
      ring

theorem mix_le {a b c p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (ha : a ≤ c) (hb : b ≤ c) :
    p * a + (1 - p) * b ≤ c := by
  have h₁ := mul_le_mul_of_nonneg_left ha hp₀
  have h₂ := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hp₁)
  nlinarith

theorem moment_bound (t : ProposalTree U R) (w : U → Rate) (u : U)
    (B : ℝ) (hB₀ : 0 ≤ B) (hB : t.budget u ≤ B) (j : ℕ) :
    t.moment w u 0 j ≤ B ^ j := by
  induction t generalizing B j with
  | leaf r =>
      cases j <;> simp [moment, hB₀]
  | coin p yes no hy hn =>
      simp only [budget, max_le_iff] at hB
      exact mix_le p.property.1 p.property.2 (hy B hB₀ hB.1 j) (hn B hB₀ hB.2 j)
  | inspect H p no reject retain hn hr ht =>
      by_cases hu : u ∈ H
      · have hb : (p : ℝ) ≤ B := by
          have hmax : 0 ≤ max (no.budget u) (max (reject.budget u) (retain.budget u)) :=
            le_max_of_le_left (no.budget_nonneg u)
          simp only [budget, hu, ↓reduceIte] at hB
          linarith
        let b := B - (p : ℝ)
        have hb₀ : 0 ≤ b := sub_nonneg.mpr hb
        have hc :
            no.budget u ≤ b ∧ reject.budget u ≤ b ∧ retain.budget u ≤ b := by
          simp only [budget, hu, ↓reduceIte] at hB
          dsimp [b]
          constructor
          · linarith [le_max_left (no.budget u) (max (reject.budget u) (retain.budget u))]
          constructor
          · linarith [le_max_right (no.budget u) (max (reject.budget u) (retain.budget u)),
              le_max_left (reject.budget u) (retain.budget u)]
          · linarith [le_max_right (no.budget u) (max (reject.budget u) (retain.budget u)),
              le_max_right (reject.budget u) (retain.budget u)]
        cases j with
        | zero => simp [moment_zero]
        | succ j =>
            have hn' := hn b hb₀ hc.1 (j + 1)
            have hr' : reject.moment w u 1 (j + 1) ≤ b ^ (j + 1) + b ^ j := by
              rw [show 1 = 0 + 1 from rfl, moment_pascal]
              exact add_le_add (hr b hb₀ hc.2.1 (j + 1)) (hr b hb₀ hc.2.1 j)
            have ht' : retain.moment w u 1 (j + 1) ≤ b ^ (j + 1) + b ^ j := by
              rw [show 1 = 0 + 1 from rfl, moment_pascal]
              exact add_le_add (ht b hb₀ hc.2.2 (j + 1)) (ht b hb₀ hc.2.2 j)
            have hm := mix_le (retention H w).property.1 (retention H w).property.2 ht' hr'
            calc
              _ ≤ (p : ℝ) * (b ^ (j + 1) + b ^ j) + (1 - (p : ℝ)) * b ^ (j + 1) := by
                simp only [moment, hu, ↓reduceIte, Nat.zero_add]
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hm p.property.1)
                  (mul_le_mul_of_nonneg_left hn' (sub_nonneg.mpr p.property.2))
              _ = B * b ^ j := by dsimp [b]; rw [pow_succ]; ring
              _ ≤ B * B ^ j := mul_le_mul_of_nonneg_left
                (pow_le_pow_left₀ hb₀ (by dsimp [b]; linarith [p.property.1]) j) hB₀
              _ = B ^ (j + 1) := by rw [pow_succ]; ring
      · have hc : no.budget u ≤ B ∧ reject.budget u ≤ B ∧ retain.budget u ≤ B := by
          simpa only [budget, hu, ↓reduceIte, zero_add, max_le_iff] using hB
        have hm := mix_le (retention H w).property.1 (retention H w).property.2
          (ht B hB₀ hc.2.2 j) (hr B hB₀ hc.2.1 j)
        simpa only [moment, hu, ↓reduceIte, add_zero] using
          mix_le p.property.1 p.property.2 hm (hn B hB₀ hc.1 j)

noncomputable def execute (w : U → Rate) (k : U → ℕ)
    (f : R → (U → ℕ) → ℝ) : ProposalTree U R → ℝ
  | .leaf r => f r k
  | .coin p yes no =>
      (p : ℝ) * yes.execute w k f + (1 - (p : ℝ)) * no.execute w k f
  | .inspect H p no reject retain =>
      let a := (retention H w : ℝ)
      (p : ℝ) * (a * retain.execute w (increment k H) f +
          (1 - a) * reject.execute w (increment k H) f) +
        (1 - (p : ℝ)) * no.execute w k f

theorem execute_const (t : ProposalTree U R) (w : U → Rate) (k : U → ℕ) (c : ℝ) :
    t.execute w k (fun _ _ => c) = c := by
  induction t generalizing k with
  | leaf => rfl
  | coin p yes no hy hn => simp only [execute, hy, hn]; ring
  | inspect H p no reject retain hn hr ht => simp only [execute, hn, hr, ht]; ring

theorem execute_mono (t : ProposalTree U R) (w : U → Rate) (k : U → ℕ)
    {f g : R → (U → ℕ) → ℝ} (h : ∀ r k, f r k ≤ g r k) :
    t.execute w k f ≤ t.execute w k g := by
  induction t generalizing k with
  | leaf r => exact h r k
  | coin p yes no hy hn =>
      exact add_le_add (mul_le_mul_of_nonneg_left (hy k) p.property.1)
        (mul_le_mul_of_nonneg_left (hn k) (sub_nonneg.mpr p.property.2))
  | inspect H p no reject retain hn hr ht =>
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ p.property.1
        exact add_le_add
          (mul_le_mul_of_nonneg_left (ht _) (retention H w).property.1)
          (mul_le_mul_of_nonneg_left (hr _) (sub_nonneg.mpr (retention H w).property.2))
      · exact mul_le_mul_of_nonneg_left (hn _) (sub_nonneg.mpr p.property.2)

theorem execute_add (t : ProposalTree U R) (w : U → Rate) (k : U → ℕ)
    (f g : R → (U → ℕ) → ℝ) :
    t.execute w k (fun r k => f r k + g r k) =
      t.execute w k f + t.execute w k g := by
  induction t generalizing k with
  | leaf => rfl
  | coin p yes no hy hn => simp only [execute, hy, hn]; ring
  | inspect H p no reject retain hn hr ht => simp only [execute, hn, hr, ht]; ring

theorem execute_sum (t : ProposalTree U R) (w : U → Rate) (k : U → ℕ)
    {J : Type*} (I : Finset J) (f : J → R → (U → ℕ) → ℝ) :
    t.execute w k (fun r k => ∑ j ∈ I, f j r k) =
      ∑ j ∈ I, t.execute w k (f j) := by
  induction I using Finset.induction_on with
  | empty => simp [execute_const]
  | @insert j I hj ih => simp only [Finset.sum_insert hj, execute_add, ih]

theorem execute_choose (t : ProposalTree U R) (w : U → Rate) (k : U → ℕ)
    (u : U) (j : ℕ) :
    t.execute w k (fun _ k => (Nat.choose (k u) j : ℝ)) = t.moment w u (k u) j := by
  induction t generalizing k with
  | leaf => rfl
  | coin p yes no hy hn => simp only [execute, moment, hy, hn]
  | inspect H p no reject retain hn hr ht =>
      simp only [execute, moment, hn, hr, ht, increment]

noncomputable def overflowPayoff (s : ℕ) (_ : R) (k : U → ℕ) : ℝ := by
  classical
  exact if ∃ u, s < k u then 1 else 0

theorem overflow_bound [Fintype U] (t : ProposalTree U R) (w : U → Rate)
    (G : ℝ) (hG₀ : 0 ≤ G) (hG : ∀ u, t.budget u ≤ G) (s : ℕ) :
    t.execute w (fun _ => 0) (overflowPayoff s) ≤
      Fintype.card U * G ^ (s + 1) := by
  classical
  calc
    _ ≤ t.execute w (fun _ => 0) (fun _ k => ∑ u, (Nat.choose (k u) (s + 1) : ℝ)) := by
      apply execute_mono
      intro r k
      unfold overflowPayoff
      split_ifs with h
      · obtain ⟨u, hu⟩ := h
        have hchoose : 1 ≤ (Nat.choose (k u) (s + 1) : ℝ) := by
          exact_mod_cast Nat.choose_pos (by omega : s + 1 ≤ k u)
        exact hchoose.trans (Finset.single_le_sum
          (f := fun v => (Nat.choose (k v) (s + 1) : ℝ))
          (fun v _ => Nat.cast_nonneg _) (Finset.mem_univ u))
      · exact Finset.sum_nonneg fun u _ => Nat.cast_nonneg _
    _ = ∑ u, t.moment w u 0 (s + 1) := by rw [execute_sum]; simp only [execute_choose]
    _ ≤ ∑ _u : U, G ^ (s + 1) :=
      Finset.sum_le_sum fun u _ => t.moment_bound w u G hG₀ (hG u) (s + 1)
    _ = _ := by simp

end ProposalTree

end SteinerLowerBound

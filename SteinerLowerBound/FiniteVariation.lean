module

public import SteinerLowerBound.FiniteProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem close_of_one_sided (μ ν : Law Ω) (ε : ℝ)
    (h : ∀ E, μ.prob E - ν.prob E ≤ ε) : Close μ ν ε := by
  intro E
  rw [abs_le]
  refine ⟨?_, h E⟩
  have hc := h Eᶜ
  rw [prob_compl, prob_compl] at hc
  linarith

theorem expect_difference_le (μ ν : Law Ω) (f : Ω → ℝ)
    (hf₀ : ∀ ω, 0 ≤ f ω) (hf₁ : ∀ ω, f ω ≤ 1) :
    μ.expect f - ν.expect f ≤
      μ.prob {ω | ν.mass ω ≤ μ.mass ω} - ν.prob {ω | ν.mass ω ≤ μ.mass ω} := by
  classical
  simp only [expect, prob, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ν.mass ω ≤ μ.mass ω
  · simp only [Set.mem_ofPred_eq, h, ↓reduceIte]
    nlinarith [hf₁ ω]
  · simp only [Set.mem_ofPred_eq, h, ↓reduceIte, sub_zero]
    nlinarith [hf₀ ω, lt_of_not_ge h]

theorem Close.expect_bound {μ ν : Law Ω} {ε : ℝ} (h : Close μ ν ε)
    (f : Ω → ℝ) (hf₀ : ∀ ω, 0 ≤ f ω) (hf₁ : ∀ ω, f ω ≤ 1) :
    |μ.expect f - ν.expect f| ≤ ε := by
  rw [abs_le]
  constructor
  · have hb := (expect_difference_le ν μ f hf₀ hf₁).trans
      (abs_le.mp (h.symm {ω | μ.mass ω ≤ ν.mass ω})).2
    linarith
  · exact (expect_difference_le μ ν f hf₀ hf₁).trans
      (abs_le.mp (h {ω | ν.mass ω ≤ μ.mass ω})).2

theorem Close.bind_same (μ : Law Ω) (k l : Ω → Law Γ) (δ : Ω → ℝ)
    (h : ∀ ω, Close (k ω) (l ω) (δ ω)) :
    Close (μ.bind k) (μ.bind l) (μ.expect δ) := by
  intro E
  rw [prob_bind, prob_bind, ← expect_sub]
  exact (μ.abs_expect_le _).trans (μ.expect_mono (fun ω => h ω E))

theorem Close.bind {μ ν : Law Ω} {ε δ : ℝ} (h : Close μ ν ε)
    (k l : Ω → Law Γ) (hk : ∀ ω, Close (k ω) (l ω) δ) :
    Close (μ.bind k) (ν.bind l) (ε + δ) := by
  intro E
  rw [prob_bind, prob_bind]
  have h₁ := h.expect_bound (fun ω => (k ω).prob E)
    (fun ω => (k ω).prob_nonneg E) (fun ω => (k ω).prob_le_one E)
  have h₂ : |ν.expect (fun ω => (k ω).prob E) - ν.expect (fun ω => (l ω).prob E)| ≤ δ := by
    rw [← expect_sub]
    calc
      _ ≤ ν.expect (fun ω => |(k ω).prob E - (l ω).prob E|) := ν.abs_expect_le _
      _ ≤ ν.expect (fun _ => δ) := ν.expect_mono fun ω => hk ω E
      _ = δ := ν.expect_const δ
  exact (abs_sub_le _ _ _).trans (add_le_add h₁ h₂)

theorem close_of_dominated_except (μ ν : Law Ω) (K : Finset Ω)
    (hin : ∀ ω ∈ K, ν.mass ω ≤ μ.mass ω)
    (hout : ∀ ω ∉ K, μ.mass ω ≤ ν.mass ω) :
    Close μ ν (∑ ω ∈ K, (μ.mass ω - ν.mass ω)) := by
  classical
  apply close_of_one_sided
  intro E
  simp only [prob, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ ω, if ω ∈ K then μ.mass ω - ν.mass ω else 0 := by
      apply Finset.sum_le_sum
      intro ω _
      by_cases hK : ω ∈ K <;> by_cases hE : ω ∈ E
      · simp [hE, hK]
      · simp only [hE, hK, ↓reduceIte, sub_zero]
        linarith [hin ω hK]
      · simp only [hE, hK, ↓reduceIte]
        linarith [hout ω hK]
      · simp [hE, hK]
    _ = _ := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun ω => ω ∈ K) = K := by ext ω; simp
      rw [he]

end Law

end SteinerLowerBound

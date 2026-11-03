module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Prices

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open scoped Classical

variable {n k b B : ℕ} {Q : Type}

noncomputable def residualCap (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (t : ℝ) : ℕ :=
  ⌊4 * ((retained I bits cfg).card : ℝ) / t⌋₊

/-- Taking a floor, rather than a ceiling, preserves the real residual bound
exactly: the left-hand side is already an integer cardinality. -/
theorem residualCap_bounds (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (t : ℝ) (ht : 0 < t)
    (hres : ∀ v, ((residualNeighbors I bits cfg v).card : ℝ) ≤ 4 * (retained I bits cfg).card / t) :
    (residualCap I bits cfg t : ℝ) ≤ 4 * (retained I bits cfg).card / t ∧
      ∀ v, (residualNeighbors I bits cfg v).card ≤ residualCap I bits cfg t := by
  have hn : (0 : ℝ) ≤ 4 * (retained I bits cfg).card / t := by positivity
  refine ⟨Nat.floor_le hn, ?_⟩
  intro v
  exact Nat.le_floor (hres v)

theorem calibrated_incidence_upper (n g gm epsilon xi b : ℝ)
    (hn : 0 ≤ n) (hg : 0 < g) (he : 0 < epsilon) (hxi : xi ≤ 1 / 2)
    (hcal : (1 - xi) * g ≤ gm) (hb : b ≤ 100 * n / (epsilon * gm) + 1) :
    b ≤ 200 * n / (epsilon * g) + 1 := by
  have hgm : g / 2 ≤ gm := by nlinarith [mul_nonneg (show 0 ≤ 1 / 2 - xi by linarith) hg.le]
  have hden : 0 < epsilon * (g / 2) := by positivity
  have hquot : 100 * n / (epsilon * gm) ≤ 200 * n / (epsilon * g) := by
    calc
      _ ≤ 100 * n / (epsilon * (g / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hden (mul_le_mul_of_nonneg_left hgm he.le)
      _ = _ := by field_simp; ring
  linarith

theorem calibrated_residual_product (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (t epsilon xi gm : ℝ)
    (ht : 0 < t) (he : 0 < epsilon) (he₁ : epsilon ≤ 1) (hxi : xi ≤ 1 / 2)
    (hg : 0 < (retained I bits cfg).card)
    (hcal : (1 - xi) * (retained I bits cfg).card ≤ gm)
    (hb : (b : ℝ) ≤ 100 * n / (epsilon * gm) + 1)
    (hB : 10 / epsilon ≤ (B : ℝ)) :
    (b : ℝ) * residualCap I bits cfg t ≤ 81 * B * n / t := by
  have hgR : (0 : ℝ) < (retained I bits cfg).card := by exact_mod_cast hg
  have hgn : ((retained I bits cfg).card : ℝ) ≤ n := by
    have hn : (retained I bits cfg).card ≤ n := by
      simpa only [Fintype.card_fin] using (Finset.card_le_univ (s := retained I bits cfg))
    exact_mod_cast hn
  have hb' := calibrated_incidence_upper n (retained I bits cfg).card gm epsilon xi b
    (Nat.cast_nonneg _) hgR he hxi hcal hb
  have hP : (residualCap I bits cfg t : ℝ) ≤ 4 * (retained I bits cfg).card / t :=
    Nat.floor_le (by positivity)
  exact AccessAccounts.residual_product n (retained I bits cfg).card t epsilon b B (residualCap I bits cfg t)
    (Nat.cast_nonneg _) hgR ht he he₁ hgn (Nat.cast_nonneg _) (Nat.cast_nonneg _) hb' hP hB

theorem calibrated_prices (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (t epsilon xi gm : ℝ)
    (ht : 0 < t) (he : 0 < epsilon) (he₁ : epsilon ≤ 1) (hxi : xi ≤ 1 / 2)
    (hg : 0 < (retained I bits cfg).card)
    (hcal : (1 - xi) * (retained I bits cfg).card ≤ gm)
    (hb : (b : ℝ) ≤ 100 * n / (epsilon * gm) + 1)
    (hB : 10 / epsilon ≤ (B : ℝ)) (hk : k ≤ n) (hsquare : b ^ 2 ≤ 50 * (n + 1))
    (hinc : (b : ℝ) ≤ 4 * n / t + 1)
    (hres : ∀ v, ((residualNeighbors I bits cfg v).card : ℝ) ≤ 4 * (retained I bits cfg).card / t) :
    workPrice (b := b) I bits cfg hT hnd C ≤
        1200000 * (n + 1) * (1 + n / t) * (B + 2 : ℝ) ^ 4 ∧
      positivePrice (b := b) I bits cfg hT hnd C ≤
        200 * (1 + n / t) * (B + 2 : ℝ) ^ 3 := by
  have hP := calibrated_residual_product (b := b) (B := B) I bits cfg t epsilon xi gm
    ht he he₁ hxi hg hcal hb hB
  have hcard := (residualCap_bounds I bits cfg t ht hres).2
  exact ⟨work_price_bound I bits cfg hT hnd C (residualCap I bits cfg t) hcard hk hsquare t ht hinc hP,
    positive_price_bound I bits cfg hT hnd C (residualCap I bits cfg t) hcard t ht hP⟩

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

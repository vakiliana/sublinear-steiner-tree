module

public import SteinerUpperBound.PortGraph.RuntimeAdapter

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {n k b B : ℕ} {Q : Type}

theorem heavy_indicator_sum (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) :
    (∑ i : Fin (b * B * k), if isHeavy I bits cfg ⟨C, i⟩ then (1 : ℝ) else 0) =
      (heavySlots I bits cfg b C).card := by
  classical
  change (∑ i : Fin (b * B * k),
    if LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) ((slotEquiv b B k).symm i)
      then (1 : ℝ) else 0) = _
  rw [(slotEquiv b B k).symm.sum_comp (fun s : LocalAccess.PortSlot b B k =>
    if LocalAccess.Heavy I.weight bits cfg (canonicalFrame I cfg b B C.val) s then (1 : ℝ) else 0)]
  simp only [heavySlots, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem work_W_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) :
    (workAccount (b := b) (B := B) I bits cfg hT hnd).W C =
      ((b * B * k : ℕ) : ℝ) * (2 * B + 76) +
        ((heavySlots I bits cfg b C).card : ℝ) * LocalAccess.partnerBudget n k b B := by
  classical
  change (∑ i : Fin (b * B * k), (workCharge I bits cfg ⟨C, i⟩ : ℝ)) = _
  simp only [workCharge, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he (i : Fin (b * B * k)) :
      ((if isHeavy I bits cfg ⟨C, i⟩ then LocalAccess.partnerBudget n k b B else 0 : ℕ) : ℝ) =
        (if isHeavy I bits cfg ⟨C, i⟩ then (1 : ℝ) else 0) * LocalAccess.partnerBudget n k b B := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul, heavy_indicator_sum]
  ring

theorem positive_W_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) :
    (positiveAccount (b := b) (B := B) I bits cfg hT hnd).W C =
      ((heavySlots I bits cfg b C).card : ℝ) * (B + 2) := by
  classical
  change (∑ i : Fin (b * B * k), (positiveCharge I bits cfg ⟨C, i⟩ : ℝ)) = _
  have he (i : Fin (b * B * k)) :
      (positiveCharge I bits cfg ⟨C, i⟩ : ℝ) =
        (if isHeavy I bits cfg ⟨C, i⟩ then (1 : ℝ) else 0) * (B + 2) := by
    unfold positiveCharge
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.sum_mul, heavy_indicator_sum]

noncomputable def workPrice (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) : ℝ :=
  (workAccount (b := b) (B := B) I bits cfg hT hnd).Cstar * (1 + (graph I bits cfg b B).degree C) +
    (workAccount (b := b) (B := B) I bits cfg hT hnd).W C

noncomputable def positivePrice (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) : ℝ :=
  (positiveAccount (b := b) (B := B) I bits cfg hT hnd).Cstar * (1 + (graph I bits cfg b B).degree C) +
    (positiveAccount (b := b) (B := B) I bits cfg hT hnd).W C

theorem work_price_geometric (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) (hk : k ≤ n)
    (hb : b ^ 2 ≤ 50 * (n + 1)) :
    workPrice (b := b) I bits cfg hT hnd C ≤
      2100 * (n + 1) * (B + 2 : ℝ) ^ 2 * (1 + 2 * b * B * P) +
        ((k : ℝ) * b * B) * (2 * B + 76) := by
  have hd : ((graph I bits cfg b B).degree C : ℝ) ≤ (b : ℝ) * B * P := by
    exact_mod_cast degree_le I bits cfg hT hnd C P hres
  have hh : ((heavySlots I bits cfg b C).card : ℝ) ≤ (b : ℝ) * B * P := by
    exact_mod_cast heavySlots_card_le I bits cfg b hT hnd C P hres
  have hc : (workCap n k b B : ℝ) ≤ 2100 * (n + 1) * (B + 2 : ℝ) ^ 2 := by
    exact_mod_cast workCap_le n k b B hk hb
  have hp : (LocalAccess.partnerBudget n k b B : ℝ) ≤ (workCap n k b B : ℝ) := by
    have hn : LocalAccess.partnerBudget n k b B ≤ workCap n k b B := by unfold workCap; omega
    exact_mod_cast hn
  have hc₀ : (0 : ℝ) ≤ workCap n k b B := Nat.cast_nonneg _
  have hh₀ : (0 : ℝ) ≤ (heavySlots I bits cfg b C).card := Nat.cast_nonneg _
  have hd₀ : (0 : ℝ) ≤ (graph I bits cfg b B).degree C := Nat.cast_nonneg _
  unfold workPrice
  rw [work_W_eq]
  change (workCap n k b B : ℝ) * (1 + (graph I bits cfg b B).degree C) + _ ≤ _
  have h₁ := mul_le_mul_of_nonneg_right hp hh₀
  have h₂ := mul_le_mul_of_nonneg_left (add_le_add hd hh) hc₀
  have h₃ := mul_le_mul_of_nonneg_right hc (show 0 ≤ (1 : ℝ) + 2 * b * B * P by positivity)
  push_cast
  nlinarith

theorem positive_price_geometric (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P) :
    positivePrice (b := b) I bits cfg hT hnd C ≤ (B + 2 : ℝ) * (1 + 2 * b * B * P) := by
  have hd : ((graph I bits cfg b B).degree C : ℝ) ≤ (b : ℝ) * B * P := by
    exact_mod_cast degree_le I bits cfg hT hnd C P hres
  have hh : ((heavySlots I bits cfg b C).card : ℝ) ≤ (b : ℝ) * B * P := by
    exact_mod_cast heavySlots_card_le I bits cfg b hT hnd C P hres
  unfold positivePrice
  rw [positive_W_eq]
  change ((B : ℝ) + 2) * (1 + (graph I bits cfg b B).degree C) + _ ≤ _
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hd hh) (show (0 : ℝ) ≤ B + 2 by positivity)]

theorem enlarged_access_work (n k t b B P : ℝ)
    (hn : 0 ≤ n) (hk : 0 ≤ k) (hkn : k ≤ n) (ht : 0 < t)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hinc : b ≤ 4 * n / t + 1) (hprod : b * P ≤ 81 * B * n / t) :
    2100 * (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P) +
        k * b * B * (2 * B + 76) ≤
      1200000 * (n + 1) * (1 + n / t) * (B + 2) ^ 4 := by
  have hold := AccessAccounts.access_work n k t b B P hn hk hkn ht hb hB hP hinc hprod
  have ha : 0 ≤ (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P) := by positivity
  have hl : 0 ≤ k * b * B := by positivity
  have h₁ : 2100 * (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P) ≤
      3 * (1000 * (n + 1) * (B + 2) ^ 2 * (1 + 2 * b * B * P)) := by nlinarith
  have h₂ : k * b * B * (2 * B + 76) ≤ 3 * (k * b * B * (2 * B + 64)) := by
    have h := mul_le_mul_of_nonneg_left (show 2 * B + 76 ≤ 3 * (2 * B + 64) by linarith) hl
    nlinarith
  nlinarith

theorem work_price_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t) :
    workPrice (b := b) I bits cfg hT hnd C ≤
      1200000 * (n + 1) * (1 + n / t) * (B + 2 : ℝ) ^ 4 :=
  (work_price_geometric I bits cfg hT hnd C P hres hk hb).trans
    (enlarged_access_work n k t b B P (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hk)
      ht (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hinc hprod)

theorem positive_price_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ)
    (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (t : ℝ) (ht : 0 < t) (hprod : (b : ℝ) * P ≤ 81 * B * n / t) :
    positivePrice (b := b) I bits cfg hT hnd C ≤
      200 * (1 + n / t) * (B + 2 : ℝ) ^ 3 :=
  (positive_price_geometric I bits cfg hT hnd C P hres).trans
    (AccessAccounts.access_disclosures n t b B P (Nat.cast_nonneg _) ht (Nat.cast_nonneg _) hprod)

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

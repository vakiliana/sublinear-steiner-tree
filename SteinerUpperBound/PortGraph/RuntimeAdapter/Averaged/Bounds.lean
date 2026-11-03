module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Transport

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

noncomputable def geometricBudget (kind : CounterKind) (n B : ℕ) (t : ℝ) : ℝ :=
  match kind with
  | .ordinary => 1200000 * (n + 1) * (1 + n / t) * (B + 2 : ℝ) ^ 4
  | .positive => 200 * (1 + n / t) * (B + 2 : ℝ) ^ 3

theorem geometricBudget_nonneg (kind : CounterKind) (n B : ℕ) (t : ℝ) (ht : 0 < t) :
    0 ≤ geometricBudget kind n B t := by
  cases kind <;> dsimp only [geometricBudget] <;> positivity

theorem costFactor_nonneg (n k b B : ℕ) : 0 ≤ costFactor n k b B := by
  unfold costFactor
  positivity

theorem rankError_nonneg (n k b B : ℕ) : 0 ≤ rankError n k b B := by
  unfold rankError
  positivity

theorem actual_price_bound (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t) :
    kind.price (b := b) I bits cfg hT hnd C ≤ geometricBudget kind n B t := by
  cases kind
  · exact work_price_bound I bits cfg hT hnd C P hres hk hb t ht hinc hprod
  · exact positive_price_bound I bits cfg hT hnd C P hres t ht hprod

theorem initiated_price_bound (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (kind.price (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card ≤
      geometricBudget kind n B t := by
  have hgR : (0 : ℝ) < (retained I bits cfg).card := by exact_mod_cast hg
  have hm : (Fintype.card (Vertex I bits cfg B) : ℝ) ≤ (retained I bits cfg).card := by
    exact_mod_cast vertices_card_le I bits cfg B
  exact initiation_bound _ _ _ hgR hm (geometricBudget_nonneg kind n B t ht)
    (fun C => actual_price_bound kind I bits cfg hT hnd C P hres hk hb t ht hinc hprod)

theorem closed_counter_tail (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) (threshold : ℝ) (hthreshold : 0 < threshold) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card ≤
      ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) * rankError n k b B +
        costFactor n k b B * geometricBudget kind n B t / threshold := by
  have hprice := initiated_price_bound kind I bits cfg hT hnd P hres hk hb t ht hinc hprod hg
  have htransport := initiated_counter_tail (b := b) kind I bits cfg hT hnd caches hc hg threshold hthreshold
  exact htransport.trans (add_le_add (le_refl _) (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprice (costFactor_nonneg n k b B)) hthreshold.le))

theorem closed_counter_tail_le (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) (threshold : ℝ) (hthreshold : 0 < threshold) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card ≤
      rankError n k b B + costFactor n k b B * geometricBudget kind n B t / threshold := by
  exact (closed_counter_tail kind I bits cfg hT hnd caches hc P hres hk hb t ht hinc hprod hg threshold hthreshold).trans
    (add_le_add (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (vertex_ratio I bits cfg B hg).2
        (rankError_nonneg n k b B)) (le_refl _))

theorem calibrated_counter_tail (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (t epsilon xi gm : ℝ) (ht : 0 < t) (he : 0 < epsilon) (he₁ : epsilon ≤ 1) (hxi : xi ≤ 1 / 2)
    (hg : 0 < (retained I bits cfg).card)
    (hcal : (1 - xi) * (retained I bits cfg).card ≤ gm)
    (hb : (b : ℝ) ≤ 100 * n / (epsilon * gm) + 1)
    (hB : 10 / epsilon ≤ (B : ℝ)) (hk : k ≤ n) (hsquare : b ^ 2 ≤ 50 * (n + 1))
    (hinc : (b : ℝ) ≤ 4 * n / t + 1)
    (hres : ∀ v, ((residualNeighbors I bits cfg v).card : ℝ) ≤ 4 * (retained I bits cfg).card / t)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card ≤
      ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) * rankError n k b B +
        costFactor n k b B * geometricBudget kind n B t / threshold := by
  exact closed_counter_tail kind I bits cfg hT hnd caches hc (residualCap I bits cfg t)
    (residualCap_bounds I bits cfg t ht hres).2 hk hsquare t ht hinc
    (calibrated_residual_product I bits cfg t epsilon xi gm ht he he₁ hxi hg hcal hb hB)
    hg threshold hthreshold

theorem counter_tail_empty (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (caches : Vertex I bits cfg B → Cache Q) (threshold : ℝ)
    (hm : Fintype.card (Vertex I bits cfg B) = 0) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card = 0 :=
  initiation_empty _ _ hm

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Calibration

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

noncomputable def uniformAverage (f : V → ℝ) : ℝ := (∑ v, f v) / Fintype.card V
noncomputable def initiationAverage (f : V → ℝ) (g : ℝ) : ℝ := (∑ v, f v) / g

theorem initiation_mono (f f' : V → ℝ) (g : ℝ) (hg : 0 ≤ g) (hf : ∀ v, f v ≤ f' v) :
    initiationAverage f g ≤ initiationAverage f' g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun v _ => hf v)) hg

theorem initiation_add (f f' : V → ℝ) (g : ℝ) :
    initiationAverage (fun v => f v + f' v) g = initiationAverage f g + initiationAverage f' g := by
  simp only [initiationAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_eq [Nonempty V] (f : V → ℝ) :
    uniformAverage f = (Law.uniform V).expect f := by
  simp only [uniformAverage, Law.expect, Law.uniform]
  rw [← Finset.mul_sum]
  ring

theorem root_normalization (f : V → ℝ) (g : ℝ) (hg : 0 < g) (hm : 0 < Fintype.card V) :
    initiationAverage f g = ((Fintype.card V : ℝ) / g) * uniformAverage f := by
  have hm' : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold initiationAverage uniformAverage
  field_simp

theorem initiation_empty (f : V → ℝ) (g : ℝ) (hm : Fintype.card V = 0) :
    initiationAverage f g = 0 := by
  let _ : IsEmpty V := Fintype.card_eq_zero_iff.mp hm
  simp [initiationAverage]

theorem normalized_budget_algebra (g m p W Cstar : ℝ) (hg : 0 < g) (hm : 0 < m) :
    (m / g) * (Cstar * (1 + p / m) + W / m) = (Cstar * (m + p) + W) / g := by
  field_simp

theorem sum_price {E : Type*} [Fintype E] {G : Matching.Graph V E}
    (S : Matching.Padded.Slots G) (A : Matching.Padded.Account S) :
    (∑ v, (A.Cstar * (1 + (G.degree v : ℝ)) + A.W v)) =
      A.Cstar * ((Fintype.card V : ℝ) + ∑ v, (G.degree v : ℝ)) + ∑ v, A.W v := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

theorem initiation_bound (f : V → ℝ) (g K : ℝ) (hg : 0 < g)
    (hm : (Fintype.card V : ℝ) ≤ g) (hK : 0 ≤ K) (hf : ∀ v, f v ≤ K) :
    initiationAverage f g ≤ K := by
  have hsum : (∑ v, f v) ≤ (Fintype.card V : ℝ) * K := by
    calc
      _ ≤ ∑ _v : V, K := Finset.sum_le_sum (fun v _ => hf v)
      _ = _ := by simp
  unfold initiationAverage
  apply (div_le_iff₀ hg).mpr
  simpa only [mul_comm] using hsum.trans (mul_le_mul_of_nonneg_right hm hK)

variable {n k b B : ℕ} {Q : Type}

theorem vertex_ratio (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ) (hg : 0 < (retained I bits cfg).card) :
    0 ≤ (Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card ∧
      (Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card ≤ 1 := by
  have hgR : (0 : ℝ) < (retained I bits cfg).card := by exact_mod_cast hg
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ hgR).mpr
  simpa only [one_mul] using (show (Fintype.card (Vertex I bits cfg B) : ℝ) ≤ (retained I bits cfg).card by
    exact_mod_cast vertices_card_le I bits cfg B)

noncomputable def callbackCounter (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (C : Vertex I bits cfg B) : ℝ :=
  (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) (caches C)).evaluate I.weight bits counter.value

noncomputable def runtimeCounter (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (C : Vertex I bits cfg B) : ℝ :=
  (Matching.Padded.Runtime.answer (config n b B k (publicSize n k b B))
    (primitives cfg (canonicalFrame I cfg b B C.val) (caches C)) (rootEmbedding I bits cfg B hT C)).evaluate
      I.weight bits counter.value

theorem callbackCounter_nonneg (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (C : Vertex I bits cfg B) : 0 ≤ callbackCounter (b := b) I bits cfg caches counter C :=
  Code.evaluate_nonneg _ _ _ counter.value_nonneg

theorem callback_normalization
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    [Nonempty (Vertex I bits cfg B)]
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (callbackCounter (b := b) I bits cfg caches counter) (retained I bits cfg).card =
      ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
        (Law.uniform (Vertex I bits cfg B)).expect (callbackCounter (b := b) I bits cfg caches counter) := by
  rw [root_normalization _ _ (by exact_mod_cast hg) Fintype.card_pos, uniformAverage_eq]

theorem callback_empty (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (hm : Fintype.card (Vertex I bits cfg B) = 0) :
    initiationAverage (callbackCounter (b := b) I bits cfg caches counter) (retained I bits cfg).card = 0 :=
  initiation_empty _ _ hm

theorem wrapper_initiation (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter) :
    initiationAverage (callbackCounter (b := b) I bits cfg caches counter) (retained I bits cfg).card =
      initiationAverage (runtimeCounter (b := b) I bits cfg hT caches counter) (retained I bits cfg).card +
        12 * counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) := by
  unfold initiationAverage callbackCounter
  simp_rw [oracle_counter (b := b) I bits cfg hT _ (publicSize n k b B)]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold runtimeCounter
  ring

theorem wrapper_overhead_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (caches : Vertex I bits cfg B → Cache Q) (counter : Matching.Padded.Causal.Counter)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (callbackCounter (b := b) I bits cfg caches counter) (retained I bits cfg).card ≤
      initiationAverage (runtimeCounter (b := b) I bits cfg hT caches counter) (retained I bits cfg).card +
        12 * counter.work := by
  rw [wrapper_initiation I bits cfg hT caches counter]
  have h := mul_le_mul_of_nonneg_left (vertex_ratio I bits cfg B hg).2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 12) counter.work_nonneg)
  linarith

theorem initiated_prices_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (workPrice (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card ≤
        1200000 * (n + 1) * (1 + n / t) * (B + 2 : ℝ) ^ 4 ∧
      initiationAverage (positivePrice (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card ≤
        200 * (1 + n / t) * (B + 2 : ℝ) ^ 3 := by
  have hgR : (0 : ℝ) < (retained I bits cfg).card := by exact_mod_cast hg
  have hm : (Fintype.card (Vertex I bits cfg B) : ℝ) ≤ (retained I bits cfg).card := by
    exact_mod_cast vertices_card_le I bits cfg B
  refine ⟨initiation_bound _ _ _ hgR hm (by positivity) ?_,
    initiation_bound _ _ _ hgR hm (by positivity) ?_⟩
  · intro C
    exact work_price_bound I bits cfg hT hnd C P hres hk hb t ht hinc hprod
  · intro C
    exact positive_price_bound I bits cfg hT hnd C P hres t ht hprod

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

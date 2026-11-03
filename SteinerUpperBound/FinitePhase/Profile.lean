module

public import SteinerUpperBound.FinitePhase.Mean
public import SteinerUpperBound.MSTProfile
public import SteinerUpperBound.Covers.Geometry.BandSoundnessRank

@[expose] public section

namespace SteinerUpperBound.FinitePhase

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

set_option maxHeartbeats 800000

variable {V : Type*} [Fintype V]

theorem thresholdOn_eq_below (I : Instance V) (T : Finset V) (a : ℝ) :
    thresholdOn I T a = TerminalMST.below I.weight T a := by
  ext x y
  simp only [thresholdOn_adj, TerminalMST.below_adj, Instance.weight_mk]

theorem components_card_eq_image (I : Instance V) (T : Finset V) (a : ℝ) :
    (componentsOn I T a).card = (T.image (thresholdOn I T a).connectedComponentMk).card := by
  let G := thresholdOn I T a
  let f : G.ConnectedComponent → Finset V :=
    fun c => T.filter (fun y => c = G.connectedComponentMk y)
  have hf (x : V) : f (G.connectedComponentMk x) = componentOn I T a x := by
    ext y
    rw [Finset.mem_filter, mem_componentOn]
    exact and_congr_right (fun _ =>
      ⟨SimpleGraph.ConnectedComponent.exact, SimpleGraph.ConnectedComponent.sound⟩)
  have him : (T.image G.connectedComponentMk).image f = componentsOn I T a := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    exact hf x
  have hinj : Set.InjOn f (T.image G.connectedComponentMk) := by
    intro c hc d _ hcd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    have hmem : x ∈ f (G.connectedComponentMk x) := Finset.mem_filter.mpr ⟨hx, rfl⟩
    rw [hcd] at hmem
    exact (Finset.mem_filter.mp hmem).2.symm
  have hcard := Finset.card_image_iff.mpr hinj
  rw [him] at hcard
  exact hcard

theorem components_add_rank (I : Instance V) (T : Finset V) (a : ℝ) (hT : T.Nonempty) :
    (componentsOn I T a).card + GraphRank.rank (thresholdOn I T a) = T.card := by
  let G := thresholdOn I T a
  have hle : G ≤ Network.completeOn T := by
    intro x y hxy
    obtain ⟨hne, hx, hy, _⟩ := (thresholdOn_adj I T a x y).mp hxy
    exact (Network.completeOn_adj T x y).mpr ⟨hne, hx, hy⟩
  have hsup : G ⊔ Network.completeOn T = Network.completeOn T := sup_eq_right.mpr hle
  have ht : 1 ≤ T.card := Finset.card_pos.mpr hT
  have hc : 1 ≤ (T.image G.connectedComponentMk).card :=
    Finset.card_pos.mpr (hT.image _)
  have hg := BandSoundness.gain_clique_eq G T
  rw [GraphRank.gain, hsup, GraphRank.rank_completeOn,
    Nat.cast_sub ht, Nat.cast_sub hc, Nat.cast_one] at hg
  have hn : (T.image G.connectedComponentMk).card + GraphRank.rank G = T.card := by
    exact_mod_cast (show ((T.image G.connectedComponentMk).card : ℝ) + GraphRank.rank G =
      (T.card : ℝ) by linarith)
  simpa only [components_card_eq_image] using hn

theorem components_eq_heavy (I : Instance V) (T : Finset V) (a : ℝ) (hT : T.Nonempty) :
    (componentsOn I T a).card =
      TerminalMST.heavy (SpanningForest.picked (TerminalMST.input I.weight T) ⊥) I.weight a + 1 := by
  have hc := components_add_rank I T a hT
  have hh := TerminalMST.heavy_profile I.weight T a
  rw [← thresholdOn_eq_below] at hh
  have ht : 1 ≤ T.card := Finset.card_pos.mpr hT
  omega

theorem heavy_map (l : List (Sym2 V)) (w : Sym2 V → ℝ) (a : ℝ) :
    TerminalMST.heavy l w a = ((l.map w).filter (fun x => decide (a ≤ x))).length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      by_cases h : a ≤ w e <;>
        simp [TerminalMST.heavy, WeightedSelection.count, h] at ih ⊢ <;> exact ih

theorem filter_threshold_decomposition (weights : List ℝ) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    (weights.filter (fun w => decide (lo ≤ w))).length =
      (weights.filter (fun w => decide (hi ≤ w))).length +
        (weights.filter (fun w => decide (lo ≤ w ∧ w < hi))).length := by
  induction weights with
  | nil => rfl
  | cons w l ih =>
      by_cases hl : lo ≤ w <;> by_cases hh : hi ≤ w <;> by_cases ht : w < hi <;>
        simp only [List.filter_cons, hl, hh, ht, decide_true, decide_false,
          Bool.false_eq_true, ite_true, ite_false, List.length_cons,
          and_false, and_true, false_and, true_and]
      all_goals first | omega | linarith

theorem weighted_filter (weights : List ℝ) (base : ℝ) (j : Fin count) (i : ℕ) :
    scale base j i * ((weights.filter (fun w => decide (Window base j i w))).length : ℝ) =
      (weights.map (fun w => if Window base j i w then scale base j i else 0)).sum := by
  induction weights with
  | nil => simp
  | cons w l ih =>
      by_cases h : Window base j i w <;>
        simp only [List.filter_cons, h, decide_true, decide_false, ite_true, ite_false,
          Bool.false_eq_true, List.length_cons, List.map_cons, List.sum_cons,
          Nat.cast_add, Nat.cast_one] <;> nlinarith

theorem profile_sum (base : ℝ) (height : Fin count → ℕ) (weights : List ℝ) (j : Fin count) :
    profile base height weights j =
      ∑ i : Fin (height j + 1),
        (weights.map (fun w => if Window base j i.val w then scale base j i.val else 0)).sum := by
  induction weights with
  | nil => simp [profile]
  | cons w l ih =>
      simp only [profile, List.map_cons, List.sum_cons, Finset.sum_add_distrib] at ih ⊢
      rw [← ih]
      rfl

noncomputable def treeWeights (I : Instance V) : List ℝ :=
  (SpanningForest.picked (TerminalMST.input I.weight I.terminals) ⊥).map I.weight

theorem treeWeights_nonneg (I : Instance V) : ∀ w ∈ treeWeights I, 0 ≤ w := by
  intro w hw
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hw
  exact I.weight_nonneg e

theorem treeWeights_sum (I : Instance V) : (treeWeights I).sum = I.mst :=
  (TerminalMST.value_eq_sum I.weight I.terminals I.weight_nonneg).symm

noncomputable def persistenceMass (I : Instance V) (base : ℝ) (height : Fin count → ℕ)
    (j : Fin count) : ℝ :=
  ∑ i : Fin (height j + 1), scale base j i.val *
    (phaseBad I I.terminals (contraction * scale base j i.val) (scale base j i.val)).card

theorem persistence_le_profile (I : Instance V) (hT : I.terminals.Nonempty)
    (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ) (j : Fin count) :
    persistenceMass I base height j ≤ profile base height (treeWeights I) j := by
  rw [profile_sum]
  apply Finset.sum_le_sum
  intro i _
  have ha := (scale_pos base hb j i.val).le
  have hsa : contraction * scale base j i.val ≤ scale base j i.val := by
    have h : contraction ≤ (1 : ℝ) := by norm_num [contraction, delta]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right h ha
  have hd := phaseBad_card_le_drop I I.terminals _ _ hsa
  rw [components_eq_heavy I _ _ hT, components_eq_heavy I _ _ hT,
    heavy_map, heavy_map] at hd
  have hf := filter_threshold_decomposition (treeWeights I)
    (contraction * scale base j i.val) (scale base j i.val) hsa
  have hc :
      (phaseBad I I.terminals (contraction * scale base j i.val) (scale base j i.val)).card ≤
        ((treeWeights I).filter (fun w => decide (Window base j i.val w))).length := by
    have hp : (fun w => decide (Window base j i.val w)) =
        (fun w => decide (contraction * scale base j i.val ≤ w ∧ w < scale base j i.val)) := by
      funext w
      by_cases h : Window base j i.val w
      · have h' : contraction * scale base j i.val ≤ w ∧ w < scale base j i.val := h
        simp only [h, h', true_and, decide_true]
      · have h' : ¬(contraction * scale base j i.val ≤ w ∧ w < scale base j i.val) := h
        simp only [h, h', decide_false]
    rw [hp]
    dsimp only [treeWeights] at hf ⊢
    omega
  rw [← weighted_filter]
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) ha

theorem persistence_failure (I : Instance V) (hT : I.terminals.Nonempty)
    (hM : 0 < I.mst) (base : ℝ) (hb : 0 < base) (height : Fin count → ℕ) :
    law.prob {j | I.mst / 200 < persistenceMass I base height j} ≤ 1 / 1000 := by
  have hs : {j | I.mst / 200 < persistenceMass I base height j} ⊆
      {j | (treeWeights I).sum / 200 < 2 * profile base height (treeWeights I) j} := by
    intro j hj
    change I.mst / 200 < persistenceMass I base height j at hj
    change (treeWeights I).sum / 200 < 2 * profile base height (treeWeights I) j
    have hd := persistence_le_profile I hT base hb height j
    have hn := profile_nonneg base hb height (treeWeights I) j
    rw [treeWeights_sum]
    linarith
  exact (law.prob_mono hs).trans
    (profile_tail base hb height (treeWeights I) (treeWeights_nonneg I)
      (by simpa only [treeWeights_sum] using hM))

end SteinerUpperBound.FinitePhase

module

public import SteinerUpperBound.MSTApproximation.Grid
public import SteinerUpperBound.MSTApproximation.Components

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry
open scoped Classical BigOperators

noncomputable def rounded (g : Grid) (c t : ℝ) : ℝ :=
  g.first + ∑ i ∈ Finset.range g.intervals, g.width i * TerminalMST.layer t (c * g.scale i)

theorem rounded_lower (g : Grid) (t : ℝ) (hlo : g.first ≤ t) (hhi : t ≤ g.scale g.intervals) :
    t ≤ rounded g 1 t := by
  have hp (i : ℕ) :
      min (g.scale (i + 1)) t - min (g.scale i) t ≤
        g.width i * TerminalMST.layer t (g.scale i) := by
    by_cases h : g.scale i ≤ t
    · rw [TerminalMST.layer, if_pos h, mul_one, min_eq_left h]
      exact sub_le_sub_right (min_le_left _ _) _
    · have h' : t ≤ g.scale i := le_of_not_ge h
      rw [TerminalMST.layer, if_neg h, mul_zero, min_eq_right h',
        min_eq_right (h'.trans (g.scale_le_succ i)), sub_self]
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.range g.intervals) => hp i)
  rw [Finset.sum_range_sub (fun i => min (g.scale i) t) g.intervals] at hs
  rw [Grid.scale_zero, min_eq_left hlo, min_eq_right hhi] at hs
  unfold rounded
  simp only [one_mul]
  linarith

theorem rounded_upper (g : Grid) (c t : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hlo : g.first ≤ t) :
    rounded g c t ≤ g.q / c * t := by
  let bound := g.q / c * t
  have ht : 0 ≤ t := g.first_pos.le.trans hlo
  have hfactor : 1 ≤ g.q / c := (le_div_iff₀ hc).mpr (by linarith [g.ratio_gt_one])
  have hbase : g.scale 0 ≤ bound := by
    rw [Grid.scale_zero]
    exact hlo.trans (by dsimp only [bound]; nlinarith)
  have hp (i : ℕ) :
      g.width i * TerminalMST.layer t (c * g.scale i) ≤
        min (g.scale (i + 1)) bound - min (g.scale i) bound := by
    by_cases h : c * g.scale i ≤ t
    · have hi : g.scale i ≤ t / c := (le_div_iff₀ hc).mpr (by nlinarith)
      have hm := mul_le_mul_of_nonneg_left hi g.ratio_pos.le
      have hnext : g.scale (i + 1) ≤ bound := by
        rw [g.scale_succ]
        dsimp only [bound]
        convert hm using 1 <;> ring
      have hcur := (g.scale_le_succ i).trans hnext
      rw [TerminalMST.layer, if_pos h, mul_one, min_eq_left hnext, min_eq_left hcur]
      rfl
    · rw [TerminalMST.layer, if_neg h, mul_zero]
      exact sub_nonneg.mpr (min_le_min (g.scale_le_succ i) le_rfl)
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.range g.intervals) => hp i)
  rw [Finset.sum_range_sub (fun i => min (g.scale i) bound) g.intervals,
    min_eq_left hbase, Grid.scale_zero] at hs
  have hlast := min_le_right (g.scale g.intervals) bound
  unfold rounded
  dsimp only [bound] at *
  linarith

theorem mapped_sum_mono {A : Type*} (l : List A) (f h : A → ℝ)
    (hle : ∀ x ∈ l, f x ≤ h x) : (l.map f).sum ≤ (l.map h).sum := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih =>
    exact add_le_add (hle x (by simp)) (ih (fun y hy => hle y (by simp [hy])))

theorem sum_rounded {V : Type*} (g : Grid) (l : List (Sym2 V)) (w : Sym2 V → ℝ) (c : ℝ) :
    (l.map (fun e => rounded g c (w e))).sum =
      (l.length : ℝ) * g.first +
        ∑ i ∈ Finset.range g.intervals, g.width i * (TerminalMST.heavy l w (c * g.scale i) : ℝ) := by
  induction l with
  | nil => simp [TerminalMST.heavy, WeightedSelection.count]
  | cons e l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Nat.cast_add, Nat.cast_one]
    simp_rw [TerminalMST.heavy_cons_real, mul_add]
    rw [Finset.sum_add_distrib]
    unfold rounded
    ring

variable {V : Type*} [Fintype V]

noncomputable def mstEdges (I : Instance V) : List (Sym2 V) :=
  SpanningForest.picked (TerminalMST.input I.weight I.terminals) ⊥

theorem mstEdges_length (I : Instance V) : (mstEdges I).length = I.terminals.card - 1 := by
  have h := SpanningForest.rank_run (TerminalMST.input I.weight I.terminals) ⊥
  rw [GraphRank.rank_bot, zero_add] at h
  exact h.symm.trans (TerminalMST.graph_rank I.weight I.terminals)

theorem mstEdges_mem (I : Instance V) {e : Sym2 V} (he : e ∈ mstEdges I) :
    e ∈ (Network.completeOn I.terminals).edgeSet :=
  (TerminalMST.input_mem I.weight I.terminals e).mp
    ((SpanningForest.picked_sublist _ _).subset he)

theorem mstEdges_sum (I : Instance V) : ((mstEdges I).map I.weight).sum = I.mst :=
  (TerminalMST.value_eq_sum I.weight I.terminals I.weight_nonneg).symm

noncomputable def exactSum (I : Instance V) (g : Grid) (c : ℝ) : ℝ :=
  ((I.terminals.card - 1 : ℕ) : ℝ) * g.first +
    ∑ i ∈ Finset.range g.intervals, g.width i * TerminalMST.curve I.weight I.terminals (c * g.scale i)

theorem exactSum_eq_rounded (I : Instance V) (g : Grid) (c : ℝ) :
    exactSum I g c = ((mstEdges I).map (fun e => rounded g c (I.weight e))).sum := by
  rw [sum_rounded, mstEdges_length]
  unfold exactSum
  simp_rw [TerminalMST.curve_heavy]
  rfl

theorem exactSum_bounds (I : Instance V) (g : Grid) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals) :
    I.mst ≤ exactSum I g 1 ∧ exactSum I g c ≤ g.q / c * I.mst := by
  have hweights (e : Sym2 V) (he : e ∈ mstEdges I) :
      g.first ≤ I.weight e ∧ I.weight e ≤ g.scale g.intervals := by
    have hm := mstEdges_mem I he
    rcases e with ⟨x, y⟩
    have hxy := (Network.completeOn_adj I.terminals x y).mp hm
    exact ⟨hfirst x hxy.2.1 y hxy.2.2 hxy.1, hlast x hxy.2.1 y hxy.2.2⟩
  constructor
  · rw [exactSum_eq_rounded, ← mstEdges_sum I]
    exact mapped_sum_mono _ _ _ (fun e he => rounded_lower g (I.weight e) (hweights e he).1 (hweights e he).2)
  · rw [exactSum_eq_rounded, ← mstEdges_sum I, ← List.sum_map_mul_left]
    exact mapped_sum_mono _ _ _ (fun e he => rounded_upper g c (I.weight e) hc hc1 (hweights e he).1)

noncomputable def coverSum (I : Instance V) (g : Grid) (N : ℕ → Finset V) : ℝ :=
  ((I.terminals.card - 1 : ℕ) : ℝ) * g.first +
    ∑ i ∈ Finset.range g.intervals,
      g.width i * ((componentCount I (N i) (g.scale i) : ℝ) - 1)

theorem coverSum_bounds (I : Instance V) (g : Grid) (N : ℕ → Finset V) (delta : ℝ)
    (hT : I.terminals.Nonempty) (hd : 0 ≤ delta) (hdhalf : delta < 1 / 2)
    (hN : ∀ i < g.intervals, N i ⊆ I.terminals)
    (hcover : ∀ i < g.intervals, CoverOn I I.terminals (N i) (delta * g.scale i))
    (hfirst : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → g.first ≤ I.distance x y)
    (hlast : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, I.distance x y ≤ g.scale g.intervals) :
    I.mst ≤ coverSum I g N ∧ coverSum I g N ≤ g.q / (1 - 2 * delta) * I.mst := by
  have hbounds := exactSum_bounds I g (1 - 2 * delta) (by linarith) (by linarith) hfirst hlast
  have hlow : exactSum I g 1 ≤ coverSum I g N := by
    unfold exactSum coverSum
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i hi
    have hil : i < g.intervals := Finset.mem_range.mp hi
    have hs := (cover_componentCount_sandwich I I.terminals (N i) delta (g.scale i)
      hd (by linarith) (g.scale_pos i) (hcover i hil) (hN i hil)).1
    rw [one_mul, curve_eq_componentCount I _ _ hT]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (show (componentCount I I.terminals (g.scale i) : ℝ) ≤
        componentCount I (N i) (g.scale i) by exact_mod_cast hs) 1) (g.width_nonneg i)
  have hhigh : coverSum I g N ≤ exactSum I g (1 - 2 * delta) := by
    unfold exactSum coverSum
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i hi
    have hil : i < g.intervals := Finset.mem_range.mp hi
    have hs := (cover_componentCount_sandwich I I.terminals (N i) delta (g.scale i)
      hd (by linarith) (g.scale_pos i) (hcover i hil) (hN i hil)).2
    rw [curve_eq_componentCount I _ _ hT]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (show (componentCount I (N i) (g.scale i) : ℝ) ≤
        componentCount I I.terminals ((1 - 2 * delta) * g.scale i) by exact_mod_cast hs) 1)
      (g.width_nonneg i)
  exact ⟨hbounds.1.trans hlow, hhigh.trans hbounds.2⟩

noncomputable abbrev fineRatio (nu : ℝ) : ℝ := 1 + nu / 100
noncomputable abbrev fineDelta (nu : ℝ) : ℝ := nu / 10000

theorem fine_factor (nu : ℝ) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    fineRatio nu / (1 - 2 * fineDelta nu) ≤ 1 + nu / 10 := by
  unfold fineRatio fineDelta
  apply (div_le_iff₀ (by linarith : 0 < 1 - 2 * (nu / 10000))).mpr
  nlinarith

end SteinerUpperBound.MSTApproximation

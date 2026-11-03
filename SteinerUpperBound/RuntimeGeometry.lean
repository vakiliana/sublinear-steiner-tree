module

public import SteinerUpperBound.RuntimeGrids
public import SteinerUpperBound.LabelledCovers
public import SteinerUpperBound.EstimatorParameters.Normalization
public import SteinerUpperBound.EstimatorAnalysis.Statistics
public import SteinerUpperBound.FinitePhase

@[expose] public section

noncomputable section

namespace SteinerUpperBound.RuntimeGeometry

open SteinerLowerBound MSTApproximation EstimatorParameters
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

theorem minimum_floored (I : Instance V) (lam : ℝ) (hk : 2 ≤ I.terminals.card) :
    lam ≤ Structural.minimumTerminalDistance (TreeGeometry.Flooring.floored I lam) := by
  classical
  let F := TreeGeometry.Flooring.floored I lam
  have hdist : (Structural.terminalDistances F).Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (show 1 < I.terminals.card by omega)
    exact ⟨F.distance x y, Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩, rfl⟩⟩
  unfold Structural.minimumTerminalDistance
  rw [dif_pos hdist]
  apply Finset.le_min'
  intro d hd
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
  have hn : x ≠ y := (Finset.mem_filter.mp hxy).2
  change lam ≤ TreeGeometry.Flooring.distance I lam x y
  rw [TreeGeometry.Flooring.distance_of_ne I lam hn]
  exact le_max_right _ _

theorem coarse_covers (I : Instance V) (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count)
    (hmin : floorScale k R ≤ Structural.minimumTerminalDistance I)
    (hdiam : TreeGeometry.terminalDiameter I ≤ 2 * R) :
    ((coarseGrid k (by omega) R hR phase).toStructural rfl).Covers I := by
  obtain ⟨hfirst, hlast, _⟩ := coarseGrid_endpoints k hk R hR phase
  constructor
  · change (coarseGrid k (by omega) R hR phase).scale 0 <
      Structural.minimumTerminalDistance I / 2
    rw [Grid.scale_zero]
    have he : zeta * R / k = floorScale k R := rfl
    rw [he] at hfirst
    linarith
  · change 2 * TreeGeometry.terminalDiameter I <
      (coarseGrid k (by omega) R hR phase).scale
        (coarseGrid k (by omega) R hR phase).intervals
    linarith

theorem fine_first (I : Instance V) (k : ℕ) (hk : 2 ≤ k) (R : ℝ) (hR : 0 < R)
    (hmin : ∀ x ∈ I.terminals, ∀ y ∈ I.terminals, x ≠ y → floorScale k R ≤ I.distance x y)
    {x y : V} (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) (hne : x ≠ y) :
    (fineGrid k (by omega) R hR).first ≤ I.distance x y := by
  have hf := (fineGrid_endpoints k hk R hR).1
  have hp := floorScale_pos k (by omega) R hR
  have he : zeta * R / k = floorScale k R := rfl
  rw [he] at hf
  linarith [hmin x hx y hy hne]

theorem fine_last (I : Instance V) (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (hk2 : 2 ≤ k) (hdiam : TreeGeometry.terminalDiameter I ≤ 2 * R)
    {x y : V} (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y ≤ (fineGrid k hk R hR).scale (fineGrid k hk R hR).intervals := by
  have hl := (fineGrid_endpoints k hk2 R hR).2.1
  have hd := Structural.terminal_distance_le_diameter I hx hy
  linarith

theorem full_sum_scales (g : Grid) (hq : g.q = Structural.omega) (R : ℝ) (hR : 0 ≤ R)
    (hcap : g.scale g.intervals ≤ 4 * g.q * R) :
    (∑ i : Fin (g.intervals + 1), g.scale i.val) ≤ 5 * g.q / (g.q - 1) * R := by
  let next : Grid := {g with intervals := g.intervals + 1}
  have he : (∑ i : Fin (g.intervals + 1), g.scale i.val) =
      (g.scale (g.intervals + 1) - g.first) / (g.q - 1) := by
    calc
      _ = ∑ i ∈ Finset.range (g.intervals + 1), g.scale i :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := next.sum_scales
  rw [he]
  apply (div_le_iff₀ (sub_pos.mpr g.ratio_gt_one)).mpr
  have hn : g.scale (g.intervals + 1) ≤ 5 * g.q * R := by
    rw [g.scale_succ]
    have h := mul_le_mul_of_nonneg_left hcap g.ratio_pos.le
    rw [hq] at h ⊢
    norm_num [Structural.omega] at h ⊢
    nlinarith
  have hp := g.first_pos
  have hd : (5 * g.q / (g.q - 1) * R) * (g.q - 1) = 5 * g.q * R := by
    field_simp [ne_of_gt (sub_pos.mpr g.ratio_gt_one)]
  rw [hd]
  linarith

theorem full_mass (I : Instance V) (g : Grid)
    (N : Fin (g.intervals + 1) → Finset V) (n : ℕ) (R : ℝ)
    (hq : g.q = Structural.omega) (hR : 0 ≤ R) (hRL : R ≤ I.mst)
    (hn : g.intervals + 1 ≤ heightBudget n) (hcap : g.scale g.intervals ≤ 4 * g.q * R)
    (hsize : ∀ i, ((N i).card : ℝ) ≤
      Hc n + 6 * coverTrials n * hopBudget n * I.mst / (deltaCoarse * g.scale i.val)) :
    (∑ i, g.scale i.val * ((N i).card : ℝ)) ≤ (A n : ℝ) * I.mst := by
  have hd : 0 < deltaCoarse := metric_scale_constants.1
  have hpoint (i : Fin (g.intervals + 1)) :
      g.scale i.val * ((N i).card : ℝ) ≤
        Hc n * g.scale i.val + 6 * coverTrials n * hopBudget n * I.mst / deltaCoarse := by
    have h := mul_le_mul_of_nonneg_left (hsize i) (g.scale_pos i.val).le
    have he : g.scale i.val *
        (Hc n + 6 * coverTrials n * hopBudget n * I.mst / (deltaCoarse * g.scale i.val)) =
        Hc n * g.scale i.val + 6 * coverTrials n * hopBudget n * I.mst / deltaCoarse := by
      field_simp [hd.ne', (g.scale_pos i.val).ne']
      <;> ring
    exact h.trans_eq he
  have hs := Finset.sum_le_sum (fun i (_hi : i ∈ Finset.univ) => hpoint i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hm := (full_sum_scales g hq R hR hcap).trans
    (mul_le_mul_of_nonneg_left hRL
      (show 0 ≤ 5 * g.q / (g.q - 1) by positivity [g.ratio_pos, g.ratio_gt_one]))
  have hh := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ Hc n by positivity)
  have hnR : ((g.intervals + 1 : ℕ) : ℝ) ≤ heightBudget n := by exact_mod_cast hn
  have hb := mul_le_mul_of_nonneg_right hnR
    (show 0 ≤ 6 * coverTrials n * hopBudget n * I.mst / deltaCoarse by positivity [I.mst_nonneg])
  have hallow := coarse_allowance_eq n g hq
  have ha : massAllowance g deltaCoarse (Hc n) (coverTrials n) (hopBudget n) (heightBudget n) ≤
      (A n : ℝ) := by linarith
  have hlast := mul_le_mul_of_nonneg_right ha I.mst_nonneg
  calc
    _ ≤ Hc n * (∑ i : Fin (g.intervals + 1), g.scale i.val) +
        ((g.intervals + 1 : ℕ) : ℝ) *
          (6 * coverTrials n * hopBudget n * I.mst / deltaCoarse) := hs
    _ ≤ Hc n * (5 * g.q / (g.q - 1) * I.mst) + (heightBudget n : ℝ) *
        (6 * coverTrials n * hopBudget n * I.mst / deltaCoarse) := add_le_add hh hb
    _ = massAllowance g deltaCoarse (Hc n) (coverTrials n) (hopBudget n) (heightBudget n) *
        I.mst := by unfold massAllowance; ring
    _ ≤ _ := hlast

theorem phase_mass_eq (I : Instance V) (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (phase : Fin FinitePhase.count) :
    Covers.Geometry.BandCompleteness.weightedPhaseBad I
        ((coarseGrid k hk R hR phase).toStructural rfl)
        (EstimatorAnalysis.radii ((coarseGrid k hk R hR phase).toStructural rfl)) =
      FinitePhase.persistenceMass I (floorScale k R / 4)
        (fun j => (coarseGrid k hk R hR j).intervals) phase := by
  unfold Covers.Geometry.BandCompleteness.weightedPhaseBad FinitePhase.persistenceMass
  apply Finset.sum_congr rfl
  intro i _
  change (coarseGrid k hk R hR phase).scale i.val *
      (Covers.Geometry.phaseBad I I.terminals
        ((coarseGrid k hk R hR phase).scale i.val -
          2 * (deltaCoarse * (coarseGrid k hk R hR phase).scale i.val))
        ((coarseGrid k hk R hR phase).scale i.val)).card = _
  rw [coarseGrid_phase_scale]
  have hd : deltaCoarse = FinitePhase.delta := by
    norm_num [deltaCoarse, deltaCoarseQ, FinitePhase.delta]
  have he (a : ℝ) : a - 2 * (deltaCoarse * a) = FinitePhase.contraction * a := by
    rw [hd]
    unfold FinitePhase.contraction
    ring
  rw [he]
  rfl

theorem phase_failure (I : Instance V) (k : ℕ) (hk : 0 < k) (R : ℝ) (hR : 0 < R)
    (hT : I.terminals.Nonempty) (hRL : R ≤ I.mst) :
    FinitePhase.law.prob {j |
      ¬ Covers.Geometry.BandCompleteness.weightedPhaseBad I
        ((coarseGrid k hk R hR j).toStructural rfl)
        (EstimatorAnalysis.radii ((coarseGrid k hk R hR j).toStructural rfl)) ≤ I.mst / 200} ≤
      1 / 1000 := by
  simp_rw [phase_mass_eq, not_le]
  exact FinitePhase.persistence_failure I hT (hR.trans_le hRL) (floorScale k R / 4)
    (by positivity [floorScale_pos k hk R hR])
    (fun j => (coarseGrid k hk R hR j).intervals)

theorem observed_geometry (I : Instance V) (root : V) (l : List V) (hn : l.Nodup)
    (hT : l.toFinset = I.terminals) (hroot : root ∈ I.terminals) (hk : 2 ≤ I.terminals.card) :
    let R := rowValue I.weight root l 0
    let lam := floorScale l.length R
    let F := TreeGeometry.Flooring.floored I lam
    0 < R ∧ 0 < lam ∧ lam ≤ Structural.minimumTerminalDistance F ∧ R ≤ F.mst ∧
      TreeGeometry.terminalDiameter F ≤ 2 * R ∧
      ∀ x y, x ≠ y → lam ≤ F.distance x y := by
  let R := rowValue I.weight root l 0
  let lam := floorScale l.length R
  let F := TreeGeometry.Flooring.floored I lam
  have hcard : l.length = I.terminals.card := by
    rw [← hT]
    exact (List.toFinset_card_of_nodup hn).symm
  have hlen : 0 < l.length := by omega
  have hr : 0 < R := (observed_radius_geometry I root l hT hroot hk).1
  have hl : 0 < lam := floorScale_pos l.length hlen R hr
  have hlR : lam ≤ R := floorScale_le l.length hlen R hr.le
  have ho : R ≤ I.optimum := by
    change rowValue I.weight root l 0 ≤ I.optimum
    rw [rowValue_eq_radius I root l hT]
    exact TreeGeometry.terminalRadius_le_optimum I root hroot
  have hm : R ≤ F.mst :=
    ho.trans ((TreeGeometry.Flooring.optimum_mono I lam).trans F.optimum_le_mst)
  have hd : TreeGeometry.terminalDiameter F ≤ 2 * R := by
    have hrad : lam ≤ TreeGeometry.terminalRadius I root := by
      rw [← rowValue_eq_radius I root l hT]
      exact hlR
    simpa only [R, rowValue_eq_radius I root l hT] using floored_diameter_le I root lam hrad
  refine ⟨hr, hl, minimum_floored I lam hk, hm, hd, ?_⟩
  intro x y hxy
  change lam ≤ TreeGeometry.Flooring.distance I lam x y
  rw [TreeGeometry.Flooring.distance_of_ne I lam hxy]
  exact le_max_right _ _

end SteinerUpperBound.RuntimeGeometry

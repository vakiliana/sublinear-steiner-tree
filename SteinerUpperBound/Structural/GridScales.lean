module

public import SteinerUpperBound.Structural.EventAvailability
public import SteinerUpperBound.Structural.Regions
public import SteinerUpperBound.Structural.StarBounds

@[expose] public section

namespace SteinerUpperBound.Structural

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

theorem minimumTerminalDistance_nonneg (I : Instance V) : 0 ≤ minimumTerminalDistance I := by
  classical
  unfold minimumTerminalDistance
  split_ifs with h
  · obtain ⟨⟨x, y⟩, _, he⟩ := Finset.mem_image.mp (Finset.min'_mem (terminalDistances I) h)
    rw [← he]
    exact I.distance_nonneg x y
  · exact le_rfl

theorem minimumTerminalDistance_le (I : Instance V) {x y : V}
    (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) (hne : x ≠ y) :
    minimumTerminalDistance I ≤ I.distance x y := by
  classical
  have hm : I.distance x y ∈ terminalDistances I := Finset.mem_image.mpr
    ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hne⟩, rfl⟩
  have h : (terminalDistances I).Nonempty := ⟨_, hm⟩
  unfold minimumTerminalDistance
  rw [dif_pos h]
  exact Finset.min'_le _ _ hm

theorem terminal_distance_le_diameter (I : Instance V) {x y : V}
    (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) :
    I.distance x y ≤ TreeGeometry.terminalDiameter I := by
  classical
  unfold TreeGeometry.terminalDiameter
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)

theorem Grid.bracket (g : Grid) (t : ℝ) (hlo : g.scale 0 ≤ t)
    (hhi : t < g.scale (Fin.last g.intervals)) :
    ∃ i j : Fin (g.intervals + 1), g.scale i ≤ t ∧ t < omega * g.scale i ∧
      t < g.scale j ∧ g.scale j ≤ omega * t := by
  classical
  let U := Finset.univ.filter (fun j => t < g.scale j)
  have hU : U.Nonempty := ⟨Fin.last g.intervals,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhi⟩⟩
  let j := U.min' hU
  have hj : t < g.scale j := (Finset.mem_filter.mp (Finset.min'_mem U hU)).2
  have hj0 : j ≠ 0 := by
    intro h
    rw [h] at hj
    linarith
  let i := (j.pred hj0).castSucc
  have hij : i < j := by
    have h := Fin.castSucc_lt_succ (i := j.pred hj0)
    simpa only [Fin.succ_pred] using h
  have hi : g.scale i ≤ t := by
    by_contra h
    have hmem : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge h⟩
    have hle : j ≤ i := Finset.min'_le U i hmem
    exact (not_lt_of_ge hle) hij
  have hratio : g.scale j = omega * g.scale i := by
    simpa only [Fin.succ_pred] using g.ratio (j.pred hj0)
  refine ⟨i, j, hi, ?_, hj, ?_⟩
  · simpa only [hratio] using hj
  · rw [hratio]
    exact mul_le_mul_of_nonneg_left hi (by norm_num [omega])

theorem Grid.bracket_of_covers (g : Grid) (I : Instance V) (hc : g.Covers I) (t : ℝ)
    (htlo : minimumTerminalDistance I / 2 < t)
    (hthi : t < 2 * TreeGeometry.terminalDiameter I) :
    ∃ i j : Fin (g.intervals + 1), g.scale i ≤ t ∧ t < omega * g.scale i ∧
      t < g.scale j ∧ g.scale j ≤ omega * t :=
  g.bracket t (hc.1.trans htlo).le (hthi.trans hc.2)

namespace Rooted

theorem path_region_depth_le {W : Type*} [Fintype W] (G : SimpleGraph W) (r : W)
    (ht : G.IsTree) {u z : W} (p : G.Walk u z) (hp : p.IsPath) {q : W}
    (hq : G.Adj u q) (hdq : G.dist r q + 1 = G.dist r u)
    (hnot : s(u, q) ∉ p.edges) : G.dist r u ≤ G.dist r z := by
  induction p generalizing q with
  | nil => exact le_rfl
  | @cons u w z huw p ih =>
    have hc := first_step_child G r ht huw p hq hdq hnot
    have hd := (mem_children G r u w).mp hc |>.2
    have hnot' : s(w, u) ∉ p.edges := by
      rw [Sym2.eq_swap]
      exact (SimpleGraph.Walk.isTrail_cons huw p).mp hp.isTrail |>.2
    have hle := ih hp.of_cons huw.symm hd.symm hnot'
    omega

end Rooted

namespace Tree

variable {I : Instance V} {S : TreeGeometry.TreeSolution I}

theorem ShortStar.scale_range (A : ShortStar S) (hred : Reduced S) :
    minimumTerminalDistance I / 2 < p * A.ell ∧
      p * A.ell < 2 * TreeGeometry.terminalDiameter I := by
  have hne := A.ports_ne (show (0 : Fin 3) ≠ 1 by decide)
  have hmin := minimumTerminalDistance_le I (A.port_terminal 0) (A.port_terminal 1) hne
  have hdist := A.port_distance_le 0 1
  have hlen₀ := A.length_bound hred 0
  have hlen₁ := A.length_bound hred 1
  have hp := A.ell_pos
  constructor
  · norm_num [p, b0, chi, e0, theta0] at hdist hlen₀ hlen₁ ⊢
    nlinarith
  · have hb := (A.limb 0).crossing_barrier hred (A.port_terminal 0) (A.port_terminal 1)
      (A.limb 0).primary_mem_region (A.port_outside (show (0 : Fin 3) ≠ 1 by decide))
    have hle := mul_le_mul_of_nonneg_left (A.shortest 0) (show 0 ≤ p by norm_num [p, chi, e0])
    have hdiam := terminal_distance_le_diameter I (A.port_terminal 0) (A.port_terminal 1)
    have hpos : 0 < p * A.ell := mul_pos (by norm_num [p, chi, e0]) hp
    change p * (A.limb 0).length < I.distance (A.port 0) (A.port 1) at hb
    nlinarith

theorem RootedFringe.root_outside {parent v : ↥S.vertices} (F : RootedFringe S parent v) :
    (F.root : V) ∉ F.fan.region := by
  intro h
  have hreach := (mem_region S parent v F.root).mp h
  obtain ⟨p, hp⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach
  have hnot : s(v, parent) ∉ (p.toPath : S.graph.Walk v F.root).edges := by
    have he : s(v, parent) = s(parent, v) := Sym2.eq_swap
    rw [he]
    exact fun h => hp (p.edges_toPath_subset_edges h)
  have hd := Rooted.path_region_depth_le S.graph F.root S.isTree
    (p.toPath : S.graph.Walk v F.root) p.toPath.isPath
    F.fan.parent_edge.symm F.parent_lower hnot
  have hz : S.graph.dist F.root F.root = 0 := SimpleGraph.dist_self
  have hh := F.parent_lower
  omega

theorem RootedFringe.regular_scale_range {parent v : ↥S.vertices} (F : RootedFringe S parent v)
    (hred : Reduced S) (hparent : delta0 * F.fan.pair.totalLength ≤ I.distance parent v) :
    minimumTerminalDistance I / 2 < F.fan.pair.totalLength / (chi - 1) ∧
      F.fan.pair.totalLength / (chi - 1) < 2 * TreeGeometry.terminalDiameter I := by
  have hpos : 0 < F.fan.pair.totalLength := add_pos F.fan.left.length_pos F.fan.right.length_pos
  have hne : (F.fan.left.primary : V) ≠ (F.fan.right.primary : V) :=
    fun h => F.fan.ports_ne (Subtype.ext h)
  have hmin := minimumTerminalDistance_le I F.fan.left.primary_terminal F.fan.right.primary_terminal hne
  have hdist := F.fan.pair.port_distance_le
  have hmin0 := minimumTerminalDistance_nonneg I
  constructor
  · have hlt : F.fan.pair.totalLength < F.fan.pair.totalLength / (chi - 1) := by
      norm_num [chi, e0]
      linarith
    change I.distance F.fan.left.primary F.fan.right.primary ≤ F.fan.pair.totalLength at hdist
    nlinarith
  · have hb := F.fan.crossing_barrier hred F.fan.left.primary F.root
      F.fan.left.primary_terminal F.root_terminal
      (F.fan.limb_primary_in_region F.fan.left F.fan.parent_ne_left) F.root_outside
    have hdiam := terminal_distance_le_diameter I F.fan.left.primary_terminal F.root_terminal
    norm_num [chi, e0, delta0, b0, p] at hparent hb ⊢
    nlinarith

theorem ShortStar.grid_scale (A : ShortStar S) (hred : Reduced S) (g : Grid) (hg : g.Covers I) :
    ∃ i : Fin (g.intervals + 1), g.scale i ≤ p * A.ell ∧ p * A.ell < omega * g.scale i := by
  obtain ⟨hlo, hhi⟩ := A.scale_range hred
  obtain ⟨i, j, hi, hi', _, _⟩ := g.bracket_of_covers I hg _ hlo hhi
  exact ⟨i, hi, hi'⟩

theorem RootedFringe.grid_scale {parent v : ↥S.vertices} (F : RootedFringe S parent v)
    (hred : Reduced S) (hparent : delta0 * F.fan.pair.totalLength ≤ I.distance parent v)
    (g : Grid) (hg : g.Covers I) :
    ∃ i : Fin (g.intervals + 1),
      F.fan.pair.totalLength / (chi - 1) < g.scale i ∧
      g.scale i ≤ omega * F.fan.pair.totalLength / (chi - 1) := by
  obtain ⟨hlo, hhi⟩ := F.regular_scale_range hred hparent
  obtain ⟨i, j, _, _, hj, hj'⟩ := g.bracket_of_covers I hg _ hlo hhi
  exact ⟨j, hj, by simpa only [mul_div_assoc] using hj'⟩

end Tree

end SteinerUpperBound.Structural

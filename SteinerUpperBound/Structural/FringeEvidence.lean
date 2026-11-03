module

public import SteinerUpperBound.Structural.Limbs
public import SteinerUpperBound.Structural.Components
public import SteinerUpperBound.Structural.LocalCost

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

structure LimbPair (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices) where
  left : Limb S v
  right : Limb S v
  disjoint : Disjoint left.region right.region

namespace LimbPair

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable abbrev ell (F : LimbPair S v) : ℝ := min F.left.length F.right.length
noncomputable abbrev totalLength (F : LimbPair S v) : ℝ := F.left.length + F.right.length

theorem ell_pos (F : LimbPair S v) : 0 < F.ell :=
  lt_min F.left.length_pos F.right.length_pos

theorem right_outside (F : LimbPair S v) : (F.right.primary : V) ∉ F.left.region := by
  intro h
  exact Finset.disjoint_left.mp F.disjoint h F.right.primary_mem_region

theorem left_outside (F : LimbPair S v) : (F.left.primary : V) ∉ F.right.region := by
  intro h
  exact Finset.disjoint_left.mp F.disjoint F.left.primary_mem_region h

theorem port_distance_le (F : LimbPair S v) :
    I.distance F.left.primary F.right.primary ≤ F.totalLength := by
  have h1 := F.left.primary_distance_le
  have h2 := F.right.primary_distance_le
  have ht := I.distance_triangle (F.left.primary : V) v F.right.primary
  rw [I.distance_comm (F.left.primary : V) v] at ht
  linarith

theorem lengths_comparable (F : LimbPair S v) (hred : Reduced S) :
    b0 * F.left.length < F.right.length ∧ b0 * F.right.length < F.left.length := by
  have h1 := F.left.crossing_barrier hred F.left.primary_terminal F.right.primary_terminal
    F.left.primary_mem_region F.right_outside
  have h2 := F.right.crossing_barrier hred F.right.primary_terminal F.left.primary_terminal
    F.right.primary_mem_region F.left_outside
  have ht := F.port_distance_le
  rw [I.distance_comm (F.right.primary : V) F.left.primary] at h2
  unfold b0
  constructor <;> nlinarith

theorem lengths_le_ell (F : LimbPair S v) (hred : Reduced S) :
    F.left.length ≤ F.ell / b0 ∧ F.right.length ≤ F.ell / b0 := by
  obtain ⟨hl, hr⟩ := F.lengths_comparable hred
  have hp := F.ell_pos
  dsimp only [ell] at hp ⊢
  by_cases h : F.left.length ≤ F.right.length
  · rw [min_eq_left h] at *
    norm_num [b0, p, chi, e0] at *
    constructor <;> nlinarith
  · rw [min_eq_right (le_of_not_ge h)] at *
    norm_num [b0, p, chi, e0] at *
    constructor <;> nlinarith

theorem total_le_ell (F : LimbPair S v) (hred : Reduced S) :
    F.totalLength ≤ 2 * F.ell / b0 := by
  obtain ⟨hl, hr⟩ := F.lengths_le_ell hred
  change F.left.length + F.right.length ≤ _
  norm_num [b0, p, chi, e0] at hl hr ⊢
  linarith

end LimbPair

theorem regular_margin {ell s sp R B c : ℝ}
    (hell : 0 < ell) (hlarge : alpha0 * ell ≤ s)
    (hs : s ≤ ell / b0) (hsp : sp ≤ s / (chi - 1))
    (hR : R ≤ 2 * ell / b0)
    (hB : p * ell + min (chi * s) (p * ell) ≤ B) (hc : c ≤ R + sp) :
    (8 / 1000 : ℝ) * ell < B - c := by
  by_cases h : chi * s ≤ p * ell
  · rw [min_eq_left h] at hB
    norm_num [alpha0, b0, p, chi, e0] at hlarge hs hsp hR hB
    nlinarith
  · rw [min_eq_right (le_of_not_ge h)] at hB
    norm_num [alpha0, b0, p, chi, e0] at hlarge hs hsp hR hB
    nlinarith

theorem cherry_local_evidence_explicit {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (C : Cherry S v) (R : Limb S v)
    (hdisj : Disjoint (Limb.cherry C).region R.region) (hred : Reduced S)
    (hlarge : alpha0 * (Limb.cherry C).length ≤ I.distance C.center C.primary)
    (a : ℝ)
    (hlo : ((Limb.cherry C).length + R.length) / (chi - 1) < a)
    (hhi : a ≤ omega * ((Limb.cherry C).length + R.length) / (chi - 1)) :
    ∃ D ∈ components I a,
      ({(C.primary : V), (C.secondary : V), (R.primary : V)} : Finset V) ⊆ D ∧
      sigma0 * a ≤ localAdvantage I D ∧
      (Limb.cherry C).longerArm + R.longerArm < a := by
  classical
  let F : LimbPair S v := ⟨Limb.cherry C, R, hdisj⟩
  let Y : Finset V := {(C.primary : V), (C.secondary : V), (R.primary : V)}
  have hchi : 0 < chi - 1 := by norm_num [chi, e0]
  have hp : 0 ≤ p := by norm_num [p, chi, e0]
  have hs : 0 ≤ I.distance C.center C.primary := I.distance_nonneg _ _
  have hell := F.ell_pos
  have hRf := F.total_le_ell hred
  have hxz : (C.primary : V) ≠ (R.primary : V) := by
    intro h
    exact F.right_outside (h ▸ (Limb.cherry C).primary_mem_region)
  have hyz : (C.secondary : V) ≠ (R.primary : V) := by
    intro h
    exact F.right_outside (h ▸ C.secondary_mem_region)
  have hxy : (C.primary : V) ≠ (C.secondary : V) := fun h => C.ports_ne (Subtype.ext h)
  have hca : (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center C.primary :=
    (Tree.mem_region S v C.center C.primary).mp (Limb.cherry C).primary_mem_region
  have hcb : ¬ (S.graph.deleteEdges {s(v, C.center)}).Reachable C.center R.primary :=
    fun h => F.right_outside ((Tree.mem_region S v C.center R.primary).mpr h)
  have hvb := (delete_edge_two_sides S.graph S.isTree.connected v C.center R.primary).resolve_right hcb
  have hstrong := C.crossing_barrier_strong hred C.primary R.primary hca hvb
    C.primary_terminal R.primary_terminal
  have hports := F.port_distance_le
  change I.distance C.primary R.primary ≤ F.totalLength at hports
  have hss' : I.distance C.primary C.secondary ≤
      I.distance C.center C.primary + I.distance C.center C.secondary := by
    simpa only [I.distance_comm (C.primary : V) C.center] using
      I.distance_triangle (C.primary : V) C.center C.secondary
  have hz := I.distance_nonneg v C.center
  have hxySmall : I.distance C.primary C.secondary < a := by
    have hbound : I.distance C.primary C.secondary < F.totalLength / (chi - 1) := by
      apply (lt_div_iff₀ hchi).mpr
      have hchi0 : 0 ≤ chi := by norm_num [chi, e0]
      nlinarith [mul_le_mul_of_nonneg_left hss' hchi.le, mul_nonneg hchi0 hz]
    exact hbound.trans hlo
  have hxzSmall : I.distance C.primary R.primary < a := by
    have hpos : 0 < F.totalLength := add_pos (Limb.cherry C).length_pos R.length_pos
    have hlt : F.totalLength < F.totalLength / (chi - 1) := by
      norm_num [chi, e0] at hpos ⊢
      linarith
    exact hports.trans_lt (hlt.trans hlo)
  let D := component I a C.primary
  have hYsub : Y ⊆ D := by
    intro z hzY
    simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hzY
    rcases hzY with rfl | rfl | rfl
    · exact component_self I a C.primary_terminal
    · exact (mem_component I a C.primary C.secondary).mpr
        ⟨C.secondary_terminal, ((threshold_adj I a _ _).mpr
          ⟨hxy, C.primary_terminal, C.secondary_terminal, hxySmall⟩).reachable⟩
    · exact (mem_component I a C.primary R.primary).mpr
        ⟨R.primary_terminal, ((threshold_adj I a _ _).mpr
          ⟨hxz, C.primary_terminal, R.primary_terminal, hxzSmall⟩).reachable⟩
  have hYcard : Y.card = 3 := by simp [Y, hxy, hxz, hyz]
  have hB : p * F.ell + min (chi * I.distance C.center C.primary) (p * F.ell) ≤ benefit I Y := by
    have hbound : p * F.ell ≤ p * (Limb.cherry C).length :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hp
    have hM : p * F.ell ≤ horizon I := by
      have hc := (Limb.cherry C).crossing_barrier hred C.primary_terminal R.primary_terminal
        (Limb.cherry C).primary_mem_region F.right_outside
      exact (hbound.trans hc.le).trans (distance_lt_horizon I C.primary_terminal R.primary_terminal).le
    have hsmall0 : 0 ≤ min (chi * I.distance C.center C.primary) (p * F.ell) :=
      le_min (mul_nonneg (by norm_num [chi, e0]) hs) (mul_nonneg hp hell.le)
    have hsep {t : ℝ} (ht : t ≤ p * F.ell) :
        ClosedCut (threshold I t ⊔ terminalGraph S) ((Limb.cherry C).region : Set V) :=
      (Limb.cherry C).threshold_region_closed hred t (ht.trans hbound)
    have hb := benefit_three_ports I (terminalGraph S) Y
      (x := (C.primary : V)) (y := (C.secondary : V)) (z := (R.primary : V))
      (by simp [Y]) (by simp [Y]) (by simp [Y])
      (p * F.ell) (min (chi * I.distance C.center C.primary) (p * F.ell))
      hsmall0 (min_le_right _ _) hM
      (by
        intro t ht
        have hc := reduced_threshold_region_closed S hred C.center C.primary C.primary_arm
          C.center_nonterminal t (ht.2.trans (min_le_left _ _))
        exact hc.not_reachable ((Tree.mem_region S C.center C.primary C.primary).mpr
          (SimpleGraph.Reachable.refl _)) C.secondary_outside_primary_arm)
      (by
        intro t ht h
        exact (hsep ht.2).not_reachable (Limb.cherry C).primary_mem_region F.right_outside h.symm)
      (by
        intro t ht h
        exact (hsep ht.2).not_reachable C.secondary_mem_region F.right_outside h.symm)
    exact hb.trans (benefitWith_le_benefit I (terminalGraph S) Y)
  have hc : localCost I Y ≤ F.totalLength + I.distance C.center C.secondary := by
    have hstar := localCost_star_le I Y C.center
    have hcz : I.distance C.center R.primary ≤ I.distance v C.center + R.length := by
      have ht := I.distance_triangle (C.center : V) v R.primary
      rw [I.distance_comm (C.center : V) v] at ht
      have hR := R.primary_distance_le
      linarith
    have hsum : (∑ z ∈ Y, I.distance C.center z) =
        I.distance C.center C.primary + I.distance C.center C.secondary + I.distance C.center R.primary := by
      simp [Y, hxy, hxz, hyz, add_assoc]
    rw [hsum] at hstar
    change localCost I Y ≤
      (I.distance v C.center + I.distance C.center C.primary + R.length) + I.distance C.center C.secondary
    linarith
  have hsUpper : I.distance C.center C.primary ≤ F.ell / b0 := by
    have hr := (F.lengths_le_ell hred).1
    change I.distance v C.center + I.distance C.center C.primary ≤ F.ell / b0 at hr
    linarith
  have hsLarge : alpha0 * F.ell ≤ I.distance C.center C.primary := by
    have hel : F.ell ≤ (Limb.cherry C).length := min_le_left _ _
    have ha0 : 0 ≤ alpha0 := by norm_num [alpha0]
    exact (mul_le_mul_of_nonneg_left hel ha0).trans hlarge
  have hmargin := regular_margin hell hsLarge hsUpper (C.longer_arm_bound hred).le hRf hB hc
  have hscale : a < (203 / 100 : ℝ) * F.ell := by
    have hh := hhi
    change a ≤ omega * F.totalLength / (chi - 1) at hh
    norm_num [omega, chi, e0, b0, p] at hRf hh
    linarith
  have hscore : sigma0 * a ≤ localAdvantage I D := by
    have hw := localAdvantage_witness I D Y hYsub (by omega) (by omega)
    norm_num [sigma0] at *
    linarith
  have hcharge : (Limb.cherry C).longerArm + R.longerArm < a := by
    have h1 := (Limb.cherry C).longerArm_lt_length hred
    have h2 := R.longerArm_lt_length hred
    have hh : (Limb.cherry C).longerArm + R.longerArm < F.totalLength / (chi - 1) := by
      change (Limb.cherry C).longerArm + R.longerArm <
        ((Limb.cherry C).length + R.length) / (chi - 1)
      rw [add_div]
      linarith
    exact hh.trans hlo
  exact ⟨D, component_mem_components I a C.primary_terminal, hYsub, hscore, hcharge⟩

theorem cherry_local_evidence {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}
    (C : Cherry S v) (R : Limb S v)
    (hdisj : Disjoint (Limb.cherry C).region R.region) (hred : Reduced S)
    (hlarge : alpha0 * (Limb.cherry C).length ≤ I.distance C.center C.primary)
    (a : ℝ)
    (hlo : ((Limb.cherry C).length + R.length) / (chi - 1) < a)
    (hhi : a ≤ omega * ((Limb.cherry C).length + R.length) / (chi - 1)) :
    ∃ D ∈ components I a, sigma0 * a ≤ localAdvantage I D ∧
      (Limb.cherry C).longerArm + R.longerArm < a := by
  obtain ⟨D, hD, _, hscore, hcharge⟩ :=
    cherry_local_evidence_explicit C R hdisj hred hlarge a hlo hhi
  exact ⟨D, hD, hscore, hcharge⟩

end SteinerUpperBound.Structural.Tree

module

public import SteinerUpperBound.Structural.Limbs
public import SteinerUpperBound.Structural.Components

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

structure ShortStar (S : TreeGeometry.TreeSolution I) where
  attachment : Fin 3 → ↥S.vertices
  limb : ∀ j, Limb S (attachment j)
  kept : Fin 3
  shortest : ∀ j, (limb kept).length ≤ (limb j).length
  disjoint : ∀ i j, i ≠ j → Disjoint (limb i).region (limb j).region
  outside : ∀ i j, i ≠ j → (attachment i : V) ∉ (limb j).region
  core : SimpleGraph V
  core_le : core ≤ S.ambient
  core_nonterminal : Network.TerminalOnly (Finset.univ \ I.terminals) core
  core_connects : ∀ i j, core.Reachable (attachment i) (attachment j)
  core_cost : GraphCost.cost I.weight core ≤ theta0 * (limb kept).length

namespace ShortStar

variable {S : TreeGeometry.TreeSolution I}

noncomputable abbrev ell (A : ShortStar S) : ℝ := (A.limb A.kept).length

abbrev port (A : ShortStar S) (j : Fin 3) : V := ((A.limb j).primary : V)

abbrev center (A : ShortStar S) : V := A.attachment A.kept

noncomputable def charge (A : ShortStar S) : ℝ :=
  ∑ j ∈ Finset.univ.erase A.kept, (A.limb j).cost

theorem ell_pos (A : ShortStar S) : 0 < A.ell := (A.limb A.kept).length_pos

theorem port_terminal (A : ShortStar S) (j : Fin 3) : A.port j ∈ I.terminals :=
  (A.limb j).primary_terminal

theorem port_outside (A : ShortStar S) {i j : Fin 3} (hij : i ≠ j) :
    A.port j ∉ (A.limb i).region := by
  intro h
  exact Finset.disjoint_left.mp (A.disjoint i j hij) h (A.limb j).primary_mem_region

theorem core_distance_le (A : ShortStar S) (i j : Fin 3) :
    I.distance (A.attachment i) (A.attachment j) ≤ theta0 * A.ell :=
  (TreeGeometry.distance_le_cost_of_reachable I A.core (A.core_connects i j)).trans A.core_cost

theorem port_distance_le (A : ShortStar S) (i j : Fin 3) :
    I.distance (A.port i) (A.port j) ≤
      (A.limb i).length + theta0 * A.ell + (A.limb j).length := by
  have h1 := (A.limb i).primary_distance_le
  have h2 := (A.limb j).primary_distance_le
  have h3 := A.core_distance_le i j
  have ht1 := I.distance_triangle (A.port i) (A.attachment i) (A.port j)
  have ht2 := I.distance_triangle (A.attachment i) (A.attachment j) (A.port j)
  rw [I.distance_comm (A.port i) (A.attachment i)] at ht1
  linarith

theorem center_port_distance_le (A : ShortStar S) (j : Fin 3) :
    I.distance A.center (A.port j) ≤ (A.limb j).length + theta0 * A.ell := by
  have h1 := (A.limb j).primary_distance_le
  have h2 := A.core_distance_le A.kept j
  have ht := I.distance_triangle A.center (A.attachment j) (A.port j)
  linarith

theorem length_bound (A : ShortStar S) (hred : Reduced S) (j : Fin 3) :
    b0 * (A.limb j).length ≤ (1 + theta0) * A.ell := by
  by_cases hj : j = A.kept
  · have hp := A.ell_pos
    rw [hj]
    norm_num [b0, p, chi, e0, theta0]
    linarith
  · have hb := (A.limb j).crossing_barrier hred (A.port_terminal j)
      (A.port_terminal A.kept) (A.limb j).primary_mem_region (A.port_outside hj)
    have ht := A.port_distance_le j A.kept
    change p * (A.limb j).length < I.distance (A.port j) (A.port A.kept) at hb
    change I.distance (A.port j) (A.port A.kept) ≤
      (A.limb j).length + theta0 * A.ell + A.ell at ht
    unfold b0
    nlinarith

theorem ports_close (A : ShortStar S) (hred : Reduced S) (a : ℝ)
    (hscale : p * A.ell < omega * a) (j : Fin 3) :
    I.distance A.center (A.port j) < 3 * a / 5 := by
  have hl := A.length_bound hred j
  have hd := A.center_port_distance_le j
  have hp := A.ell_pos
  norm_num [b0, p, chi, e0, theta0, omega] at hl hd hscale
  linarith

theorem ports_augmented_separated (A : ShortStar S) (hred : Reduced S) (a : ℝ)
    (ha : a ≤ p * A.ell) {i j : Fin 3} (hij : i ≠ j) :
    ¬ (threshold I a ⊔ terminalGraph S).Reachable (A.port i) (A.port j) := by
  have hscale : a ≤ p * (A.limb i).length := by
    have hs := A.shortest i
    have hp : 0 ≤ p := by norm_num [p, chi, e0]
    exact ha.trans (mul_le_mul_of_nonneg_left hs hp)
  have hc := (A.limb i).threshold_region_closed hred a hscale
  exact hc.not_reachable (A.limb i).primary_mem_region (A.port_outside hij)

theorem center_eligible (A : ShortStar S) (hred : Reduced S) (a : ℝ)
    (ha : a ≤ p * A.ell) (hscale : p * A.ell < omega * a) :
    A.center ∈ eligible I a := by
  have hsep {i j : Fin 3} (hij : i ≠ j) :
      ¬ (threshold I a).Reachable (A.port i) (A.port j) :=
    fun h => A.ports_augmented_separated hred a ha hij (h.mono le_sup_left)
  exact row_eligible_of_three I a A.center (A.port_terminal 0) (A.port_terminal 1)
    (A.port_terminal 2) (A.ports_close hred a hscale 0).le (A.ports_close hred a hscale 1).le
      (A.ports_close hred a hscale 2).le (hsep (by decide)) (hsep (by decide)) (hsep (by decide))

theorem charge_le_scale (A : ShortStar S) (hred : Reduced S) (a : ℝ)
    (hscale : p * A.ell < omega * a) :
    A.charge ≤ (5 / 2 : ℝ) * a := by
  have hfactor : 0 ≤ 1 + 1 / (chi - 1) := by norm_num [chi, e0]
  have hb0 : 0 < b0 := by norm_num [b0, p, chi, e0]
  have hlimb (j : Fin 3) : (A.limb j).cost ≤
      (1 + 1 / (chi - 1)) * ((1 + theta0) / b0) * A.ell := by
    have hl := A.length_bound hred j
    have hd : (A.limb j).length ≤ (1 + theta0) / b0 * A.ell := by
      calc
        _ ≤ ((1 + theta0) * A.ell) / b0 := (le_div_iff₀ hb0).mpr (by nlinarith)
        _ = _ := by ring
    exact ((A.limb j).cost_le_length_factor hred).trans
      (by nlinarith [mul_le_mul_of_nonneg_left hd hfactor])
  have hsum : A.charge ≤ 2 *
      ((1 + 1 / (chi - 1)) * ((1 + theta0) / b0) * A.ell) := by
    unfold charge
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase A.kept,
          (1 + 1 / (chi - 1)) * ((1 + theta0) / b0) * A.ell :=
        Finset.sum_le_sum fun j _ => hlimb j
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ _)]
        norm_num
  have hp := A.ell_pos
  norm_num [chi, e0, theta0, b0, p, omega] at hsum hscale
  linarith

end ShortStar

end SteinerUpperBound.Structural.Tree

module

public import SteinerUpperBound.Structural.StarReconnection
public import SteinerUpperBound.Structural.PromotionBounds

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

namespace CherryData

theorem delta_nonterminal_nonpos (C : CherryData I) :
    C.delta (nonterminalWeight I) ≤ 0 := by
  have hn := I.distance_nonneg C.center C.attachment
  simp [delta, nonterminalWeight_mk, nonterminalDistance, C.attachment_nonterminal,
    C.center_nonterminal, C.primary_terminal, C.secondary_terminal]
  exact hn

theorem delta_count (C : CherryData I) : C.delta (steinerCountWeight I) = -2 := by
  have hsib : steinerCountWeight I s(C.primary, C.secondary) = 0 := by
    simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj,
      C.ports_ne, C.primary_terminal, C.secondary_terminal]
  have hstem : steinerCountWeight I s(C.primary, C.attachment) = 1 := by
    rw [Sym2.eq_swap]
    exact steinerCountWeight_incident I C.attachment_nonterminal _
  norm_num [delta, hsib, hstem, steinerCountWeight_incident I C.center_nonterminal]

end CherryData

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable def cherryDelta (L : Limb S v) (w : Sym2 V → ℝ) : ℝ :=
  ∑ C ∈ L.cherrySet, C.delta w

theorem cherryDelta_potential_removed (L : Limb S v) :
    L.cherryDelta (potentialWeight I) - potentialWeight I s((v : V), (L.primary : V)) =
      L.siblingWeight I.weight - chi * L.cost := by
  cases L with
  | direct x hv hx h =>
    simp [cherryDelta, cherrySet, primary, siblingWeight, cost, potentialWeight_mk, potentialDistance, hv]
  | cherry C =>
    simp only [cherryDelta, cherrySet, Finset.sum_singleton, CherryData.delta, Cherry.data,
      potentialWeight_mk, potentialDistance, C.primary_terminal, C.secondary_terminal,
      C.attachment_nonterminal, C.center_nonterminal, and_self, false_and, and_false,
      ↓reduceIte, primary, siblingWeight, Instance.weight_mk, cost]
    rw [I.distance_comm (C.primary : V) v, I.distance_comm (C.center : V) v]
    ring

theorem cherryDelta_potential_le (L : Limb S v) :
    L.cherryDelta (potentialWeight I) ≤ (2 - chi) * L.longerArm := by
  have he := L.cherryDelta_potential_removed
  have hb := L.potential_reconnection_bound
  rw [Limb.siblingWeight_potential, Limb.edgeWeight_potential] at hb
  linarith

theorem sibling_plus_route (L : Limb S v) (ell extra route : ℝ)
    (hmin : ell ≤ L.length) (hroute : route ≤ L.length + extra + ell) :
    L.siblingWeight I.weight + route ≤ 2 * L.cost + extra := by
  cases L with
  | direct x hv hx h =>
    change 0 + route ≤ 2 * I.distance v x + extra
    change ell ≤ I.distance v x at hmin
    change route ≤ I.distance v x + extra + ell at hroute
    linarith
  | cherry C =>
    have ht := I.distance_triangle (C.primary : V) C.center C.secondary
    rw [I.distance_comm (C.primary : V) C.center] at ht
    have ho := C.ordered
    change ell ≤ I.distance v C.center + I.distance C.center C.primary at hmin
    change route ≤ (I.distance v C.center + I.distance C.center C.primary) + extra + ell at hroute
    change I.distance C.primary C.secondary + route ≤
      2 * (I.distance v C.center + I.distance C.center C.primary + I.distance C.center C.secondary) + extra
    linarith

end Limb

namespace ShortStar

variable {S : TreeGeometry.TreeSolution I}

theorem charge_ge_two_ell (A : ShortStar S) : 2 * A.ell ≤ A.charge := by
  have heach : ∀ i ∈ Finset.univ.erase A.kept, A.ell ≤ (A.limb i).cost :=
    fun i hi => (A.shortest i).trans (A.limb i).length_le_cost
  have hc : (Finset.univ.erase A.kept).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    norm_num
  calc
    _ = ∑ _i ∈ Finset.univ.erase A.kept, A.ell := by simp [hc]
    _ ≤ _ := Finset.sum_le_sum heach

theorem potential_price (A : ShortStar S) (hred : Reduced S)
    (Q : TreeGeometry.TreeSolution I)
    (hc : ∀ (w : Sym2 V → ℝ), (∀ e, 0 ≤ w e) →
      GraphCost.cost (fun e => w (e.map Subtype.val)) Q.graph ≤
        GraphCost.cost (fun e => w (e.map Subtype.val)) S.graph +
          (∑ C ∈ A.cherries, C.delta w) +
          ∑ i ∈ Finset.univ.erase A.kept,
            (w s(A.port A.kept, A.port i) - w s((A.attachment i : V), A.port i))) :
    potential Q ≤ potential S + (21 / 10 - chi) * A.charge := by
  classical
  let D : Finset (Fin 3) := Finset.univ.erase A.kept
  let f := fun i : Fin 3 => (A.limb i).cherryDelta (potentialWeight I)
  let g := fun i : Fin 3 => I.distance (A.port A.kept) (A.port i) -
    potentialWeight I s((A.attachment i : V), A.port i)
  have hcard : D.card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    norm_num
  have hport (i : Fin 3) : potentialWeight I s(A.port A.kept, A.port i) =
      I.distance (A.port A.kept) (A.port i) := by
    simp [potentialWeight_mk, potentialDistance, A.port_terminal A.kept, A.port_terminal i]
  have hh := hc (potentialWeight I) (potentialWeight_nonneg I)
  rw [A.delta_sum] at hh
  simp only [hport] at hh
  change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤
    GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph +
      (∑ i, f i) + ∑ i ∈ D, g i at hh
  have hsplit : (∑ i, f i) = f A.kept + ∑ i ∈ D, f i := by
    have he := Finset.sum_erase_add Finset.univ f (Finset.mem_univ A.kept)
    linarith
  have hmerge : (∑ i ∈ D, f i) + (∑ i ∈ D, g i) = ∑ i ∈ D, (f i + g i) :=
    (Finset.sum_add_distrib).symm
  have heach : ∀ i ∈ D, f i + g i ≤ (2 - chi) * (A.limb i).cost + theta0 * A.ell := by
    intro i hi
    have he := (A.limb i).cherryDelta_potential_removed
    change f i - potentialWeight I s((A.attachment i : V), A.port i) =
      (A.limb i).siblingWeight I.weight - chi * (A.limb i).cost at he
    have hp := A.port_distance_le i A.kept
    change I.distance (A.port i) (A.port A.kept) ≤
      (A.limb i).length + theta0 * A.ell + A.ell at hp
    rw [I.distance_comm (A.port i) (A.port A.kept)] at hp
    have hb := (A.limb i).sibling_plus_route A.ell (theta0 * A.ell)
      (I.distance (A.port A.kept) (A.port i)) (A.shortest i) hp
    dsimp only [g]
    nlinarith
  have hsum : (∑ i ∈ D, (f i + g i)) ≤
      (2 - chi) * A.charge + 2 * theta0 * A.ell := by
    have hs := Finset.sum_le_sum heach
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul, hcard, ← Finset.sum_add_distrib] at hs
    change (∑ i ∈ D, (f i + g i)) ≤
      (2 - chi) * A.charge + (2 : ℝ) * (theta0 * A.ell) at hs
    nlinarith
  have hkept := (A.limb A.kept).cherryDelta_potential_le
  have hlonger := (A.limb A.kept).longerArm_lt_length hred
  change (A.limb A.kept).longerArm < A.ell / (chi - 1) at hlonger
  have hcharge := A.charge_ge_two_ell
  have hp := A.ell_pos
  change f A.kept ≤ (2 - chi) * (A.limb A.kept).longerArm at hkept
  change GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) Q.graph ≤
    GraphCost.cost (fun e => potentialWeight I (e.map Subtype.val)) S.graph +
      (21 / 10 - chi) * A.charge
  norm_num [chi, e0, theta0] at hsum hkept hlonger ⊢
  nlinarith

theorem operated_exists (A : ShortStar S) (hred : Reduced S) :
    ∃ Q : TreeGeometry.TreeSolution I, Q.vertices ⊆ S.vertices ∧ Q.IsClean ∧
      terminalGraph S ≤ terminalGraph Q ∧
      (∀ i j, (terminalGraph Q).Reachable (A.port i) (A.port j)) ∧
      nonterminalCost Q ≤ nonterminalCost S ∧
      (steinerEdges Q).card < (steinerEdges S).card ∧
      potential Q ≤ potential S + (21 / 10 - chi) * A.charge := by
  classical
  obtain ⟨R, hsub, hperm, hports, hcost⟩ := A.reconnected_exists
  have hpot := A.potential_price hred R hcost
  have hnn := hcost (nonterminalWeight I) (nonterminalWeight_nonneg I)
  have hdeltaNN : (∑ C ∈ A.cherries, C.delta (nonterminalWeight I)) ≤ 0 :=
    Finset.sum_nonpos (fun C hC => C.delta_nonterminal_nonpos)
  have hNN (i : Fin 3) : nonterminalWeight I s(A.port A.kept, A.port i) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, A.port_terminal A.kept]
  have hOldNN (i : Fin 3) : nonterminalWeight I s((A.attachment i : V), A.port i) = 0 := by
    simp [nonterminalWeight_mk, nonterminalDistance, A.port_terminal i]
  simp only [hNN, hOldNN, sub_self, Finset.sum_const_zero, add_zero] at hnn
  have hnn' : nonterminalCost R ≤ nonterminalCost S := by
    change GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) R.graph ≤
      GraphCost.cost (fun e => nonterminalWeight I (e.map Subtype.val)) S.graph
    linarith
  have hcount := hcost (steinerCountWeight I) (steinerCountWeight_nonneg I)
  have hdeltaCount : (∑ C ∈ A.cherries, C.delta (steinerCountWeight I)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro C hC
    rw [C.delta_count]
    norm_num
  have hcard : (Finset.univ.erase A.kept).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    norm_num
  have hsumCount : (∑ i ∈ Finset.univ.erase A.kept,
      (steinerCountWeight I s(A.port A.kept, A.port i) -
        steinerCountWeight I s((A.attachment i : V), A.port i))) = -2 := by
    calc
      _ = ∑ _i ∈ Finset.univ.erase A.kept, (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne := A.ports_ne (Ne.symm (Finset.mem_erase.mp hi).1)
        have hnew : steinerCountWeight I s(A.port A.kept, A.port i) = 0 := by
          simp [steinerCountWeight, SimpleGraph.mem_edgeSet, Network.completeOn_adj, hne,
            A.port_terminal A.kept, A.port_terminal i]
        rw [hnew, steinerCountWeight_incident I (A.limb i).attachment_nonterminal]
        norm_num
      _ = _ := by simp [hcard]
  rw [hsumCount, steinerCountWeight_cost R, steinerCountWeight_cost S] at hcount
  have hcountN : (steinerEdges R).card + 1 ≤ (steinerEdges S).card := by
    exact_mod_cast (show ((steinerEdges R).card : ℝ) + 1 ≤ (steinerEdges S).card by linarith)
  obtain ⟨Q, hQsub, hclean, hQpot, hQnn, hQperm, hQcount⟩ :=
    cleanup_preserving R ⟨A.port 0, A.port_terminal 0⟩
  exact ⟨Q, hQsub.trans hsub, hclean, hperm.trans hQperm,
    (fun i j => (hports i j).mono hQperm), hQnn.trans hnn',
      lt_of_le_of_lt hQcount (Nat.lt_of_succ_le hcountN), hQpot.trans hpot⟩

end ShortStar

end SteinerUpperBound.Structural.Tree

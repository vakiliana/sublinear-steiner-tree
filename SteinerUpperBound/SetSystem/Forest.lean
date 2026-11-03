module

public import SteinerUpperBound.SetSystem.SelectedIncidence
public import SteinerUpperBound.SpanningForest

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U V : Type*}

theorem spanningRun_acyclic (edges : List (Sym2 V)) (G : SimpleGraph V)
    (hG : G.IsAcyclic) : (SpanningForest.run edges G).IsAcyclic := by
  classical
  induction edges generalizing G with
  | nil => exact hG
  | cons e edges ih =>
      induction e using Sym2.inductionOn with
      | _ x y =>
          by_cases h : G.Reachable x y
          · simpa only [SpanningForest.run, SpanningForest.step,
              SpanningForest.linked_mk, h, ite_true] using ih G hG
          · apply ih
            simpa only [SpanningForest.step, SpanningForest.linked_mk, h, ite_false,
              SimpleGraph.edge]
              using hG.sup_edge_of_not_reachable h

noncomputable def spanningForest [Fintype V] (G : SimpleGraph V) : SimpleGraph V :=
  SpanningForest.run G.edgeFinset.toList ⊥

theorem spanningForest_le [Fintype V] (G : SimpleGraph V) : spanningForest G ≤ G := by
  classical
  unfold spanningForest
  have h := SpanningForest.run_le G.edgeFinset.toList (⊥ : SimpleGraph V)
  simpa only [Finset.toList_toFinset, GraphRank.ofEdges_edgeFinset, bot_sup_eq] using h

theorem spanningForest_acyclic [Fintype V] (G : SimpleGraph V) :
    (spanningForest G).IsAcyclic :=
  spanningRun_acyclic _ _ SimpleGraph.isAcyclic_bot

theorem spanningForest_reachable [Fintype V] (G : SimpleGraph V) (x y : V) :
    (spanningForest G).Reachable x y ↔ G.Reachable x y := by
  classical
  have hs := SpanningForest.run_space G.edgeFinset.toList (⊥ : SimpleGraph V)
  simp only [GraphRank.space_bot, Finset.toList_toFinset,
    GraphRank.ofEdges_edgeFinset, bot_sup_eq] at hs
  rw [← GraphRank.mem_space_iff, ← GraphRank.mem_space_iff]
  change GraphRank.delta x y ∈ GraphRank.space (SpanningForest.run G.edgeFinset.toList ⊥) ↔ _
  rw [hs]

noncomputable def forestPorts [Fintype U] (H : SimpleGraph (U ⊕ R)) (r : R) :
    Finset U := Finset.univ.filter (fun x => H.Adj (Sum.inl x) (Sum.inr r))

theorem incidence_forestPorts [Fintype U] (H : SimpleGraph (U ⊕ R))
    (ports : R → Finset U) (hle : H ≤ incidenceGraph ports) :
    incidenceGraph (forestPorts H) = H := by
  classical
  ext v w
  cases v with
  | inl x =>
      cases w with
      | inl y =>
          exact ⟨False.elim, fun h => (hle h).elim⟩
      | inr r => simp [forestPorts]
  | inr r =>
      cases w with
      | inl x => simpa [forestPorts] using (SimpleGraph.adj_comm H (Sum.inl x) (Sum.inr r))
      | inr s =>
          exact ⟨False.elim, fun h => (hle h).elim⟩

theorem prune_rows_profit (F : Finset R) (ports : R → Finset U) :
    (∑ r ∈ F, ((ports r).card : ℝ)) - 2 * F.card ≤
      (∑ r ∈ F.filter (fun r => 3 ≤ (ports r).card), ((ports r).card : ℝ)) -
        2 * (F.filter (fun r => 3 ≤ (ports r).card)).card := by
  classical
  let S := F.filter (fun r => 3 ≤ (ports r).card)
  have hSF : S ⊆ F := Finset.filter_subset _ _
  have hdrop : ∑ r ∈ F \ S, (((ports r).card : ℝ) - 2) ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    obtain ⟨hrF, hrS⟩ := Finset.mem_sdiff.mp hr
    have hc : (ports r).card ≤ 2 := by
      by_contra hc
      exact hrS (Finset.mem_filter.mpr ⟨hrF, by omega⟩)
    exact sub_nonpos.mpr (by exact_mod_cast hc)
  have hsplit := Finset.sum_sdiff hSF (f := fun r => ((ports r).card : ℝ) - 2)
  have hh : ∑ r ∈ F, (((ports r).card : ℝ) - 2) ≤
      ∑ r ∈ S, (((ports r).card : ℝ) - 2) := by linarith
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm] using hh

/-- The labels and ports are actual row memberships; no forest or saving conclusion is assumed. -/
theorem saving_forest (E : Finset R) (rows : R → Finset U) (A : Finset U)
    (hlarge : ∀ r ∈ E, 3 ≤ (A ∩ rows r).card) :
    ∃ (B : Finset U) (S : Finset R) (ports : ↥S → Finset ↥B),
      B ⊆ A ∧ S ⊆ E ∧
      (∀ r, ∀ x ∈ ports r, x.val ∈ rows r.val) ∧
      (∀ r, 3 ≤ (ports r).card) ∧
      (incidenceGraph ports).IsAcyclic ∧
      saving E rows A / 2 ≤ (∑ r, ((ports r).card : ℝ)) - 2 * S.card ∧
      3 * S.card ≤ ∑ r, (ports r).card ∧
      GraphRank.rank (portGraph ports) + S.card = ∑ r, (ports r).card := by
  classical
  obtain ⟨F, hFE, hopt⟩ := saving_attained E rows A
  let B := coveredElements F rows A
  let G := incidenceGraph (selectedPorts F rows A)
  let H := spanningForest G
  let Q := forestPorts H
  have hHle : H ≤ G := spanningForest_le G
  have hHacyc : H.IsAcyclic := spanningForest_acyclic G
  have hQeq : incidenceGraph Q = H := incidence_forestPorts H _ hHle
  have hQacyc : (incidenceGraph Q).IsAcyclic := hQeq ▸ hHacyc
  have hcomp : Nat.card H.ConnectedComponent = Nat.card G.ConnectedComponent :=
    Nat.card_congr (componentEquiv H G id Function.surjective_id
      (spanningForest_reachable G))
  have heuler := GraphRank.rank_add_components H
  rw [forest_rank H hHacyc, hcomp, ← hQeq, incidence_edges_card] at heuler
  have heuler' : (∑ r : ↥F, ((Q r).card : ℝ)) + Nat.card G.ConnectedComponent =
      (B.card : ℝ) + F.card := by
    have he : (∑ r : ↥F, (Q r).card) + Nat.card G.ConnectedComponent = B.card + F.card := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_coe] using heuler
    exact_mod_cast he
  have hc := selectedIncidence_components_bound E F rows A hFE hlarge
  have hprofit : saving E rows A / 2 ≤ (∑ r : ↥F, ((Q r).card : ℝ)) - 2 * F.card := by
    change saving E rows A = (B.card : ℝ) - F.card at hopt
    linarith
  let p : R → Finset ↥B := fun r => if hr : r ∈ F then Q ⟨r, hr⟩ else ∅
  have hp (r : ↥F) : p r.val = Q r := by simp [p, r.property]
  let S := F.filter (fun r => 3 ≤ (p r).card)
  have hSF : S ⊆ F := Finset.filter_subset _ _
  let ports : ↥S → Finset ↥B := fun r => p r.val
  have hsumF : (∑ r ∈ F, ((p r).card : ℝ)) = ∑ r : ↥F, ((Q r).card : ℝ) := by
    rw [← Finset.sum_coe_sort]
    exact Finset.sum_congr rfl (fun r _ => congrArg (fun t : Finset ↥B => (t.card : ℝ)) (hp r))
  have hsumS : (∑ r ∈ S, ((p r).card : ℝ)) = ∑ r : ↥S, ((ports r).card : ℝ) := by
    rw [← Finset.sum_coe_sort]
  have hretained (r : ↥S) : 3 ≤ (ports r).card := (Finset.mem_filter.mp r.property).2
  have hports_eq (r : ↥S) : ports r = Q ⟨r.val, hSF r.property⟩ :=
    hp ⟨r.val, hSF r.property⟩
  have hacyc : (incidenceGraph ports).IsAcyclic := by
    have he : ports = fun r : ↥S => Q ⟨r.val, hSF r.property⟩ :=
      funext hports_eq
    rw [he]
    apply incidence_reindex_acyclic Q (fun r : ↥S => (⟨r.val, hSF r.property⟩ : ↥F))
      (fun r s h => by
        apply Subtype.ext
        exact congrArg (fun t : ↥F => t.val) h) hQacyc
  have hsound (r : ↥S) (x : ↥B) (hx : x ∈ ports r) : x.val ∈ rows r.val := by
    rw [hports_eq r] at hx
    have ha := (Finset.mem_filter.mp hx).2
    have hb := hHle ha
    exact (Finset.mem_filter.mp hb).2
  have hfinal : saving E rows A / 2 ≤ (∑ r, ((ports r).card : ℝ)) - 2 * S.card := by
    have hprune := prune_rows_profit F p
    change _ ≤ (∑ r ∈ S, ((p r).card : ℝ)) - 2 * S.card at hprune
    rw [hsumF, hsumS] at hprune
    exact hprofit.trans hprune
  have hdegree : 3 * S.card ≤ ∑ r : ↥S, (ports r).card := by
    calc
      _ = ∑ _r : ↥S, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun r _ => hretained r)
  have hrank := incidence_forest_port_rank ports
    (fun r => Finset.card_pos.mp (by have := hretained r; omega)) hacyc
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hrank
  exact ⟨B, S, ports, Finset.inter_subset_left, hSF.trans hFE, hsound,
    hretained, hacyc, hfinal, hdegree, hrank⟩

end SteinerUpperBound.SetSystem

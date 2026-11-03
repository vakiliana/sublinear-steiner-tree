module

public import SteinerUpperBound.TreeGeometry.Basic

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*}

noncomputable def collapse (v x : V) (z : V) : V :=
  if z = v then x else z

@[simp] theorem collapse_at (v x : V) : collapse v x v = x := by
  classical
  simp [collapse]

theorem collapse_of_ne {v x z : V} (h : z ≠ v) : collapse v x z = z := by
  classical
  simp [collapse, h]

theorem collapse_ne {v x : V} (h : x ≠ v) (z : V) : collapse v x z ≠ v := by
  classical
  by_cases hz : z = v <;> simp [collapse, hz, h]

theorem feasible_map_fixed (T : Finset V) (G : SimpleGraph V)
    (hG : Network.Feasible T G) (f : V → V) (hf : ∀ x ∈ T, f x = x) :
    Network.Feasible T (G.map f) := by
  intro x hx y hy
  simpa only [hf x hx, hf y hy] using reachable_map (hG x hx y hy) f

theorem collapse_support_subset (G : SimpleGraph V) (U : Finset V)
    (hG : G.support ⊆ (U : Set V)) (v x : V) (hx : x ∈ U) (hxv : x ≠ v) :
    (G.map (collapse v x)).support ⊆ (U.erase v : Set V) := by
  classical
  intro y hy
  obtain ⟨z, hyz⟩ := hy
  obtain ⟨_, a, b, hab, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hyz
  have ha : a ∈ U := hG ⟨b, hab⟩
  apply Finset.mem_erase.mpr
  refine ⟨collapse_ne hxv a, ?_⟩
  by_cases hav : a = v
  · simpa [collapse, hav] using hx
  · simpa [collapse, hav] using ha

theorem sum_two_charge_le {α : Type*} [DecidableEq α] (E : Finset α)
    (a b : α) (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b)
    (f g : α → ℝ) (hpair : f a + f b ≤ g a + g b)
    (hrest : ∀ e ∈ E, e ≠ a → e ≠ b → f e ≤ g e) :
    ∑ e ∈ E, f e ≤ ∑ e ∈ E, g e := by
  have hba : b ∈ E.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hf := Finset.sum_erase_add E f ha
  have hg := Finset.sum_erase_add E g ha
  have hf' := Finset.sum_erase_add (E.erase a) f hba
  have hg' := Finset.sum_erase_add (E.erase a) g hba
  have hr : ∑ e ∈ (E.erase a).erase b, f e ≤ ∑ e ∈ (E.erase a).erase b, g e := by
    apply Finset.sum_le_sum
    intro e he
    obtain ⟨heb, he⟩ := Finset.mem_erase.mp he
    obtain ⟨hea, he⟩ := Finset.mem_erase.mp he
    exact hrest e he hea heb
  linarith

theorem collapse_leaf_cost_le [Fintype V] (I : Instance V) (G : SimpleGraph V)
    (v x : V) (hx : G.Adj v x)
    (hn : ∀ z, G.Adj v z → z = x) :
    GraphCost.cost I.weight (G.map (collapse v x)) ≤ GraphCost.cost I.weight G := by
  classical
  apply (MetricComparison.Padding.cost_map_le G (collapse v x)
    (fun e => I.weight (e.map (collapse v x))) I.weight I.weight_nonneg
    (fun _ _ => le_rfl)).trans
  apply Finset.sum_le_sum
  intro e he
  rcases e with ⟨a, b⟩
  have hab : G.Adj a b := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
  simp only [Sym2.map_mk, Instance.weight_mk]
  by_cases hav : a = v
  · subst a
    have hb := hn b hab
    subst b
    simp only [collapse_at, collapse_of_ne hx.ne.symm, Instance.distance_self]
    exact I.distance_nonneg _ _
  by_cases hbv : b = v
  · subst b
    have ha := hn a hab.symm
    subst a
    simp only [collapse_at, collapse_of_ne hx.ne.symm, Instance.distance_self]
    exact I.distance_nonneg _ _
  · rw [collapse_of_ne hav, collapse_of_ne hbv]

theorem collapse_two_cost_le [Fintype V] (I : Instance V) (G : SimpleGraph V)
    (v x y : V) (hx : G.Adj v x) (hy : G.Adj v y) (hxy : x ≠ y)
    (hn : ∀ z, G.Adj v z → z = x ∨ z = y) :
    GraphCost.cost I.weight (G.map (collapse v x)) ≤ GraphCost.cost I.weight G := by
  classical
  apply (MetricComparison.Padding.cost_map_le G (collapse v x)
    (fun e => I.weight (e.map (collapse v x))) I.weight I.weight_nonneg
    (fun _ _ => le_rfl)).trans
  apply sum_two_charge_le G.edgeFinset s(v, x) s(v, y)
  · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hx
  · simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hy
  · intro h
    have := (Sym2.eq_iff.mp h)
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · exact hxy h
    · exact hy.ne h
  · simp only [Sym2.map_mk, Instance.weight_mk, collapse_at,
      collapse_of_ne hx.ne.symm, collapse_of_ne hy.ne.symm, Instance.distance_self, zero_add]
    exact (I.distance_triangle x v y).trans_eq (by rw [I.distance_comm x v])
  · intro e he hea heb
    rcases e with ⟨a, b⟩
    have hab : G.Adj a b := by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
    have hav : a ≠ v := by
      intro hav
      subst a
      rcases hn b hab with h | h
      · exact hea (by rw [h])
      · exact heb (by rw [h])
    have hbv : b ≠ v := by
      intro hbv
      subst b
      rcases hn a hab.symm with h | h
      · exact hea (by rw [h, Sym2.eq_swap])
      · exact heb (by rw [h, Sym2.eq_swap])
    simp only [Sym2.map_mk, Instance.weight_mk, collapse_of_ne hav, collapse_of_ne hbv,
      le_refl]

theorem exists_collapse_cost_le [Fintype V] (I : Instance V) (G : SimpleGraph V)
    (v : V) (hpos : 0 < G.degree v) (hdeg : G.degree v ≤ 2) :
    ∃ x, G.Adj v x ∧
      GraphCost.cost I.weight (G.map (collapse v x)) ≤ GraphCost.cost I.weight G := by
  classical
  by_cases h1 : G.degree v = 1
  · obtain ⟨x, hx, hn⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h1
    exact ⟨x, hx, collapse_leaf_cost_le I G v x hx (fun z hz => hn z hz)⟩
  · have h2 : (G.neighborFinset v).card = 2 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      omega
    obtain ⟨x, y, hxy, hn⟩ := Finset.card_eq_two.mp h2
    have hadj (z : V) : G.Adj v z ↔ z = x ∨ z = y := by
      have h := Finset.ext_iff.mp hn z
      simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_insert,
        Finset.mem_singleton] using h
    exact ⟨x, (hadj x).mpr (Or.inl rfl),
      collapse_two_cost_le I G v x y ((hadj x).mpr (Or.inl rfl))
        ((hadj y).mpr (Or.inr rfl)) hxy (fun z hz => (hadj z).mp hz)⟩

namespace TreeSolution

variable {I : Instance V}

theorem ambient_support_subset (S : TreeSolution I) :
    S.ambient.support ⊆ (S.vertices : Set V) := by
  intro x hx
  obtain ⟨y, hxy⟩ := hx
  obtain ⟨_, a, b, _, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp hxy
  exact a.property

theorem degree_ambient [Fintype V] (S : TreeSolution I) (v : ↥S.vertices) :
    S.ambient.degree v = S.graph.degree v := by
  classical
  rw [← SimpleGraph.ncard_neighborSet, ← SimpleGraph.ncard_neighborSet]
  simp only [ambient]
  have h := SimpleGraph.degree_map_apply S.graph
    (⟨Subtype.val, Subtype.val_injective⟩ : ↥S.vertices ↪ V) v
  simpa only [← SimpleGraph.ncard_neighborSet, Function.Embedding.coeFn_mk] using h

theorem remove_nonterminal [Fintype V] (S : TreeSolution I)
    (hT : I.terminals.Nonempty) (v : ↥S.vertices)
    (hv : (v : V) ∉ I.terminals) (hd : S.graph.degree v ≤ 2) :
    ∃ S' : TreeSolution I, S'.vertices ⊆ S.vertices.erase v ∧ S'.cost ≤ S.cost := by
  classical
  obtain ⟨r, hr⟩ := hT
  have hvr : v ≠ (⟨r, S.contains hr⟩ : ↥S.vertices) := by
    intro h
    exact hv (by simpa only [h] using hr)
  have hp : 0 < S.graph.degree v :=
    (S.isTree.connected v ⟨r, S.contains hr⟩).degree_pos_left hvr
  obtain ⟨x, hx, hc⟩ := exists_collapse_cost_le I S.ambient v
    (by simpa only [S.degree_ambient] using hp) (by simpa only [S.degree_ambient] using hd)
  have hxU : x ∈ S.vertices := S.ambient_support_subset ⟨v, hx.symm⟩
  have hfixed : ∀ z ∈ I.terminals, collapse (v : V) x z = z := by
    intro z hz
    exact collapse_of_ne (fun h => hv (h ▸ hz))
  have hf := feasible_map_fixed I.terminals S.ambient S.ambient_feasible
    (collapse (v : V) x) hfixed
  have hTU : I.terminals ⊆ S.vertices.erase v := by
    intro z hz
    exact Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hz), S.contains hz⟩
  obtain ⟨S', hs, hcost⟩ := exists_tree_cost_le_subset I ⟨r, hr⟩ _ hf
    (S.vertices.erase v) hTU
    (collapse_support_subset S.ambient S.vertices S.ambient_support_subset v x hxU hx.ne.symm)
  refine ⟨S', hs, hcost.trans ?_⟩
  simpa only [S.cost_ambient] using hc

def IsClean (S : TreeSolution I) : Prop :=
  ∀ v : ↥S.vertices, (v : V) ∉ I.terminals → 3 ≤ S.graph.degree v

theorem cleanup [Fintype V] (S : TreeSolution I) (hT : I.terminals.Nonempty) :
    ∃ S' : TreeSolution I, S'.vertices ⊆ S.vertices ∧ S'.cost ≤ S.cost ∧ S'.IsClean := by
  classical
  have hex : ∃ n : ℕ, ∃ Q : TreeSolution I,
      Q.vertices ⊆ S.vertices ∧ Q.cost ≤ S.cost ∧ Q.vertices.card = n :=
    ⟨S.vertices.card, S, Finset.Subset.refl _, le_rfl, rfl⟩
  obtain ⟨Q, hsub, hcost, hcard⟩ := Nat.find_spec hex
  refine ⟨Q, hsub, hcost, ?_⟩
  intro v hv
  by_contra hd
  obtain ⟨R, hrsub, hrcost⟩ := Q.remove_nonterminal hT v hv (by omega)
  have hRsub : R.vertices ⊆ S.vertices :=
    (hrsub.trans (Finset.erase_subset _ _)).trans hsub
  have hmin := Nat.find_min' hex ⟨R, hRsub, hrcost.trans hcost, rfl⟩
  have hle := Finset.card_le_card hrsub
  have hlt := Finset.card_erase_lt_of_mem v.property
  omega

end TreeSolution

theorem clean_optimum_tree_attained [Fintype V] (I : Instance V)
    (hT : I.terminals.Nonempty) :
    ∃ S : TreeSolution I, S.cost = I.optimum ∧ S.IsClean := by
  obtain ⟨S, hS⟩ := optimum_tree_attained I hT
  obtain ⟨Q, _, hcost, hclean⟩ := S.cleanup hT
  exact ⟨Q, le_antisymm (hcost.trans_eq hS) Q.optimum_le_cost, hclean⟩

end SteinerUpperBound.TreeGeometry

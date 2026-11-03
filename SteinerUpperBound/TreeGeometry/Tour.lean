module

public import SteinerUpperBound.TreeGeometry.Basic

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open SteinerLowerBound
open scoped Classical BigOperators

universe u v

variable {V : Type u} {W : Type v}

noncomputable def routeCost (I : Instance V) (x : V) : List V → ℝ
  | [] => 0
  | y :: l => I.distance x y + routeCost I y l

def routeEnd (x : V) : List V → V
  | [] => x
  | y :: l => routeEnd y l

@[simp] theorem routeCost_nil (I : Instance V) (x : V) : routeCost I x [] = 0 := rfl

@[simp] theorem routeCost_cons (I : Instance V) (x y : V) (l : List V) :
    routeCost I x (y :: l) = I.distance x y + routeCost I y l := rfl

@[simp] theorem routeEnd_nil (x : V) : routeEnd x [] = x := rfl

@[simp] theorem routeEnd_cons (x y : V) (l : List V) :
    routeEnd x (y :: l) = routeEnd y l := rfl

theorem routeCost_append (I : Instance V) (x : V) (l m : List V) :
    routeCost I x (l ++ m) = routeCost I x l + routeCost I (routeEnd x l) m := by
  induction l generalizing x with
  | nil => simp
  | cons y l ih => simp [ih, add_assoc]

theorem routeEnd_append (x : V) (l m : List V) :
    routeEnd x (l ++ m) = routeEnd (routeEnd x l) m := by
  induction l generalizing x with
  | nil => rfl
  | cons y l ih => exact ih y

theorem routeCost_nonneg (I : Instance V) (x : V) (l : List V) :
    0 ≤ routeCost I x l := by
  induction l generalizing x with
  | nil => exact le_rfl
  | cons y l ih => exact add_nonneg (I.distance_nonneg x y) (ih y)

theorem distance_le_routeCost (I : Instance V) (x : V) (l : List V) :
    I.distance x (routeEnd x l) ≤ routeCost I x l := by
  induction l generalizing x with
  | nil => simp [I.distance_self]
  | cons y l ih =>
    apply (I.distance_triangle x y _).trans
    simpa only [routeEnd_cons, routeCost_cons] using
      add_le_add (le_refl (I.distance x y)) (ih y)

theorem insert_detour (I : Instance V) (x : V) (l : List V) (a b : V)
    (ha : a ∈ x :: l) :
    ∃ m : List V, routeEnd x m = routeEnd x l ∧
      (∀ z ∈ x :: l, z ∈ x :: m) ∧ b ∈ x :: m ∧
      routeCost I x m = routeCost I x l + 2 * I.distance a b := by
  induction l generalizing x with
  | nil =>
    have hax : a = x := by simpa only [List.mem_singleton] using ha
    subst a
    refine ⟨[b, x], rfl, ?_, by simp, ?_⟩
    · intro z hz
      have hzx : z = x := List.mem_singleton.mp hz
      simp [hzx]
    · simp [I.distance_comm b x, two_mul]
  | cons y l ih =>
    rcases List.mem_cons.mp ha with hax | ha
    · subst a
      refine ⟨b :: x :: y :: l, rfl, ?_, by simp, ?_⟩
      · intro z hz
        simp only [List.mem_cons] at hz ⊢
        tauto
      · simp only [routeCost_cons, I.distance_comm b x]
        ring
    · obtain ⟨m, hm, hsub, hb, hc⟩ := ih y ha
      refine ⟨y :: m, hm, ?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with h | h
        · exact List.mem_cons.mpr (Or.inl h)
        · exact List.mem_cons.mpr (Or.inr (hsub z h))
      · exact List.mem_cons.mpr (Or.inr hb)
      · simp only [routeCost_cons, hc]
        ring

theorem cost_delete_edge_add [Fintype W] (G : SimpleGraph W)
    (w : Sym2 W → ℝ) (e : Sym2 W) (he : e ∈ G.edgeSet) :
    GraphCost.cost w (G.deleteEdges {e}) + w e = GraphCost.cost w G := by
  classical
  let : DecidableRel (G.deleteEdges {e}).Adj := fun _ _ => Classical.propDecidable _
  unfold GraphCost.cost
  calc
    (∑ a ∈ (G.deleteEdges {e}).edgeFinset, w a) + w e =
        (∑ a ∈ G.edgeFinset.erase e, w a) + w e := by
      congr 1
      apply Finset.sum_congr
      · ext a
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
          Set.mem_sdiff, Set.mem_singleton_iff, Finset.mem_erase, and_comm, ne_eq]
      · intro a _
        rfl
    _ = _ := Finset.sum_erase_add _ _ (by simpa only [SimpleGraph.mem_edgeFinset] using he)

theorem leaf_induce_map [Fintype W] (G : SimpleGraph W) (a b : W)
    (_hab : G.Adj a b) (hn : ∀ z, G.Adj a z → z = b) :
    (G.induce ({a}ᶜ : Set W)).map Subtype.val = G.deleteEdges {s(a, b)} := by
  classical
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · intro h
    obtain ⟨_, x', y', hxy, rfl, rfl⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
    refine ⟨hxy, ?_⟩
    intro he
    have hx : (x' : W) ≠ a := x'.property
    have hy : (y' : W) ≠ a := y'.property
    rcases Sym2.eq_iff.mp he with ⟨h, _⟩ | ⟨_, h⟩
    · exact hx h
    · exact hy h
  · rintro ⟨hxy, he⟩
    have hx : x ≠ a := by
      intro hx
      subst x
      exact he (by rw [hn y hxy])
    have hy : y ≠ a := by
      intro hy
      subst y
      exact he (by rw [hn x hxy.symm, Sym2.eq_swap])
    exact (SimpleGraph.map_adj' _ _ _ _).mpr
      ⟨hxy.ne, ⟨x, hx⟩, ⟨y, hy⟩, hxy, rfl, rfl⟩

theorem cost_induce_leaf_add [Fintype W] (G : SimpleGraph W)
    (w : Sym2 W → ℝ) (a b : W) (hab : G.Adj a b)
    (hn : ∀ z, G.Adj a z → z = b) :
    GraphCost.cost (fun e => w (e.map Subtype.val)) (G.induce ({a}ᶜ : Set W)) +
      w s(a, b) = GraphCost.cost w G := by
  rw [← cost_map_eq _ _ Subtype.val_injective, leaf_induce_map G a b hab hn]
  exact cost_delete_edge_add G w s(a, b) hab

/-- Doubling is constructed by removing a leaf and inserting the two traversals of
its incident edge into the recursively constructed closed route. -/
theorem exists_tree_tour (I : Instance V) [Fintype W] (G : SimpleGraph W)
    (hG : G.IsTree) (f : W → V) (r : W) :
    ∃ l : List V, routeEnd (f r) l = f r ∧
      (∀ w : W, f w ∈ f r :: l) ∧
      routeCost I (f r) l ≤ 2 * GraphCost.cost (fun e => I.weight (e.map f)) G := by
  classical
  suffices hh : ∀ n : ℕ, ∀ (A : Type v) [Fintype A], Fintype.card A = n →
      ∀ (H : SimpleGraph A), H.IsTree → ∀ (g : A → V) (s : A),
      ∃ l : List V, routeEnd (g s) l = g s ∧
        (∀ w : A, g w ∈ g s :: l) ∧
        routeCost I (g s) l ≤ 2 * GraphCost.cost (fun e => I.weight (e.map g)) H by
    exact hh _ W rfl G hG f r
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A inst hcard H ht g s
    by_cases hsmall : Fintype.card A ≤ 1
    · have : Subsingleton A := Fintype.card_le_one_iff_subsingleton.mp hsmall
      refine ⟨[], rfl, ?_, ?_⟩
      · intro w
        simp [Subsingleton.elim w s]
      · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => I.weight_nonneg _)
    have : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨a, ha⟩ := ht.exists_vert_degree_one_of_nontrivial
    obtain ⟨b, hab, hn⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp ha
    let A' := ↥({a}ᶜ : Set A)
    let H' := H.induce ({a}ᶜ : Set A)
    have ht' : H'.IsTree :=
      ⟨ht.connected.induce_compl_singleton_of_degree_eq_one ha, ht.isAcyclic.induce _⟩
    have hlt : Fintype.card A' < n := by
      rw [← hcard]
      exact Fintype.card_subtype_lt (by simp : a ∉ ({a}ᶜ : Set A))
    have hsplit :
        GraphCost.cost (fun e => I.weight (e.map (fun x : A' => g x))) H' +
          I.distance (g a) (g b) =
        GraphCost.cost (fun e => I.weight (e.map g)) H := by
      simpa only [H', Sym2.map_map, Function.comp_def, Sym2.map_mk, Instance.weight_mk]
        using cost_induce_leaf_add H (fun e => I.weight (e.map g)) a b hab hn
    by_cases hsa : s = a
    · subst s
      obtain ⟨l, hl, hvisit, hcost⟩ := ih _ hlt A' rfl H' ht'
        (fun x => g x) ⟨b, hab.ne.symm⟩
      refine ⟨g b :: (l ++ [g a]), ?_, ?_, ?_⟩
      · simp only [routeEnd_cons, routeEnd_append, hl, routeEnd_nil]
      · intro w
        by_cases hwa : w = a
        · simp [hwa]
        · have hw := hvisit ⟨w, hwa⟩
          simp only [List.mem_cons, List.mem_append] at hw ⊢
          tauto
      · simp only [routeCost_cons, routeCost_append, hl, routeCost_nil, add_zero]
        rw [I.distance_comm (g b) (g a)]
        linarith
    · obtain ⟨l, hl, hvisit, hcost⟩ := ih _ hlt A' rfl H' ht'
        (fun x => g x) ⟨s, hsa⟩
      obtain ⟨m, hm, hsub, hma, hmcost⟩ := insert_detour I (g s) l (g b) (g a)
        (hvisit ⟨b, hab.ne.symm⟩)
      refine ⟨m, hm.trans hl, ?_, ?_⟩
      · intro w
        by_cases hwa : w = a
        · simpa only [hwa] using hma
        · exact hsub _ (hvisit ⟨w, hwa⟩)
      · rw [hmcost, I.distance_comm (g b) (g a)]
        linarith

end SteinerUpperBound.TreeGeometry

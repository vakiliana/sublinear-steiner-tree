module

public import SteinerUpperBound.SetSystem.Rank

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

noncomputable def incidenceGraph (ports : R → Finset U) : SimpleGraph (U ⊕ R) where
  Adj v w := match v, w with
    | Sum.inl x, Sum.inr r => x ∈ ports r
    | Sum.inr r, Sum.inl x => x ∈ ports r
    | _, _ => False
  symm := ⟨by intro v w; cases v <;> cases w <;> exact id⟩
  loopless := ⟨by intro v; cases v <;> exact id⟩

@[simp] theorem incidenceGraph_adj_left (ports : R → Finset U) (x y : U) :
    ¬(incidenceGraph ports).Adj (Sum.inl x) (Sum.inl y) := id

@[simp] theorem incidenceGraph_adj_right (ports : R → Finset U) (r s : R) :
    ¬(incidenceGraph ports).Adj (Sum.inr r) (Sum.inr s) := id

@[simp] theorem incidenceGraph_adj_inl_inr (ports : R → Finset U) (x : U) (r : R) :
    (incidenceGraph ports).Adj (Sum.inl x) (Sum.inr r) ↔ x ∈ ports r := Iff.rfl

@[simp] theorem incidenceGraph_adj_inr_inl (ports : R → Finset U) (x : U) (r : R) :
    (incidenceGraph ports).Adj (Sum.inr r) (Sum.inl x) ↔ x ∈ ports r := Iff.rfl

noncomputable def portGraph (ports : R → Finset U) : SimpleGraph U where
  Adj x y := x ≠ y ∧ ∃ r, x ∈ ports r ∧ y ∈ ports r
  symm := ⟨by rintro x y ⟨hxy, r, hx, hy⟩; exact ⟨hxy.symm, r, hy, hx⟩⟩
  loopless := ⟨by rintro x ⟨h, _⟩; exact h rfl⟩

theorem portGraph_reachable (ports : R → Finset U) (r : R)
    {x y : U} (hx : x ∈ ports r) (hy : y ∈ ports r) :
    (portGraph ports).Reachable x y := by
  by_cases he : x = y
  · subst y; exact SimpleGraph.Reachable.refl _
  · exact (show (portGraph ports).Adj x y from ⟨he, r, hx, hy⟩).reachable

theorem incidence_edges_card [Fintype R] [Fintype U] (ports : R → Finset U) :
    Nat.card (incidenceGraph ports).edgeSet = ∑ r, (ports r).card := by
  classical
  let f : (Σ r, ↥(ports r)) → (incidenceGraph ports).edgeSet :=
    fun p => ⟨Sym2.mk (Sum.inl p.2.val) (Sum.inr p.1),
      (SimpleGraph.mem_edgeSet _).mpr p.2.property⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨r, x⟩ ⟨s, y⟩ h
      have he := congrArg Subtype.val h
      change Sym2.mk (Sum.inl x.val) (Sum.inr r) =
        Sym2.mk (Sum.inl y.val) (Sum.inr s) at he
      simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
        Sum.inl_ne_inr, Sum.inr_ne_inl, false_and, or_false] at he
      obtain ⟨hxy, rfl⟩ := he
      exact congrArg (Sigma.mk r) (Subtype.ext hxy)
    · rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ v w =>
          cases v with
          | inl x =>
              cases w with
              | inl y => exact (incidenceGraph_adj_left ports x y
                  ((SimpleGraph.mem_edgeSet _).mp he)).elim
              | inr r =>
                  exact ⟨⟨r, ⟨x, (SimpleGraph.mem_edgeSet _).mp he⟩⟩, rfl⟩
          | inr r =>
              cases w with
              | inl x =>
                  refine ⟨⟨r, ⟨x, (SimpleGraph.mem_edgeSet _).mp he⟩⟩, ?_⟩
                  apply Subtype.ext
                  exact Sym2.eq_swap
              | inr s => exact (incidenceGraph_adj_right ports r s
                  ((SimpleGraph.mem_edgeSet _).mp he)).elim
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp only [Fintype.card_coe]

theorem incidence_row_degree [Fintype R] [Fintype U] (ports : R → Finset U) (r : R) :
    (incidenceGraph ports).degree (Sum.inr r) = (ports r).card := by
  classical
  have he : (incidenceGraph ports).neighborFinset (Sum.inr r) =
      (ports r).image Sum.inl := by
    ext v
    cases v <;> simp
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he,
    Finset.card_image_of_injective _ Sum.inl_injective]

theorem portGraph_incidence_reachable (ports : R → Finset U) {x y : U}
    (h : (portGraph ports).Reachable x y) :
    (incidenceGraph ports).Reachable (Sum.inl x) (Sum.inl y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hxy p ih =>
      obtain ⟨_, r, hxr, hyr⟩ := hxy
      have hx : (incidenceGraph ports).Adj (Sum.inl x) (Sum.inr r) := hxr
      have hy : (incidenceGraph ports).Adj (Sum.inr r) (Sum.inl y) := hyr
      exact hx.reachable.trans (hy.reachable.trans ih)

noncomputable def incidenceRoot (ports : R → Finset U)
    (hne : ∀ r, (ports r).Nonempty) : U ⊕ R → U
  | Sum.inl x => x
  | Sum.inr r => (hne r).choose

theorem incidence_root_reachable (ports : R → Finset U)
    (hne : ∀ r, (ports r).Nonempty) (v : U ⊕ R) :
    (incidenceGraph ports).Reachable v (Sum.inl (incidenceRoot ports hne v)) := by
  cases v with
  | inl x => exact SimpleGraph.Reachable.refl _
  | inr r =>
      exact (show (incidenceGraph ports).Adj (Sum.inr r)
        (Sum.inl ((hne r).choose)) from (hne r).choose_spec).reachable

theorem incidence_root_iff (ports : R → Finset U)
    (hne : ∀ r, (ports r).Nonempty) (v w : U ⊕ R) :
    (incidenceGraph ports).Reachable v w ↔
      (portGraph ports).Reachable (incidenceRoot ports hne v) (incidenceRoot ports hne w) := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
        have hab' : (portGraph ports).Reachable (incidenceRoot ports hne a)
            (incidenceRoot ports hne b) := by
          cases a with
          | inl x =>
              cases b with
              | inl y => exact hab.elim
              | inr r => exact portGraph_reachable ports r hab (hne r).choose_spec
          | inr r =>
              cases b with
              | inl x => exact portGraph_reachable ports r (hne r).choose_spec hab
              | inr s => exact hab.elim
        exact hab'.trans ih
  · intro h
    exact (incidence_root_reachable ports hne v).trans
      ((portGraph_incidence_reachable ports h).trans
        (incidence_root_reachable ports hne w).symm)

theorem incidence_forest_port_rank [Fintype R] [Fintype U]
    (ports : R → Finset U) (hne : ∀ r, (ports r).Nonempty)
    (hforest : (incidenceGraph ports).IsAcyclic) :
    GraphRank.rank (portGraph ports) + Nat.card R = ∑ r, (ports r).card := by
  have he := Nat.card_congr (componentEquiv (incidenceGraph ports) (portGraph ports)
    (incidenceRoot ports hne) (fun x => ⟨Sum.inl x, rfl⟩) (incidence_root_iff ports hne))
  have hi := GraphRank.rank_add_components (incidenceGraph ports)
  have hp := GraphRank.rank_add_components (portGraph ports)
  rw [forest_rank _ hforest, incidence_edges_card] at hi
  have hc : Nat.card (U ⊕ R) = Nat.card U + Nat.card R := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum]
  omega

theorem incidence_forest_port_rank_sub [Fintype R] [Fintype U]
    (ports : R → Finset U) (hne : ∀ r, (ports r).Nonempty)
    (hforest : (incidenceGraph ports).IsAcyclic) :
    GraphRank.rank (portGraph ports) = (∑ r, (ports r).card) - Nat.card R := by
  have h := incidence_forest_port_rank ports hne hforest
  omega

theorem incidence_reindex_acyclic {S : Type*} (ports : R → Finset U)
    (f : S → R) (hf : Function.Injective f)
    (hforest : (incidenceGraph ports).IsAcyclic) :
    (incidenceGraph (fun s => ports (f s))).IsAcyclic := by
  let hom : incidenceGraph (fun s => ports (f s)) →g incidenceGraph ports :=
    ⟨Sum.map id f, by intro a b h; cases a <;> cases b <;> exact h⟩
  have hinj : Function.Injective hom := by
    intro a b h
    cases a <;> cases b <;> simp_all [hom, hf.eq_iff]
  exact SimpleGraph.IsAcyclic.comap hom hinj hforest

end SteinerUpperBound.SetSystem

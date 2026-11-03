module

public import SteinerUpperBound.SetSystem.PortSaving

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

open scoped Classical BigOperators

variable {R U : Type*}

noncomputable def portGraphList : List (R × Finset U) → SimpleGraph U
  | [] => ⊥
  | e :: l => Network.completeOn e.2 ⊔ portGraphList l

@[simp]
theorem portGraphList_nil : portGraphList ([] : List (R × Finset U)) = ⊥ := rfl

@[simp]
theorem portGraphList_cons (e : R × Finset U) (l : List (R × Finset U)) :
    portGraphList (e :: l) = Network.completeOn e.2 ⊔ portGraphList l := rfl

theorem portGraphList_adj (l : List (R × Finset U)) (x y : U) :
    (portGraphList l).Adj x y ↔
      x ≠ y ∧ ∃ e ∈ l, x ∈ e.2 ∧ y ∈ e.2 := by
  induction l with
  | nil => simp [portGraphList]
  | cons e l ih =>
      simp only [portGraphList_cons, SimpleGraph.sup_adj, Network.completeOn_adj, ih,
        List.mem_cons]
      aesop

theorem portGraphList_eq_portGraph (l : List (R × Finset U)) :
    portGraphList l = SetSystem.portGraph (fun j : Fin l.length => (l.get j).2) := by
  ext x y
  rw [portGraphList_adj]
  constructor
  · rintro ⟨hne, e, he, hx, hy⟩
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp he
    exact ⟨hne, j, hx, hy⟩
  · rintro ⟨hne, j, hx, hy⟩
    exact ⟨hne, l.get j, l.get_mem j, hx, hy⟩

/-- Positions, not center IDs, are counted; repeated centers are allowed. -/
theorem port_rank_saving_list [Fintype U] (E : Finset R) (rows : R → Finset U)
    (A : Finset U) (l : List (R × Finset U))
    (h : ∀ e ∈ l, e.1 ∈ E ∧ e.2 ⊆ A ∩ rows e.1) :
    (GraphRank.rank (portGraphList l) : ℝ) - l.length ≤ Structural.saving E rows A := by
  have hh := SetSystem.port_rank_saving E rows A
    (fun j : Fin l.length => (l.get j).1) (fun j : Fin l.length => (l.get j).2)
    (fun j => (h (l.get j) (l.get_mem j)).1)
    (fun j => (h (l.get j) (l.get_mem j)).2)
  rw [← portGraphList_eq_portGraph l] at hh
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hh

end SteinerUpperBound.SavingSoundness

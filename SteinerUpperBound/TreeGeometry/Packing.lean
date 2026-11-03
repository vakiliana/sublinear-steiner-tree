module

public import SteinerUpperBound.TreeGeometry.Shortcut

@[expose] public section

namespace SteinerUpperBound.TreeGeometry

open scoped Classical BigOperators

variable {V : Type*}

theorem separated_route_card (I : Instance V) (P : Finset V) (r : ℝ)
    (hsep : (P : Set V).Pairwise (fun x y => r ≤ I.distance x y))
    (x : V) (l : List V) (hP : ∀ z ∈ x :: l, z ∈ P) :
    (((x :: l).toFinset.card : ℝ) - 1) * r ≤ routeCost I x l := by
  classical
  induction l generalizing x with
  | nil => simp
  | cons y l ih =>
    have htail : ∀ z ∈ y :: l, z ∈ P :=
      fun z hz => hP z (List.mem_cons_of_mem _ hz)
    have hi := ih y htail
    by_cases hx : x ∈ (y :: l).toFinset
    · have he : (x :: y :: l).toFinset = (y :: l).toFinset := by
        rw [List.toFinset_cons]
        exact Finset.insert_eq_of_mem hx
      rw [he, routeCost_cons]
      linarith [I.distance_nonneg x y]
    · have hxy : x ≠ y := by
        intro he
        exact hx (by simp [he])
      have hd : r ≤ I.distance x y :=
        hsep (hP x (by simp)) (hP y (by simp)) hxy
      have hc : (x :: y :: l).toFinset.card = (y :: l).toFinset.card + 1 := by
        rw [List.toFinset_cons, Finset.card_insert_of_notMem hx]
      rw [hc, Nat.cast_add, Nat.cast_one, routeCost_cons]
      linarith

theorem separated_terminal_packing [Fintype V] (I : Instance V)
    (P : Finset V) (hPT : P ⊆ I.terminals) (r : ℝ) (hr : 0 < r)
    (hsep : (P : Set V).Pairwise (fun x y => r ≤ I.distance x y)) :
    (P.card : ℝ) ≤ 1 + 2 * I.mst / r := by
  classical
  by_cases hP : P.Nonempty
  · obtain ⟨x, hx⟩ := hP
    obtain ⟨l, _, _, hcover, hcost⟩ := terminal_tour_mst I x (hPT hx)
    let m := l.filter (fun z => z ∈ P)
    have hm : ∀ z ∈ x :: m, z ∈ P := by
      intro z hz
      rcases List.mem_cons.mp hz with h | h
      · simpa only [h] using hx
      · exact of_decide_eq_true (List.mem_filter.mp h).2
    have hcov : ∀ z ∈ P, z ∈ x :: m := by
      intro z hz
      rcases List.mem_cons.mp (hcover z (hPT hz)) with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨h, decide_eq_true hz⟩))
    have he : (x :: m).toFinset = P := by
      ext z
      simp only [List.mem_toFinset]
      exact ⟨hm z, hcov z⟩
    have hc := separated_route_card I P r hsep x m hm
    rw [he] at hc
    have hlength : routeCost I x m ≤ 2 * I.mst :=
      (routeCost_sublist I x List.filter_sublist).trans hcost
    have hdiv : (P.card : ℝ) - 1 ≤ 2 * I.mst / r :=
      (le_div_iff₀ hr).mpr (hc.trans hlength)
    linarith
  · have he := Finset.not_nonempty_iff_eq_empty.mp hP
    rw [he, Finset.card_empty, Nat.cast_zero]
    positivity [I.mst_nonneg]

theorem separated_terminal_packing_lt [Fintype V] (I : Instance V)
    (P : Finset V) (hPT : P ⊆ I.terminals) (r : ℝ) (hr : 0 < r)
    (hsep : (P : Set V).Pairwise (fun x y => r < I.distance x y)) :
    (P.card : ℝ) ≤ 1 + 2 * I.mst / r := by
  apply separated_terminal_packing I P hPT r hr
  intro x hx y hy hxy
  exact (hsep hx hy hxy).le

end SteinerUpperBound.TreeGeometry

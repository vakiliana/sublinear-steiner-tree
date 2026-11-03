module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Structural.Rooted

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (r : V)

noncomputable def children (v : V) : Finset V :=
  Finset.univ.filter (fun w => G.Adj v w ∧ G.dist r w = G.dist r v + 1)

theorem mem_children (v w : V) :
    w ∈ children G r v ↔ G.Adj v w ∧ G.dist r w = G.dist r v + 1 := by
  classical
  simp only [children, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def maxDepth : ℕ := Finset.univ.sup (G.dist r)

theorem depth_le (v : V) : G.dist r v ≤ maxDepth G r :=
  Finset.le_sup (Finset.mem_univ v)

theorem exists_lower_neighbor (ht : G.IsTree) {v : V} (hv : v ≠ r) :
    ∃ w, G.Adj v w ∧ G.dist r w + 1 = G.dist r v := by
  obtain ⟨q, hq⟩ := ht.connected.exists_walk_length_eq_dist v r
  cases q with
  | nil => exact False.elim (hv rfl)
  | @cons v w r h p =>
    refine ⟨w, h, ?_⟩
    have hp := G.dist_le p
    rw [G.dist_comm (u := w) (v := r)] at hp
    have hs := ht.dist_eq_dist_add_one_of_adj r h
    rw [G.dist_comm (u := v) (v := r)] at hq
    simp only [SimpleGraph.Walk.length_cons] at hq
    omega

theorem lower_neighbor_unique (ht : G.IsTree) {v x y : V}
    (hx : G.Adj v x) (hy : G.Adj v y)
    (hdx : G.dist r x + 1 = G.dist r v)
    (hdy : G.dist r y + 1 = G.dist r v) : x = y := by
  obtain ⟨px, hpx⟩ := ht.connected.exists_walk_length_eq_dist r x
  obtain ⟨py, hpy⟩ := ht.connected.exists_walk_length_eq_dist r y
  have hpx' : (px.concat hx.symm).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    simpa only [SimpleGraph.Walk.length_concat, hpx] using hdx
  have hpy' : (py.concat hy.symm).IsPath := by
    apply SimpleGraph.Walk.isPath_of_length_eq_dist
    simpa only [SimpleGraph.Walk.length_concat, hpy] using hdy
  have he := ht.isAcyclic.path_unique ⟨px.concat hx.symm, hpx'⟩ ⟨py.concat hy.symm, hpy'⟩
  have hw : px.concat hx.symm = py.concat hy.symm := congrArg Subtype.val he
  simpa only [SimpleGraph.Walk.penultimate_concat] using
    congrArg SimpleGraph.Walk.penultimate hw

theorem degree_eq_children_add_one (ht : G.IsTree) {v : V} (hv : v ≠ r) :
    G.degree v = (children G r v).card + 1 := by
  classical
  obtain ⟨w, hw, hd⟩ := exists_lower_neighbor G r ht hv
  have he : G.neighborFinset v = insert w (children G r v) := by
    ext z
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, mem_children]
    constructor
    · intro hz
      rcases ht.dist_eq_dist_add_one_of_adj r hz with h | h
      · exact Or.inl (lower_neighbor_unique G r ht hz hw h.symm hd)
      · exact Or.inr ⟨hz, h⟩
    · rintro (rfl | ⟨h, _⟩)
      · exact hw
      · exact h
  have hwc : w ∉ children G r v := by
    intro h
    have hh := (mem_children G r v w).mp h
    omega
  rw [← SimpleGraph.card_neighborFinset_eq_degree, he, Finset.card_insert_of_notMem hwc]

noncomputable def heightAux (T : Finset V) : ℕ → V → ℕ
  | 0, _ => 0
  | n + 1, v => (if v ∈ T then 0 else 1) + (children G r v).sup (heightAux T n)

noncomputable def height (T : Finset V) (v : V) : ℕ :=
  heightAux G r T (maxDepth G r + 1 - G.dist r v) v

theorem height_eq (T : Finset V) (v : V) :
    height G r T v = (if v ∈ T then 0 else 1) + (children G r v).sup (height G r T) := by
  classical
  have hd := depth_le G r v
  obtain ⟨n, hn⟩ : ∃ n, maxDepth G r + 1 - G.dist r v = n + 1 :=
    ⟨maxDepth G r - G.dist r v, by omega⟩
  unfold height
  rw [hn, heightAux]
  congr 1
  apply Finset.sup_congr rfl
  intro w hw
  have hc := (mem_children G r v w).mp hw
  have he : n = maxDepth G r + 1 - G.dist r w := by omega
  rw [he]

theorem nonterminal_height_pos (T : Finset V) {v : V} (hv : v ∉ T) :
    0 < height G r T v := by
  classical
  rw [height_eq G r T v]
  simp only [hv, ↓reduceIte]
  omega

theorem child_height_le (T : Finset V) {v w : V} (hw : w ∈ children G r v) :
    height G r T w ≤ height G r T v := by
  have hs : height G r T w ≤ (children G r v).sup (height G r T) := Finset.le_sup hw
  rw [height_eq G r T v]
  omega

theorem child_height_lt (T : Finset V) {v w : V} (hv : v ∉ T)
    (hw : w ∈ children G r v) : height G r T w < height G r T v := by
  classical
  have hs : height G r T w ≤ (children G r v).sup (height G r T) := Finset.le_sup hw
  rw [height_eq G r T v]
  simp only [hv, ↓reduceIte]
  omega

theorem terminal_height_zero_of_children (T : Finset V) {v : V} (hv : v ∈ T)
    (hc : ∀ w ∈ children G r v, height G r T w = 0) : height G r T v = 0 := by
  classical
  rw [height_eq]
  simp only [hv, ↓reduceIte, zero_add]
  apply Nat.le_zero.mp
  exact Finset.sup_le (fun w hw => Nat.le_zero.mpr (hc w hw))

theorem positive_child_height (T : Finset V) {v : V} (n : ℕ) (hn : 0 < n)
    (h : n ≤ (children G r v).sup (height G r T)) :
    ∃ w ∈ children G r v, n ≤ height G r T w := by
  classical
  by_contra hh
  push_neg at hh
  have he : (children G r v).sup (height G r T) ≤ n - 1 :=
    Finset.sup_le (fun w hw => by have := hh w hw; omega)
  omega

theorem no_small_terminal_height (T : Finset V) (n : ℕ) (hn : 0 < n)
    (hboundary : ∀ v w, w ∈ children G r v → v ∈ T → w ∉ T →
      height G r T w ≠ n) :
    ∀ v ∈ T, height G r T v ≠ n := by
  classical
  intro v hv
  have hmain : ∀ d : ℕ, ∀ v ∈ T, maxDepth G r + 1 - G.dist r v = d →
      height G r T v ≠ n := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hv hd he
      have hsup : n ≤ (children G r v).sup (height G r T) := by
        have heq := height_eq G r T v
        simp only [hv, ↓reduceIte, zero_add] at heq
        omega
      obtain ⟨w, hw, hnw⟩ := positive_child_height G r T n hn hsup
      have hle := child_height_le G r T hw
      have hew : height G r T w = n := by omega
      by_cases hwT : w ∈ T
      · have hc := (mem_children G r v w).mp hw
        have hdepth := depth_le G r v
        have hwd : maxDepth G r + 1 - G.dist r w < d := by omega
        exact ih _ hwd w hwT rfl hew
      · exact hboundary v w hw hv hwT hew
  exact hmain _ v hv rfl

end SteinerUpperBound.Structural.Rooted

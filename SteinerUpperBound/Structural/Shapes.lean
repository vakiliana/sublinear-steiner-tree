module

public import SteinerUpperBound.Structural.Rooted

@[expose] public section

namespace SteinerUpperBound.Structural.Rooted

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V) (r : V) (T : Finset V)

noncomputable def terminalNeighbors (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun w => w ∈ T)

noncomputable def limbNeighbors (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun w => w ∈ T ∨
    (w ∉ T ∧ G.degree w = 3 ∧ (terminalNeighbors G T w).card = 2))

def NoZeroCoreStar : Prop :=
  ∀ v ∉ T, (limbNeighbors G T v).card ≤ 2

def Clean : Prop := ∀ v ∉ T, 3 ≤ G.degree v

theorem mem_limbNeighbors (v w : V) :
    w ∈ limbNeighbors G T v ↔ G.Adj v w ∧
      (w ∈ T ∨ (w ∉ T ∧ G.degree w = 3 ∧ (terminalNeighbors G T w).card = 2)) := by
  classical
  simp only [limbNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]

theorem two_children (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    {v : V} (hv : v ∉ T) : 2 ≤ (children G r v).card := by
  have hvr : v ≠ r := fun h => hv (h ▸ hr)
  have hd := degree_eq_children_add_one G r ht hvr
  have hh := hc v hv
  omega

theorem parent_not_child {v w : V} (hd : G.dist r w + 1 = G.dist r v) :
    w ∉ children G r v := by
  intro hw
  have hh := (mem_children G r v w).mp hw
  omega

theorem terminal_parent_gives_three (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    {v w : V} (hv : v ∉ T) (hw : w ∈ T) (hvw : G.Adj v w)
    (hd : G.dist r w + 1 = G.dist r v)
    (hch : children G r v ⊆ limbNeighbors G T v) :
    3 ≤ (limbNeighbors G T v).card := by
  classical
  have hs : insert w (children G r v) ⊆ limbNeighbors G T v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hz
    · simpa only [he] using (mem_limbNeighbors G T v w).mpr ⟨hvw, Or.inl hw⟩
    · exact hch hz
  have hcard := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem (parent_not_child G r hd)] at hcard
  have h2 := two_children G r T ht hr hc hv
  omega

theorem height_one_children_terminal {v : V} (hv : v ∉ T) (hh : height G r T v = 1) :
    ∀ w ∈ children G r v, w ∈ T := by
  intro w hw
  by_contra hwT
  have hlt := child_height_lt G r T hv hw
  have hp := nonterminal_height_pos G r T hwT
  omega

theorem height_one_parent_nonterminal (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v w : V}
    (hv : v ∉ T) (hh : height G r T v = 1)
    (hvw : G.Adj v w) (hd : G.dist r w + 1 = G.dist r v) :
    w ∉ T := by
  intro hw
  have hch : children G r v ⊆ limbNeighbors G T v := by
    intro z hz
    exact (mem_limbNeighbors G T v z).mpr
      ⟨((mem_children G r v z).mp hz).1,
        Or.inl (height_one_children_terminal G r T hv hh z hz)⟩
  have h3 := terminal_parent_gives_three G r T ht hr hc hv hw hvw hd hch
  have h2 := hstar v hv
  omega

theorem height_one_cherry (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v : V}
    (hv : v ∉ T) (hh : height G r T v = 1) :
    G.degree v = 3 ∧ (children G r v).card = 2 ∧
      terminalNeighbors G T v = children G r v := by
  classical
  have hchildren := height_one_children_terminal G r T hv hh
  have hch : children G r v ⊆ limbNeighbors G T v := by
    intro z hz
    exact (mem_limbNeighbors G T v z).mpr
      ⟨((mem_children G r v z).mp hz).1, Or.inl (hchildren z hz)⟩
  have hle := (Finset.card_le_card hch).trans (hstar v hv)
  have hge := two_children G r T ht hr hc hv
  have hcard : (children G r v).card = 2 := by omega
  have hvr : v ≠ r := fun h => hv (h ▸ hr)
  have hd := degree_eq_children_add_one G r ht hvr
  refine ⟨by omega, hcard, ?_⟩
  ext z
  simp only [terminalNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hz, hzT⟩
    rcases ht.dist_eq_dist_add_one_of_adj r hz with h | h
    · exact False.elim ((height_one_parent_nonterminal G r T ht hr hc hstar hv hh hz h.symm) hzT)
    · exact (mem_children G r v z).mpr ⟨hz, h⟩
  · intro hz
    exact ⟨((mem_children G r v z).mp hz).1, hchildren z hz⟩

theorem no_terminal_height_one (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) :
    ∀ v ∈ T, height G r T v ≠ 1 := by
  apply no_small_terminal_height G r T 1 (by omega)
  intro v w hw hv hwT hh
  have ha := (mem_children G r v w).mp hw
  exact height_one_parent_nonterminal G r T ht hr hc hstar hwT hh ha.1.symm
    (by omega) hv

theorem height_two_children_limbs (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v : V}
    (hv : v ∉ T) (hh : height G r T v = 2) :
    children G r v ⊆ limbNeighbors G T v := by
  intro w hw
  have hadj := ((mem_children G r v w).mp hw).1
  apply (mem_limbNeighbors G T v w).mpr
  refine ⟨hadj, ?_⟩
  by_cases hwT : w ∈ T
  · exact Or.inl hwT
  · have hlt := child_height_lt G r T hv hw
    have hp := nonterminal_height_pos G r T hwT
    have h1 : height G r T w = 1 := by omega
    obtain ⟨hd, hcard, he⟩ := height_one_cherry G r T ht hr hc hstar hwT h1
    exact Or.inr ⟨hwT, hd, by rw [he, hcard]⟩

theorem height_two_parent_nonterminal (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v w : V}
    (hv : v ∉ T) (hh : height G r T v = 2)
    (hvw : G.Adj v w) (hd : G.dist r w + 1 = G.dist r v) :
    w ∉ T := by
  intro hw
  have h3 := terminal_parent_gives_three G r T ht hr hc hv hw hvw hd
    (height_two_children_limbs G r T ht hr hc hstar hv hh)
  have h2 := hstar v hv
  omega

theorem no_terminal_height_two (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) :
    ∀ v ∈ T, height G r T v ≠ 2 := by
  apply no_small_terminal_height G r T 2 (by omega)
  intro v w hw hv hwT hh
  have ha := (mem_children G r v w).mp hw
  exact height_two_parent_nonterminal G r T ht hr hc hstar hwT hh ha.1.symm
    (by omega) hv

theorem height_two_fan (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) {v : V}
    (hv : v ∉ T) (hh : height G r T v = 2) :
    G.degree v = 3 ∧ (children G r v).card = 2 ∧
      children G r v ⊆ limbNeighbors G T v ∧
      ∃ w ∈ children G r v, w ∉ T ∧ height G r T w = 1 := by
  classical
  have hch := height_two_children_limbs G r T ht hr hc hstar hv hh
  have hle := (Finset.card_le_card hch).trans (hstar v hv)
  have hge := two_children G r T ht hr hc hv
  have hcard : (children G r v).card = 2 := by omega
  have hvr : v ≠ r := fun h => hv (h ▸ hr)
  have hd := degree_eq_children_add_one G r ht hvr
  refine ⟨by omega, hcard, hch, ?_⟩
  have hs : 1 ≤ (children G r v).sup (height G r T) := by
    have he := height_eq G r T v
    simp only [hv, ↓reduceIte] at he
    omega
  obtain ⟨w, hw, h1⟩ := positive_child_height G r T 1 (by omega) hs
  have hlt := child_height_lt G r T hv hw
  have hew : height G r T w = 1 := by omega
  have hwT : w ∉ T := fun h => no_terminal_height_one G r T ht hr hc hstar w h hew
  exact ⟨w, hw, hwT, hew⟩

theorem height_le_root (ht : G.IsTree) (v : V) : height G r T v ≤ height G r T r := by
  have hmain : ∀ n : ℕ, ∀ v, G.dist r v = n → height G r T v ≤ height G r T r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hd
      by_cases hvr : v = r
      · subst v
        exact le_rfl
      · obtain ⟨w, hw, hwd⟩ := exists_lower_neighbor G r ht hvr
        have hchild : v ∈ children G r w :=
          (mem_children G r w v).mpr ⟨hw.symm, hwd.symm⟩
        exact (child_height_le G r T hchild).trans
          (ih _ (by omega) w rfl)
  exact hmain _ v rfl

theorem exists_height_three (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) (hne : ∃ v, v ∉ T) :
    ∃ v, v ∉ T ∧ height G r T v = 3 := by
  classical
  obtain ⟨v, hv⟩ := hne
  have hp := nonterminal_height_pos G r T hv
  have hle := height_le_root G r T ht v
  have hn1 := no_terminal_height_one G r T ht hr hc hstar r hr
  have hn2 := no_terminal_height_two G r T ht hr hc hstar r hr
  have hr3 : 3 ≤ height G r T r := by omega
  have hmain : ∀ d : ℕ, ∀ v, maxDepth G r + 1 - G.dist r v = d →
      3 ≤ height G r T v → ∃ w, w ∉ T ∧ height G r T w = 3 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro v hd hv3
      by_cases hvT : v ∈ T
      · have hs : 3 ≤ (children G r v).sup (height G r T) := by
          have he := height_eq G r T v
          simp only [hvT, ↓reduceIte, zero_add] at he
          omega
        obtain ⟨w, hw, hw3⟩ := positive_child_height G r T 3 (by omega) hs
        have hc := (mem_children G r v w).mp hw
        have hdepth := depth_le G r v
        exact ih _ (by omega) w rfl hw3
      · by_cases he : height G r T v = 3
        · exact ⟨v, hvT, he⟩
        · have hs : 3 ≤ (children G r v).sup (height G r T) := by
            have heq := height_eq G r T v
            simp only [hvT, ↓reduceIte] at heq
            omega
          obtain ⟨w, hw, hw3⟩ := positive_child_height G r T 3 (by omega) hs
          have hc := (mem_children G r v w).mp hw
          have hdepth := depth_le G r v
          exact ih _ (by omega) w rfl hw3
  exact hmain _ r rfl hr3

theorem height_three_fork (ht : G.IsTree) (hr : r ∈ T) (hc : Clean G T)
    (hstar : NoZeroCoreStar G T) (hne : ∃ v, v ∉ T) :
    ∃ v w z, v ∉ T ∧ w ∈ children G r v ∧ z ∈ children G r v ∧ w ≠ z ∧
      w ∉ T ∧ height G r T w = 2 ∧
      (z ∈ limbNeighbors G T v ∨ (z ∉ T ∧ height G r T z = 2)) := by
  classical
  obtain ⟨v, hvT, hv3⟩ := exists_height_three G r T ht hr hc hstar hne
  have hs : 2 ≤ (children G r v).sup (height G r T) := by
    have he := height_eq G r T v
    simp only [hvT, ↓reduceIte] at he
    omega
  obtain ⟨w, hw, hw2⟩ := positive_child_height G r T 2 (by omega) hs
  have hwlt := child_height_lt G r T hvT hw
  have hew : height G r T w = 2 := by omega
  have hwT : w ∉ T := fun h => no_terminal_height_two G r T ht hr hc hstar w h hew
  have hcard := two_children G r T ht hr hc hvT
  have hnonempty : ((children G r v).erase w).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hw]
    omega
  obtain ⟨z, hz⟩ := hnonempty
  obtain ⟨hzw, hz⟩ := Finset.mem_erase.mp hz
  refine ⟨v, w, z, hvT, hw, hz, hzw.symm, hwT, hew, ?_⟩
  have hzlt := child_height_lt G r T hvT hz
  by_cases hzT : z ∈ T
  · exact Or.inl ((mem_limbNeighbors G T v z).mpr
      ⟨((mem_children G r v z).mp hz).1, Or.inl hzT⟩)
  · have hzpos := nonterminal_height_pos G r T hzT
    by_cases hz1 : height G r T z = 1
    · obtain ⟨hd, hcard, he⟩ := height_one_cherry G r T ht hr hc hstar hzT hz1
      exact Or.inl ((mem_limbNeighbors G T v z).mpr
        ⟨((mem_children G r v z).mp hz).1, Or.inr ⟨hzT, hd, by rw [he, hcard]⟩⟩)
    · exact Or.inr ⟨hzT, by omega⟩

end SteinerUpperBound.Structural.Rooted

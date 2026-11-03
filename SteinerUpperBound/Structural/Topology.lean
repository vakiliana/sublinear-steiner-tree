module

public import SteinerUpperBound.Structural.FanElimination
public import SteinerUpperBound.Structural.Stars
public import SteinerUpperBound.Structural.Shapes

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

noncomputable def selectedTerminals (S : TreeGeometry.TreeSolution I) : Finset ↥S.vertices :=
  Finset.univ.filter (fun x => (x : V) ∈ I.terminals)

theorem mem_selectedTerminals (S : TreeGeometry.TreeSolution I) (x : ↥S.vertices) :
    x ∈ selectedTerminals S ↔ (x : V) ∈ I.terminals := by
  classical
  simp only [selectedTerminals, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rooted_clean (S : TreeGeometry.TreeSolution I) (hc : S.IsClean) :
    Rooted.Clean S.graph (selectedTerminals S) := by
  intro v hv
  exact hc v (fun h => hv ((mem_selectedTerminals S v).mpr h))

theorem limb_of_neighbor (S : TreeGeometry.TreeSolution I) (v w : ↥S.vertices)
    (hv : (v : V) ∉ I.terminals)
    (hw : w ∈ Rooted.limbNeighbors S.graph (selectedTerminals S) v) :
    ∃ L : Limb S v, L.stem = w := by
  classical
  obtain ⟨hvw, hwT | ⟨hwT, hdeg, hports⟩⟩ :=
    (Rooted.mem_limbNeighbors S.graph (selectedTerminals S) v w).mp hw
  · exact ⟨Limb.direct w hv ((mem_selectedTerminals S w).mp hwT) hvw, rfl⟩
  · obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hports
    have hxmem : x ∈ Rooted.terminalNeighbors S.graph (selectedTerminals S) w := by rw [hset]; simp
    have hymem : y ∈ Rooted.terminalNeighbors S.graph (selectedTerminals S) w := by rw [hset]; simp
    obtain ⟨hwx, hxT⟩ : S.graph.Adj w x ∧ (x : V) ∈ I.terminals := by
      simpa only [Rooted.terminalNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        mem_selectedTerminals] using hxmem
    obtain ⟨hwy, hyT⟩ : S.graph.Adj w y ∧ (y : V) ∈ I.terminals := by
      simpa only [Rooted.terminalNeighbors, Finset.mem_filter, SimpleGraph.mem_neighborFinset,
        mem_selectedTerminals] using hymem
    have hnvx : v ≠ x := fun h => hv (h ▸ hxT)
    have hnvy : v ≠ y := fun h => hv (h ▸ hyT)
    have hs : ({v, x, y} : Finset ↥S.vertices) ⊆ S.graph.neighborFinset w := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · simpa only [SimpleGraph.mem_neighborFinset] using hvw.symm
      · simpa only [SimpleGraph.mem_neighborFinset] using hwx
      · simpa only [SimpleGraph.mem_neighborFinset] using hwy
    have hc : ({v, x, y} : Finset ↥S.vertices).card = 3 := by simp [hnvx, hnvy, hxy]
    have he := Finset.eq_of_subset_of_card_le hs (by
      rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg, hc])
    have hn (z : ↥S.vertices) (hz : S.graph.Adj w z) : z = v ∨ z = x ∨ z = y := by
      have hm : z ∈ ({v, x, y} : Finset ↥S.vertices) := by
        rw [he]
        simpa only [SimpleGraph.mem_neighborFinset] using hz
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hwNT : (w : V) ∉ I.terminals :=
      fun h => hwT ((mem_selectedTerminals S w).mpr h)
    by_cases horder : I.distance w x ≤ I.distance w y
    · exact ⟨Limb.cherry
        { center := w, primary := x, secondary := y, attachment_nonterminal := hv
          center_nonterminal := hwNT, primary_terminal := hxT, secondary_terminal := hyT
          ports_ne := hxy, trunk := hvw, primary_arm := hwx, secondary_arm := hwy
          neighbors := hn, ordered := horder }, rfl⟩
    · exact ⟨Limb.cherry
        { center := w, primary := y, secondary := x, attachment_nonterminal := hv
          center_nonterminal := hwNT, primary_terminal := hyT, secondary_terminal := hxT
          ports_ne := hxy.symm, trunk := hvw, primary_arm := hwy, secondary_arm := hwx
          neighbors := fun z hz => by have h := hn z hz; tauto
          ordered := le_of_not_ge horder }, rfl⟩

theorem zero_core_star_of_three (S : TreeGeometry.TreeSolution I) (v : ↥S.vertices)
    (L : Fin 3 → Limb S v) (hinj : Function.Injective (fun i => (L i).stem)) :
    Nonempty (ShortStar S) := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ (fun i => (L i).length)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  refine ⟨
    { attachment := fun _ => v
      limb := L
      kept := k
      shortest := fun j => hk j (Finset.mem_univ j)
      disjoint := ?_
      outside := ?_
      core := ⊥
      core_le := bot_le
      core_nonterminal := Network.bot_terminalOnly _
      core_connects := fun _ _ => SimpleGraph.Reachable.refl _
      core_cost := ?_ }⟩
  · intro i j hij
    apply disjoint_regions_of_outside S v (L i).stem v (L j).stem (L i).stem_adj (L j).stem_adj
    · intro he
      have hstem : (L i).stem = (L j).stem := by
        rcases Sym2.eq_iff.mp he with ⟨_, h⟩ | ⟨h, h'⟩
        · exact h
        · exact h'.trans h
      exact hij (hinj hstem)
    · exact region_attachment_outside S v (L j).stem (L j).stem_adj
    · exact region_attachment_outside S v (L i).stem (L i).stem_adj
  · intro i j hij
    exact region_attachment_outside S v (L j).stem (L j).stem_adj
  · rw [Network.cost_bot]
    exact mul_nonneg (by norm_num [theta0]) (L k).length_pos.le

theorem no_zero_core_star_of_no_star (S : TreeGeometry.TreeSolution I)
    (hstar : ¬ Nonempty (ShortStar S)) :
    Rooted.NoZeroCoreStar S.graph (selectedTerminals S) := by
  classical
  intro v hv
  by_contra hcard
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    (Finset.two_lt_card_iff (s := Rooted.limbNeighbors S.graph (selectedTerminals S) v)).mp (by omega)
  have hvT : (v : V) ∉ I.terminals := fun h => hv ((mem_selectedTerminals S v).mpr h)
  obtain ⟨Lx, hLx⟩ := limb_of_neighbor S v x hvT hx
  obtain ⟨Ly, hLy⟩ := limb_of_neighbor S v y hvT hy
  obtain ⟨Lz, hLz⟩ := limb_of_neighbor S v z hvT hz
  let L : Fin 3 → Limb S v := ![Lx, Ly, Lz]
  have hinj : Function.Injective (fun i => (L i).stem) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [L]
  exact hstar (zero_core_star_of_three S v L hinj)

structure RootedFringe (S : TreeGeometry.TreeSolution I) (parent v : ↥S.vertices) where
  fan : Fan S parent v
  root : ↥S.vertices
  root_terminal : (root : V) ∈ I.terminals
  height_two : Rooted.height S.graph root (selectedTerminals S) v = 2
  parent_lower : S.graph.dist root parent + 1 = S.graph.dist root v
  has_cherry : 0 < fan.cherryCount

theorem fringe_of_height_two (S : TreeGeometry.TreeSolution I) (hc : S.IsClean)
    (hstar : ¬ Nonempty (ShortStar S)) (r : ↥S.vertices) (hr : (r : V) ∈ I.terminals)
    (parent v : ↥S.vertices) (hp : (parent : V) ∉ I.terminals) (hv : (v : V) ∉ I.terminals)
    (hpv : S.graph.Adj parent v)
    (hdepth : S.graph.dist r parent + 1 = S.graph.dist r v)
    (hheight : Rooted.height S.graph r (selectedTerminals S) v = 2) :
    Nonempty (RootedFringe S parent v) := by
  classical
  have hv' : v ∉ selectedTerminals S := fun h => hv ((mem_selectedTerminals S v).mp h)
  have hno := no_zero_core_star_of_no_star S hstar
  obtain ⟨_, hcard, hlimbs, w, hw, hwT, hw1⟩ := Rooted.height_two_fan S.graph r (selectedTerminals S)
    S.isTree ((mem_selectedTerminals S r).mpr hr) (rooted_clean S hc) hno hv' hheight
  obtain ⟨x, y, hxy, hchildren⟩ := Finset.card_eq_two.mp hcard
  have hx : x ∈ Rooted.children S.graph r v := by rw [hchildren]; simp
  have hy : y ∈ Rooted.children S.graph r v := by rw [hchildren]; simp
  obtain ⟨L, hL⟩ := limb_of_neighbor S v x hv (hlimbs hx)
  obtain ⟨R, hR⟩ := limb_of_neighbor S v y hv (hlimbs hy)
  have hpL : parent ≠ L.stem := by
    rw [hL]
    intro he
    exact Rooted.parent_not_child S.graph r hdepth (he ▸ hx)
  have hpR : parent ≠ R.stem := by
    rw [hR]
    intro he
    exact Rooted.parent_not_child S.graph r hdepth (he ▸ hy)
  let F : Fan S parent v :=
    { parent_nonterminal := hp
      parent_edge := hpv
      left := L
      right := R
      parent_ne_left := hpL
      parent_ne_right := hpR
      stems_ne := by rw [hL, hR]; exact hxy
      neighbors := by
        intro z hz
        rcases S.isTree.dist_eq_dist_add_one_of_adj r hz with hd | hd
        · exact Or.inl (Rooted.lower_neighbor_unique S.graph r S.isTree hz hpv.symm hd.symm hdepth)
        · have hz' : z ∈ Rooted.children S.graph r v :=
            (Rooted.mem_children S.graph r v z).mpr ⟨hz, hd⟩
          rw [hchildren] at hz'
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
          rw [hL, hR]
          tauto }
  have hhas : 0 < F.cherryCount := by
    have hw' : w = L.stem ∨ w = R.stem := by
      rw [hchildren] at hw
      simpa only [Finset.mem_insert, Finset.mem_singleton, hL, hR] using hw
    have hwNT : (w : V) ∉ I.terminals := fun h => hwT ((mem_selectedTerminals S w).mpr h)
    cases L with
    | direct l hlT hlA hlAdj =>
      cases R with
      | direct q hqT hqA hqAdj =>
        rcases hw' with he | he
        · exact False.elim (hwNT (by simpa only [he, Limb.stem] using hlA))
        · exact False.elim (hwNT (by simpa only [he, Limb.stem] using hqA))
      | cherry D => exact Nat.zero_lt_succ _
    | cherry C =>
      change 0 < 1 + R.cherryCount
      omega
  exact ⟨⟨F, r, hr, hheight, hdepth, hhas⟩⟩

end SteinerUpperBound.Structural.Tree

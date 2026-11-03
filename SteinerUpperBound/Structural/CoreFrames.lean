module

public import SteinerUpperBound.Structural.Topology

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

theorem edge_le_of_adj {G : SimpleGraph V} {x y : V} (h : G.Adj x y) :
    SimpleGraph.edge x y ≤ G := by
  intro a b hab
  rcases (SimpleGraph.edge_adj x y a b).mp hab with ⟨he | he, _⟩
  · rcases he with ⟨rfl, rfl⟩
    exact h
  · rcases he with ⟨rfl, rfl⟩
    exact h.symm

theorem edge_delete_le_of_adj_ne {G : SimpleGraph V} {x y : V}
    (h : G.Adj x y) (e : Sym2 V) (hne : s(x, y) ≠ e) :
    SimpleGraph.edge x y ≤ G.deleteEdges {e} :=
  edge_le_of_adj (SimpleGraph.deleteEdges_adj.mpr ⟨h, by simpa only [Set.mem_singleton_iff] using hne⟩)

theorem pair_val_ne (S : TreeGeometry.TreeSolution I) (a b c d : ↥S.vertices)
    (h : s(a, b) ≠ s(c, d)) :
    s((a : V), (b : V)) ≠ s((c : V), (d : V)) := by
  intro he
  apply h
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩)

theorem edge_terminalOnly (T : Finset V) {x y : V} (hx : x ∈ T) (hy : y ∈ T) :
    Network.TerminalOnly T (SimpleGraph.edge x y) := by
  intro a b hab
  exact Network.completeOn_terminalOnly T a b (edge_le_completeOn T hx hy hab)

structure CoreFrame (S : TreeGeometry.TreeSolution I) where
  limbs : Fin 3 → Σ v : ↥S.vertices, Limb S v
  core : SimpleGraph V
  core_le : core ≤ S.ambient
  core_nonterminal : Network.TerminalOnly (Finset.univ \ I.terminals) core
  core_connects : ∀ i j, core.Reachable (limbs i).1 (limbs j).1
  core_avoids : ∀ j, core ≤ S.ambient.deleteEdges {s(((limbs j).1 : V), ((limbs j).2.stem : V))}
  edges_ne : ∀ i j, i ≠ j →
    s((limbs i).1, (limbs i).2.stem) ≠ s((limbs j).1, (limbs j).2.stem)

namespace CoreFrame

variable {S : TreeGeometry.TreeSolution I}

abbrev attachment (F : CoreFrame S) (i : Fin 3) : ↥S.vertices := (F.limbs i).1
abbrev limb (F : CoreFrame S) (i : Fin 3) : Limb S (F.attachment i) := (F.limbs i).2
abbrev port (F : CoreFrame S) (i : Fin 3) : V := (F.limb i).primary

theorem outside (F : CoreFrame S) (i j : Fin 3) :
    (F.attachment i : V) ∉ (F.limb j).region := by
  have hc : ClosedCut F.core ((F.limb j).region : Set V) :=
    closedCut_mono (F.core_avoids j) (ambient_region_closed S (F.attachment j) (F.limb j).stem)
  intro hi
  have hj := (hc.reachable (F.core_connects j i)).mpr hi
  exact region_attachment_outside S (F.attachment j) (F.limb j).stem (F.limb j).stem_adj hj

theorem disjoint (F : CoreFrame S) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (F.limb i).region (F.limb j).region :=
  disjoint_regions_of_outside S (F.attachment i) (F.limb i).stem
    (F.attachment j) (F.limb j).stem (F.limb i).stem_adj (F.limb j).stem_adj
      (F.edges_ne i j hij) (F.outside i j) (F.outside j i)

theorem port_outside (F : CoreFrame S) {i j : Fin 3} (hij : i ≠ j) :
    F.port j ∉ (F.limb i).region := by
  intro h
  exact Finset.disjoint_left.mp (F.disjoint hij) h (F.limb j).primary_mem_region

theorem port_distance_le (F : CoreFrame S) (i j : Fin 3) :
    I.distance (F.port i) (F.port j) ≤ (F.limb i).length +
      GraphCost.cost I.weight F.core + (F.limb j).length := by
  have hc := TreeGeometry.distance_le_cost_of_reachable I F.core (F.core_connects i j)
  have hi := (F.limb i).primary_distance_le
  have hj := (F.limb j).primary_distance_le
  have ht1 := I.distance_triangle (F.port i) (F.attachment i) (F.port j)
  have ht2 := I.distance_triangle (F.attachment i) (F.attachment j) (F.port j)
  rw [I.distance_comm (F.port i) (F.attachment i)] at ht1
  linarith

theorem port_barrier (F : CoreFrame S) (hred : Reduced S) {i j : Fin 3} (hij : i ≠ j) :
    p * (F.limb i).length < I.distance (F.port i) (F.port j) :=
  (F.limb i).crossing_barrier hred (F.limb i).primary_terminal (F.limb j).primary_terminal
    (F.limb i).primary_mem_region (F.port_outside hij)

theorem short_star (F : CoreFrame S) (lower : ℝ)
    (hlower : ∀ i, lower ≤ (F.limb i).length)
    (hcost : GraphCost.cost I.weight F.core ≤ theta0 * lower) : Nonempty (ShortStar S) := by
  classical
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ (fun i => (F.limb i).length)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  refine ⟨
    { attachment := F.attachment
      limb := F.limb
      kept := k
      shortest := fun j => hk j (Finset.mem_univ _)
      disjoint := fun i j hij => F.disjoint hij
      outside := fun i j hij => F.outside i j
      core := F.core
      core_le := F.core_le
      core_nonterminal := F.core_nonterminal
      core_connects := F.core_connects
      core_cost := hcost.trans (mul_le_mul_of_nonneg_left (hlower k) (by norm_num [theta0])) }⟩

end CoreFrame

end SteinerUpperBound.Structural.Tree

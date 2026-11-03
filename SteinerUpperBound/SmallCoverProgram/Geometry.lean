module

public import SteinerUpperBound.SmallCoverProgram.Greedy
public import SteinerUpperBound.SmallCoverProgram.Encoding
public import SteinerUpperBound.Covers.Geometry.Structural

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.SmallCoverProgram

open Covers.Geometry
open scoped Classical

variable {n g : ℕ}

def retained (N : Vector (Fin n) g) : Finset (Fin n) := Finset.univ.image N.get

theorem mem_retained (N : Vector (Fin n) g) (x : Fin n) :
    x ∈ retained N ↔ ∃ i, N.get i = x := by simp [retained]

theorem retained_get (N : Vector (Fin n) g) (i : Fin g) : N.get i ∈ retained N :=
  (mem_retained N _).mpr ⟨i, rfl⟩

noncomputable def indexedGraph (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ) :
    SimpleGraph (Fin g) :=
  SimpleGraph.fromRel (fun i j => I.distance (N.get i) (N.get j) < a)

theorem indexedGraph_adj (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ)
    (i j : Fin g) :
    (indexedGraph I N a).Adj i j ↔ i ≠ j ∧ I.distance (N.get i) (N.get j) < a := by
  simp [indexedGraph, SimpleGraph.fromRel, I.distance_comm]

theorem indexedGraph_map (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ) :
    (indexedGraph I N a).map N.get = thresholdOn I (retained N) a := by
  ext x y
  rw [SimpleGraph.map_adj', thresholdOn_adj]
  constructor
  · rintro ⟨hne, i, j, hij, rfl, rfl⟩
    exact ⟨hne, retained_get N i, retained_get N j, ((indexedGraph_adj I N a i j).mp hij).2⟩
  · rintro ⟨hne, hx, hy, hd⟩
    obtain ⟨i, rfl⟩ := (mem_retained N x).mp hx
    obtain ⟨j, rfl⟩ := (mem_retained N y).mp hy
    have hij : i ≠ j := by intro h; exact hne (congrArg N.get h)
    exact ⟨hne, i, j, (indexedGraph_adj I N a i j).mpr ⟨hij, hd⟩, rfl, rfl⟩

theorem indexed_reachable (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) (i j : Fin g) :
    (indexedGraph I N a).Reachable i j ↔
      (thresholdOn I (retained N) a).Reachable (N.get i) (N.get j) := by
  have hh := SetSystem.quotient_reachable (⊥ : SimpleGraph (Fin g)) (indexedGraph I N a) N.get
    (by intro x y; simp [hN.eq_iff]) i j
  simpa only [bot_sup_eq, indexedGraph_map] using hh

noncomputable def cell (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ) (i : Fin g) :
    Finset (Fin n) := componentOn I (retained N) a (N.get i)

theorem cell_mem (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ) (i : Fin g) :
    cell I N a i ∈ componentsOn I (retained N) a :=
  componentOn_mem_componentsOn I _ a (retained_get N i)

theorem cell_eq_iff (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) (i j : Fin g) :
    cell I N a i = cell I N a j ↔ (indexedGraph I N a).Reachable i j := by
  rw [cell, cell, componentOn_eq_iff I (retained N) a (retained_get N j)]
  exact (indexed_reachable I N hN a i j).symm

noncomputable def observedAdj (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) :
    Closure.Dense Bool g :=
  (adjacencyTableRun N (metricTableRun m N).value a).value

noncomputable def connectedTable (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) :
    Closure.Dense Bool g := (Closure.computed (observedAdj m N a)).value

noncomputable def observedRowTable (m : Sym2 (Fin n) → ℝ) (N : Vector (Fin n) g) (a : ℝ) :
    Vector (Vector Bool g) n :=
  (rowTableRun (metricTableRun m N).value
    (Closure.rootsRun (connectedTable m N a)).value (5 * a / 8)).value

noncomputable def observedRows (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ) :
    Fin n → Finset (Fin g) := rowSets (observedRowTable I.weight N a)

def rootIds (a : Closure.Dense Bool g) : Finset (Fin g) :=
  Finset.univ.filter (fun i => Closure.rootValue a i = i)

theorem mem_rootIds (a : Closure.Dense Bool g) (i : Fin g) :
    i ∈ rootIds a ↔ Closure.rootValue a i = i := by simp [rootIds]

theorem connectedTable_correct (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ)
    (i j : Fin g) :
    Closure.entry (connectedTable I.weight N a) i j = true ↔
      (indexedGraph I N a).Reachable i j := by
  apply Closure.computed_correct
  intro x y
  rw [observedAdj, adjacencyTable_get, metricTable_get, Instance.weight_mk, indexedGraph_adj]

theorem cell_root (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) (i : Fin g) :
    cell I N a (Closure.rootValue (connectedTable I.weight N a) i) = cell I N a i :=
  (cell_eq_iff I N hN a _ _).mpr
    (Closure.root_reachable _ _ (connectedTable_correct I N a) i).symm

theorem cell_injective_roots (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    Set.InjOn (cell I N a) (rootIds (connectedTable I.weight N a) : Set (Fin g)) := by
  intro i hi j hj he
  have hh := Closure.root_eq_of_reachable _ _ (connectedTable_correct I N a)
    ((cell_eq_iff I N hN a i j).mp he)
  rw [(mem_rootIds _ i).mp hi, (mem_rootIds _ j).mp hj] at hh
  exact hh

theorem cell_surjective (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ)
    (C : Finset (Fin n)) (hC : C ∈ componentsOn I (retained N) a) :
    ∃ i : Fin g, cell I N a i = C := by
  obtain ⟨x, hx⟩ := componentsOn_nonempty I (retained N) a hC
  obtain ⟨i, hi⟩ := (mem_retained N x).mp (componentsOn_subset I (retained N) a hC hx)
  refine ⟨i, ?_⟩
  simpa only [cell, hi] using componentOn_eq_of_mem I (retained N) a hC hx

theorem root_cells (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    (rootIds (connectedTable I.weight N a)).image (cell I N a) =
      componentsOn I (retained N) a := by
  classical
  apply Finset.Subset.antisymm
  · intro C hC
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hC
    exact cell_mem I N a i
  · intro C hC
    obtain ⟨i, hi⟩ := cell_surjective I N a C hC
    apply Finset.mem_image.mpr
    refine ⟨Closure.rootValue (connectedTable I.weight N a) i, ?_, (cell_root I N hN a i).trans hi⟩
    exact (mem_rootIds _ _).mpr (Closure.root_idempotent _ _ (connectedTable_correct I N a) i)

theorem mem_observedRows (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ)
    (v : Fin n) (j : Fin g) :
    j ∈ observedRows I N a v ↔ ∃ i : Fin g,
      I.distance v (N.get i) ≤ 5 * a / 8 ∧
        Closure.rootValue (connectedTable I.weight N a) i = j := by
  unfold observedRows rowSets
  rw [mem_bits]
  change ((rowTableRun (metricTableRun I.weight N).value
    (Closure.rootsRun (connectedTable I.weight N a)).value (5 * a / 8)).value.get v).get j = true ↔ _
  rw [rowTable_get]
  simp_rw [metricTable_get, Instance.weight_mk, Closure.rootsRun_get]
  constructor
  · rintro ⟨i, hd, he⟩
    exact ⟨i, by simpa only [I.distance_comm] using hd, Fin.ext he⟩
  · rintro ⟨i, hd, he⟩
    exact ⟨i, by simpa only [I.distance_comm] using hd, congrArg Fin.val he⟩

theorem observedRows_support (I : Instance (Fin n)) (N : Vector (Fin n) g) (a : ℝ)
    (v : Fin n) :
    observedRows I N a v ⊆ rootIds (connectedTable I.weight N a) := by
  intro j hj
  obtain ⟨i, _, rfl⟩ := (mem_observedRows I N a v j).mp hj
  exact (mem_rootIds _ _).mpr (Closure.root_idempotent _ _ (connectedTable_correct I N a) i)

theorem observedRows_image (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    SetSystem.mapPorts (observedRows I N a) (cell I N a) =
      rowOn I (retained N) a (5 * a / 8) := by
  funext v
  ext C
  rw [SetSystem.mem_mapPorts, mem_rowOn]
  constructor
  · rintro ⟨j, hj, hjC⟩
    obtain ⟨i, hd, hij⟩ := (mem_observedRows I N a v j).mp hj
    have hiC : cell I N a i = C :=
      (cell_root I N hN a i).symm.trans ((congrArg (cell I N a) hij).trans hjC)
    refine ⟨hjC ▸ cell_mem I N a j, N.get i, ?_, hd⟩
    exact hiC ▸ componentOn_self I (retained N) a (retained_get N i)
  · rintro ⟨hC, x, hx, hd⟩
    obtain ⟨i, hi⟩ := (mem_retained N x).mp (componentsOn_subset I (retained N) a hC hx)
    let j := Closure.rootValue (connectedTable I.weight N a) i
    refine ⟨j, (mem_observedRows I N a v j).mpr ⟨i, ?_, rfl⟩, ?_⟩
    · simpa only [hi] using hd
    · have hci : cell I N a i = C := by
        simpa only [cell, hi] using componentOn_eq_of_mem I (retained N) a hC hx
      exact (cell_root I N hN a i).trans hci

theorem observedRows_card (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) (v : Fin n) :
    (observedRows I N a v).card = (rowOn I (retained N) a (5 * a / 8) v).card := by
  have hh := mapPorts_card_of_injOn (observedRows I N a) (cell I N a) v
    (fun x hx y hy => cell_injective_roots I N hN a
      (observedRows_support I N a v hx) (observedRows_support I N a v hy))
  rw [observedRows_image I N hN a] at hh
  exact hh.symm

theorem observed_eligible (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    eligible (observedRowTable I.weight N a) = eligibleOn I (retained N) a (5 * a / 8) := by
  ext v
  rw [mem_eligible]
  change (3 ≤ (observedRows I N a v).card) ↔ _
  simp only [eligibleOn, Finset.mem_filter, Finset.mem_univ, true_and,
    observedRows_card I N hN a v]

theorem greedy_actual_estimate (I : Instance (Fin n)) (N : Vector (Fin n) g)
    (hN : Function.Injective N.get) (a : ℝ) :
    (greedyScoreRun (observedRowTable I.weight N a)).value =
      SetSystem.smallCoverEstimate (eligibleOn I (retained N) a (5 * a / 8))
        (rowOn I (retained N) a (5 * a / 8)) (componentsOn I (retained N) a) (List.finRange n) := by
  rw [greedyScoreRun_value]
  have hB (v : Fin n) : SetSystem.mapPorts (observedRows I N a) (cell I N a) v ⊆
      componentsOn I (retained N) a := by
    rw [observedRows_image I N hN a]
    exact rowOn_subset_componentsOn I (retained N) a (5 * a / 8) v
  have hh := smallCoverEstimate_rename (eligible (observedRowTable I.weight N a))
    (observedRows I N a) (rootIds (connectedTable I.weight N a)) (observedRows_support I N a)
    (cell I N a) (cell_injective_roots I N hN a) (componentsOn I (retained N) a) hB (List.finRange n)
  rw [observedRows_image I N hN a, observed_eligible I N hN a] at hh
  rw [observed_eligible I N hN a]
  exact hh

end SteinerUpperBound.SmallCoverProgram

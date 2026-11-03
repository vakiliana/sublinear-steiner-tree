module

public import SteinerUpperBound.PortGraph.Copies

@[expose] public section

namespace SteinerUpperBound.PortGraph

open QueryProgram
open scoped Classical BigOperators
open Covers.Geometry

variable {n k : ℕ} {Q : Type}

noncomputable def pointList (cfg : LocalAccess.SlotConfig Q n k) (C : Finset (Fin n)) :
    List (Fin n) :=
  (LocalAccess.canonicalResult C.toList cfg.terminals.toList).value

noncomputable def canonicalFrame (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (b B : ℕ) (C : Finset (Fin n)) : LocalAccess.Frame (Fin n) b B :=
  (LocalAccess.frameResult I.weight (radius cfg) b B (List.finRange n)
    cfg.terminals.toList C.toList).value

theorem terminal_mem (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (x : Fin n) :
    x ∈ cfg.terminals.toList ↔ x ∈ I.terminals := by
  classical
  rw [← List.mem_toFinset, hT]

theorem pointList_mem (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Finset (Fin n))
    (hC : C ⊆ I.terminals) (x : Fin n) :
    x ∈ pointList cfg C ↔ x ∈ C := by
  rw [pointList, LocalAccess.canonical_value]
  simp only [List.mem_filter, decide_eq_true_eq, Finset.mem_toList]
  exact ⟨And.right, fun hx => ⟨(terminal_mem I cfg hT x).mpr (hC hx), hx⟩⟩

theorem pointList_set (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Finset (Fin n))
    (hC : C ⊆ I.terminals) : (pointList cfg C).toFinset = C := by
  classical
  ext x
  simpa only [List.mem_toFinset] using pointList_mem I cfg hT C hC x

theorem pointList_nodup (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.Nodup) (C : Finset (Fin n)) : (pointList cfg C).Nodup :=
  LocalAccess.canonical_nodup _ _ hT

theorem pointList_length (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Finset (Fin n)) (hC : C ⊆ I.terminals) :
    (pointList cfg C).length = C.card := by
  classical
  rw [← List.toFinset_card_of_nodup (pointList_nodup cfg hnd C), pointList_set I cfg hT C hC]

theorem canonicalFrame_points (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (b B : ℕ) (C : Finset (Fin n)) :
    (canonicalFrame I cfg b B C).points = pointList cfg C := rfl

theorem frame_value_congr {V : Type*} (w : Sym2 V → ℝ) (r : ℝ) (b B : ℕ)
    (vertices terminals p p' : List V) (hp : p.toFinset = p'.toFinset) :
    (LocalAccess.frameResult w r b B vertices terminals p).value =
      (LocalAccess.frameResult w r b B vertices terminals p').value := by
  have h := LocalAccess.canonical_equal p p' terminals hp
  simp only [LocalAccess.frameResult, Outcome.combine, Outcome.add, Outcome.pure]
  rw [h]

theorem canonicalFrame_pointSlot (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (b B : ℕ) (C : Finset (Fin n)) (i : Fin B) :
    (canonicalFrame I cfg b B C).pointSlots.get i = (pointList cfg C)[i.val]? := by
  rw [canonicalFrame, LocalAccess.frame_pointSlot, pointList, LocalAccess.canonical_value]

theorem bool_ext (x y : Bool) (h : x = true ↔ y = true) : x = y := by
  cases x <;> cases y <;> simp_all

theorem canonicalFrame_centers (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    {C : Finset (Fin n)} (hC : C ∈ parts I bits cfg) :
    (canonicalFrame I cfg b B C).rows.centers = centerList I bits cfg b C := by
  rw [canonicalFrame, LocalAccess.frame_rows]
  unfold centerList incidentList
  apply congrArg (List.take b)
  apply List.filter_congr
  intro v _
  apply bool_ext
  rw [LocalAccess.near_value]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, hd⟩
    apply (mem_rowOn I _ _ _ v C).mpr
    refine ⟨hC, x, (pointList_mem I cfg hT C
      ((componentsOn_subset I _ _ hC).trans (retained_subset I bits cfg)) x).mp hx, ?_⟩
    simpa only [Instance.weight_mk] using hd
  · intro hv
    obtain ⟨_, x, hx, hd⟩ := (mem_rowOn I _ _ _ v C).mp hv
    refine ⟨x, (pointList_mem I cfg hT C
      ((componentsOn_subset I _ _ hC).trans (retained_subset I bits cfg)) x).mpr hx, ?_⟩
    simpa only [Instance.weight_mk] using hd

theorem canonicalFrame_rowSlot (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    {C : Finset (Fin n)} (hC : C ∈ parts I bits cfg) (i : Fin b) :
    (canonicalFrame I cfg b B C).rows.slots.get i = (centerList I bits cfg b C)[i.val]? := by
  have h := LocalAccess.frame_rowSlot I.weight (radius cfg) b B (List.finRange n)
    cfg.terminals.toList C.toList i
  rw [← LocalAccess.frame_rows] at h
  rw [← canonicalFrame, canonicalFrame_centers I bits cfg b B hT hC] at h
  exact h

noncomputable def exploreSet {V R : Type*} (bits : R → Bool) (key : V → R) (terminals : List V) :
    Finset V :=
  ComponentExplore.retained bits key terminals.toFinset

noncomputable def exploreGraph {V R : Type*} [Fintype V] (w : Sym2 V → ℝ)
    (bits : R → Bool) (key : V → R) (a : ℝ) (terminals : List V) : SimpleGraph V :=
  ComponentExplore.retainedGraph w bits key terminals.toFinset a

theorem exploreGraph_below {V R : Type*} [Fintype V] (w : Sym2 V → ℝ)
    (bits : R → Bool) (key : V → R) (a : ℝ) (terminals : List V) :
    exploreGraph w bits key a terminals = TerminalMST.below w (exploreSet bits key terminals) a := rfl

theorem explored_component_mem {V : Type*} [Fintype V] (G : SimpleGraph V) (x y : V) :
    y ∈ ComponentExplore.component G x ↔ G.Reachable x y := by
  classical
  simp only [ComponentExplore.component, Finset.mem_filter, Finset.mem_univ, true_and]

theorem explore_reachable {V R : Type*} [Fintype V] (w : Sym2 V → ℝ)
    (bits : R → Bool) (key : V → R) (a : ℝ) (terminals : List V)
    {x y : V} (hx : x ∈ exploreSet bits key terminals)
    (hxy : (exploreGraph w bits key a terminals).Reachable x y) :
    y ∈ exploreSet bits key terminals :=
  ComponentExplore.reachable_retained w bits key _ a hx hxy

theorem exploreSet_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals) :
    exploreSet bits cfg.key cfg.terminals.toList = retained I bits cfg := by
  classical
  ext x
  simp only [exploreSet, ComponentExplore.retained, retained, Finset.mem_filter, List.mem_toFinset]
  exact and_congr_left (fun _ => terminal_mem I cfg hT x)

theorem exploreGraph_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals) :
    exploreGraph I.weight bits cfg.key cfg.scale cfg.terminals.toList =
      thresholdOn I (retained I bits cfg) cfg.scale := by
  rw [exploreGraph_below, exploreSet_eq I bits cfg hT]
  ext x y
  rw [TerminalMST.below_adj, thresholdOn_adj]
  rw [Instance.weight_mk]

theorem explore_component (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    {x : Fin n} (hx : x ∈ retained I bits cfg) :
    ComponentExplore.component
      (exploreGraph I.weight bits cfg.key cfg.scale cfg.terminals.toList) x =
      portComponent I bits cfg x := by
  classical
  have hx' : x ∈ exploreSet bits cfg.key cfg.terminals.toList := by
    rwa [exploreSet_eq I bits cfg hT]
  ext y
  rw [explored_component_mem, portComponent, mem_componentOn]
  constructor
  · intro h
    exact ⟨by
      have hy := explore_reachable I.weight bits cfg.key cfg.scale cfg.terminals.toList hx' h
      rwa [exploreSet_eq I bits cfg hT] at hy,
      (exploreGraph_eq I bits cfg hT) ▸ h⟩
  · rintro ⟨_, h⟩
    exact (exploreGraph_eq I bits cfg hT).symm ▸ h

/-- The false completion flag supplies a real connected `B+1` witness. Thus a
small component cannot be rejected merely because the cache or root changed. -/
theorem explore_complete_iff (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) {x : Fin n}
    (hx : x ∈ retained I bits cfg) (c : Cache Q) (hc : Cache.Correct bits c) :
    (ComponentExplore.result I.weight bits cfg.key cfg.scale B cfg.terminals.toList x c).value.complete = true ↔
      (portComponent I bits cfg x).card ≤ B := by
  classical
  have hx' : x ∈ exploreSet bits cfg.key cfg.terminals.toList := by
    rwa [exploreSet_eq I bits cfg hT]
  let e := ComponentExplore.result I.weight bits cfg.key cfg.scale B cfg.terminals.toList x c
  let G := exploreGraph I.weight bits cfg.key cfg.scale cfg.terminals.toList
  have hr := ComponentExplore.result_correct I.weight bits cfg.key cfg.scale B
    cfg.terminals.toList x c hc hx'
  change (∀ y ∈ e.value.project.state.found, G.Reachable x y) ∧
    (if e.value.complete = true then e.value.project.state.found = ComponentExplore.component G x ∧
      e.value.project.state.found.card ≤ B else e.value.project.state.found.card = B + 1) at hr
  have heq := explore_component I bits cfg hT hx
  change ComponentExplore.component G x = portComponent I bits cfg x at heq
  change e.value.complete = true ↔ _
  constructor
  · intro he
    have h := hr.2
    rw [ite_eq_left he] at h
    rw [← heq, ← h.1]
    exact h.2
  · intro hsmall
    by_contra hn
    have hs := hr.2
    rw [ite_eq_right hn] at hs
    have hsub : e.value.project.state.found ⊆ ComponentExplore.component G x := by
      intro y hy
      exact (explored_component_mem G x y).mpr (hr.1 y hy)
    have hcard := Finset.card_le_card hsub
    rw [hs, heq] at hcard
    omega

theorem locate_frame (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    {x : Fin n} (hx : x ∈ retained I bits cfg) (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.locateResult I.weight bits cfg.key cfg.scale b B (List.finRange n)
      cfg.terminals.toList x c).value.frame =
      if (portComponent I bits cfg x).card ≤ B then
        some (canonicalFrame I cfg b B (portComponent I bits cfg x)) else none := by
  classical
  let e := ComponentExplore.result I.weight bits cfg.key cfg.scale B cfg.terminals.toList x c
  have hx' : x ∈ exploreSet bits cfg.key cfg.terminals.toList := by
    rwa [exploreSet_eq I bits cfg hT]
  by_cases hsmall : (portComponent I bits cfg x).card ≤ B
  · have he : e.value.complete = true := (explore_complete_iff I bits cfg B hT hx c hc).mpr hsmall
    have hpoints := (LocalAccess.explored_complete I.weight bits cfg.key cfg.scale B
      cfg.terminals.toList x c hc hx' he).1
    simp only [LocalAccess.locateResult]
    rw [ite_eq_left he, ite_eq_left hsmall]
    simp only [Outcome.combine, Outcome.add, Outcome.pure]
    congr 1
    apply frame_value_congr I.weight (radius cfg) b B (List.finRange n) cfg.terminals.toList
      e.value.memory.points (portComponent I bits cfg x).toList
    simpa only [Finset.toList_toFinset] using
      hpoints.trans (explore_component I bits cfg hT hx)
  · have he : e.value.complete ≠ true := fun he =>
      hsmall ((explore_complete_iff I bits cfg B hT hx c hc).mp he)
    simp only [LocalAccess.locateResult]
    rw [ite_eq_right he, ite_eq_right hsmall]
    rfl

end SteinerUpperBound.PortGraph

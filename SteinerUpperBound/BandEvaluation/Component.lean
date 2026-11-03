module

public import SteinerUpperBound.BandEvaluation.FrontendDeterminism

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open QueryProgram Covers.Geometry
open scoped Classical

variable {V Q : Type*} [Fintype V]

noncomputable def retainedSet (b : Q → Bool) (key : V → Q) (terminals : List V) : Finset V :=
  ComponentExplore.retained b key terminals.toFinset

noncomputable def trueComponent (I : Instance V) (b : Q → Bool) (key : V → Q)
    (terminals : List V) (a : ℝ) (root : V) : Finset V :=
  componentOn I (retainedSet b key terminals) a root

theorem retainedGraph_eq (I : Instance V) (b : Q → Bool) (key : V → Q)
    (terminals : List V) (a : ℝ) :
    ComponentExplore.retainedGraph I.weight b key terminals.toFinset a =
      thresholdOn I (retainedSet b key terminals) a := by
  ext x y
  simp only [ComponentExplore.retainedGraph, retainedSet, TerminalMST.below_adj,
    thresholdOn_adj, Instance.weight_mk]

theorem explored_component_eq (I : Instance V) (b : Q → Bool) (key : V → Q)
    (terminals : List V) (a : ℝ) (root : V) (hr : root ∈ retainedSet b key terminals) :
    ComponentExplore.component (ComponentExplore.retainedGraph I.weight b key terminals.toFinset a) root =
      trueComponent I b key terminals a root := by
  ext y
  simp only [ComponentExplore.component, Finset.mem_filter, Finset.mem_univ, true_and,
    trueComponent, mem_componentOn]
  rw [← retainedGraph_eq]
  exact ⟨fun h => ⟨ComponentExplore.reachable_retained I.weight b key terminals.toFinset a hr h, h⟩,
    And.right⟩

theorem explore_points_of_complete (I : Instance V) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct b c) (hr : root ∈ retainedSet b key terminals)
    (hcomplete : (ComponentExplore.result I.weight b key a B terminals root c).value.complete = true) :
    (ComponentExplore.result I.weight b key a B terminals root c).value.memory.points.toFinset =
      trueComponent I b key terminals a root := by
  have h := ComponentExplore.result_correct I.weight b key a B terminals root c hc hr
  have he := explored_component_eq I b key terminals a root hr
  have hh := h.2
  simp only [ComponentExplore.Answer.project, hcomplete, ↓reduceIte, he] at hh
  exact hh.1

theorem explore_complete_iff (I : Instance V) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (terminals : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct b c) (hr : root ∈ retainedSet b key terminals) :
    (ComponentExplore.result I.weight b key a B terminals root c).value.complete = true ↔
      (trueComponent I b key terminals a root).card ≤ B := by
  have h := ComponentExplore.result_correct I.weight b key a B terminals root c hc hr
  have he := explored_component_eq I b key terminals a root hr
  have hsub :
      (ComponentExplore.result I.weight b key a B terminals root c).value.memory.points.toFinset ⊆
        trueComponent I b key terminals a root := by
    intro y hy
    rw [← he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1 y hy⟩
  cases hv : (ComponentExplore.result I.weight b key a B terminals root c).value.complete with
  | true =>
      have hh := h.2
      simp only [ComponentExplore.Answer.project, hv, ↓reduceIte, he] at hh
      have hcard := hh.2
      rw [hh.1] at hcard
      exact ⟨fun _ => hcard, fun _ => rfl⟩
  | false =>
      have hh := h.2
      simp only [ComponentExplore.Answer.project, hv, Bool.false_eq_true, ↓reduceIte] at hh
      have hle := Finset.card_le_card hsub
      have hn : ¬(trueComponent I b key terminals a root).card ≤ B := by
        change (ComponentExplore.result I.weight b key a B terminals root c).value.memory.points.toFinset.card =
          B + 1 at hh
        omega
      simp only [Bool.false_eq_true, hn]

theorem explore_length_le (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (terminals : List V) (root : V) (c : Cache Q) (hc : Cache.Correct b c) :
    (ComponentExplore.result w b key a B terminals root c).value.memory.points.length ≤ B + 1 := by
  have hv := ComponentExplore.result_valid w b key a B terminals root c hc
  have hz := ComponentExplore.loop_count w b key a B terminals (B + 1) (ComponentExplore.initial root c)
    (by simp [ComponentExplore.initial])
  change (ComponentExplore.result w b key a B terminals root c).value.memory.count ≤ B + 1 at hz
  rw [hv.count_eq] at hz
  exact hz

omit [Fintype V] in
theorem component_nonempty (I : Instance V) (N : Finset V) (a : ℝ) (root : V) (hr : root ∈ N) :
    (componentOn I N a root).Nonempty :=
  ⟨root, componentOn_self I N a hr⟩

omit [Fintype V] in
theorem component_empty_of_not_mem (I : Instance V) (N : Finset V) (a : ℝ) (root : V) (hr : root ∉ N) :
    componentOn I N a root = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hyN, p⟩ := (mem_componentOn I N a root y).mp hy
  obtain ⟨p⟩ := p
  cases p with
  | nil => exact hr hyN
  | cons hxy p => exact hr ((thresholdOn_adj I N a _ _).mp hxy).2.1

theorem band_empty (I : Instance V) (a rho tau : ℝ) : Band.score I ∅ a rho tau = 0 := by
  have hs : Band.smallSets (∅ : Finset V) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro Y hY
    obtain ⟨hsub, h2, _⟩ := (Band.mem_smallSets ∅ Y).mp hY
    have he : Y = ∅ := Finset.subset_empty.mp hsub
    rw [he, Finset.card_empty] at h2
    omega
  simp [Band.score, Band.candidates, hs]

end SteinerUpperBound.BandEvaluation

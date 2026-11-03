module

public import SteinerUpperBound.Covers.Geometry.Threshold

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open scoped Classical BigOperators

variable {V : Type*}

def CoverOn (I : Instance V) (T N : Finset V) (ρ : ℝ) : Prop :=
  ∀ x ∈ T, ∃ y ∈ N, I.distance x y ≤ ρ

/-- Analysis-only projection: retained points are fixed; other terminals use a
chosen cover witness. The total extension fixes points outside `T`. -/
noncomputable def project (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (x : V) : V :=
  if x ∈ N then x else if hx : x ∈ T then Classical.choose (hc x hx) else x

theorem project_fix (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) {x : V} (hx : x ∈ N) :
    project I T N ρ hc x = x := by simp [project, hx]

theorem project_mem (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) {x : V} (hx : x ∈ T) :
    project I T N ρ hc x ∈ N := by
  by_cases hxN : x ∈ N
  · simpa only [project_fix I T N ρ hc hxN] using hxN
  · simpa [project, hxN, hx] using (Classical.choose_spec (hc x hx)).1

theorem project_move (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) {x : V} (hx : x ∈ T) :
    I.distance x (project I T N ρ hc x) ≤ ρ := by
  by_cases hxN : x ∈ N
  · rw [project_fix I T N ρ hc hxN, I.distance_self]
    exact hρ
  · simpa [project, hxN, hx] using (Classical.choose_spec (hc x hx)).2

noncomputable def projection (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) : {x // x ∈ T} → {y // y ∈ N} :=
  fun x => ⟨project I T N ρ hc x.val, project_mem I T N ρ hc x.property⟩

theorem projection_move (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (x : {x // x ∈ T}) :
    I.distance x.val (projection I T N ρ hc x).val ≤ ρ :=
  project_move I T N ρ hc hρ x.property

theorem projection_fix (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (y : {y // y ∈ N}) :
    (projection I T N ρ hc ⟨y.val, hNT y.property⟩).val = y.val :=
  project_fix I T N ρ hc y.property

theorem projection_surjective (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) :
    Function.Surjective (projection I T N ρ hc) := by
  intro y
  refine ⟨⟨y.val, hNT y.property⟩, ?_⟩
  apply Subtype.ext
  exact project_fix I T N ρ hc y.property

theorem project_distance (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) {x y : V}
    (hx : x ∈ T) (hy : y ∈ T) :
    I.distance (project I T N ρ hc x) (project I T N ρ hc y) ≤ I.distance x y + 2 * ρ := by
  have hxmove := project_move I T N ρ hc hρ hx
  have hymove := project_move I T N ρ hc hρ hy
  have h₁ := I.distance_triangle (project I T N ρ hc x) x (project I T N ρ hc y)
  have h₂ := I.distance_triangle x y (project I T N ρ hc y)
  rw [I.distance_comm (project I T N ρ hc x) x] at h₁
  linarith

theorem reachable_map_of_edges {G H : SimpleGraph V} (f : V → V)
    (h : ∀ x y, G.Adj x y → H.Reachable (f x) (f y)) {x y : V}
    (hxy : G.Reachable x y) : H.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons huv p ih => exact (h _ _ huv).trans ih

/-- A strict `t-2ρ` threshold path projects to a strict `t` threshold path.
Equal consecutive projected vertices are handled by reflexive reachability. -/
theorem project_reachable (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (t : ℝ) {x y : V}
    (hxy : (thresholdOn I T (t - 2 * ρ)).Reachable x y) :
    (thresholdOn I N t).Reachable (project I T N ρ hc x) (project I T N ρ hc y) := by
  apply reachable_map_of_edges (project I T N ρ hc) _ hxy
  intro u v huv
  obtain ⟨_, hu, hv, hd⟩ := (thresholdOn_adj I T (t - 2 * ρ) u v).mp huv
  by_cases he : project I T N ρ hc u = project I T N ρ hc v
  · rw [he]
  · apply SimpleGraph.Adj.reachable
    apply (thresholdOn_adj I N t _ _).mpr
    refine ⟨he, project_mem I T N ρ hc hu, project_mem I T N ρ hc hv, ?_⟩
    linarith [project_distance I T N ρ hc hρ hu hv]

theorem terminal_attachment (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {x : V} (hx : x ∈ T) :
    (thresholdOn I T a).Reachable x (project I T N ρ hc x) := by
  by_cases he : x = project I T N ρ hc x
  · rw [← he]
  · apply SimpleGraph.Adj.reachable
    exact (thresholdOn_adj I T a _ _).mpr
      ⟨he, hx, hNT (project_mem I T N ρ hc hx),
        (project_move I T N ρ hc hρ hx).trans_lt hρa⟩

/-- The retained relation, pulled back by the actual projection, refines the
exact terminal relation. Attachments require `ρ < a`, not independence. -/
theorem pullback_reachable (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {x y : V} (hx : x ∈ T) (hy : y ∈ T)
    (hxy : (thresholdOn I N a).Reachable
      (project I T N ρ hc x) (project I T N ρ hc y)) :
    (thresholdOn I T a).Reachable x y :=
  (terminal_attachment I T N ρ hc hNT hρ a hρa hx).trans
    ((reachable_mono I hNT le_rfl hxy).trans
      (terminal_attachment I T N ρ hc hNT hρ a hρa hy).symm)

noncomputable def pullbackComponent (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (a : ℝ) (x : V) : Finset V :=
  T.filter (fun y => (thresholdOn I N a).Reachable
    (project I T N ρ hc x) (project I T N ρ hc y))

/-- The actual path/partition sandwich, expressed as inclusions of finite
component cells on the original terminal set. -/
theorem component_sandwich (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {x : V} (hx : x ∈ T) :
    componentOn I T (a - 2 * ρ) x ⊆ pullbackComponent I T N ρ hc a x ∧
      pullbackComponent I T N ρ hc a x ⊆ componentOn I T a x := by
  constructor
  · intro y hy
    obtain ⟨hyT, hxy⟩ := (mem_componentOn I T _ x y).mp hy
    exact Finset.mem_filter.mpr ⟨hyT, project_reachable I T N ρ hc hρ a hxy⟩
  · intro y hy
    obtain ⟨hyT, hxy⟩ := Finset.mem_filter.mp hy
    exact (mem_componentOn I T a x y).mpr
      ⟨hyT, pullback_reachable I T N ρ hc hNT hρ a hρa hx hyT hxy⟩

/-- Lower and upper bottleneck comparisons without selecting bottleneck minima.
For any retained component `C` at `a`, a terminal `t`-path between its points
has a `C`-path at `t+2ρ`, for every real threshold `t`. -/
theorem bottleneck_upper (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I N a) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) (t : ℝ)
    (hxy : (thresholdOn I T t).Reachable x y) :
    (thresholdOn I C (t + 2 * ρ)).Reachable x y := by
  by_cases hta : t + 2 * ρ ≤ a
  · have hxy' : (thresholdOn I T ((t + 2 * ρ) - 2 * ρ)).Reachable x y := by
      simpa only [add_sub_cancel_right] using hxy
    have hp := project_reachable I T N ρ hc hρ (t + 2 * ρ) hxy'
    rw [project_fix I T N ρ hc (componentsOn_subset I N a hC hx),
      project_fix I T N ρ hc (componentsOn_subset I N a hC hy)] at hp
    exact reachable_restrict I N a hC hta hx hp
  · exact reachable_mono I (Finset.Subset.refl C) (le_of_not_ge hta)
      (componentOn_connected I N a hC hx hy)

theorem bottleneck_lower (I : Instance V) (T N : Finset V) (hNT : N ⊆ T) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I N a) (t : ℝ) {x y : V}
    (hxy : (thresholdOn I C t).Reachable x y) :
    (thresholdOn I T t).Reachable x y :=
  reachable_mono I ((componentsOn_subset I N a hC).trans hNT) le_rfl hxy

/-- The shifted-threshold relation used for every `Y ⊆ C`. -/
theorem component_shifted_reachable (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ)
    {C Y : Finset V} (hC : C ∈ componentsOn I N a) (hY : Y ⊆ C)
    (t : ℝ) (hta : t ≤ a) {x y : V} (hx : x ∈ Y) (hy : y ∈ Y)
    (hxy : (thresholdOn I T (t - 2 * ρ)).Reachable x y) :
    (thresholdOn I C t).Reachable x y := by
  have hp := project_reachable I T N ρ hc hρ t hxy
  rw [project_fix I T N ρ hc (componentsOn_subset I N a hC (hY hx)),
    project_fix I T N ρ hc (componentsOn_subset I N a hC (hY hy))] at hp
  exact reachable_restrict I N a hC hta (hY hx) hp

end SteinerUpperBound.Covers.Geometry

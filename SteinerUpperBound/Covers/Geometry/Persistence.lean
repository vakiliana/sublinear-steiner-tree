module

public import SteinerUpperBound.Covers.Geometry.Domination

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open scoped Classical BigOperators

variable {V : Type*}

theorem componentMap_coarsen (I : Instance V) (T : Finset V) (s a : ℝ)
    (hsa : s ≤ a) {x : V} (hx : x ∈ T) :
    componentMap I T a (componentOn I T s x) = componentOn I T a x := by
  have hn : (componentOn I T s x).Nonempty := ⟨x, componentOn_self I T s hx⟩
  have hr := ((mem_componentOn I T s x _).mp (Classical.choose_spec hn)).2
  rw [componentMap, dif_pos hn]
  exact (componentOn_eq_of_reachable I T a
    (reachable_mono I (Finset.Subset.refl T) hsa hr)).symm

theorem componentMap_coarsen_mem (I : Instance V) (T : Finset V) (s a : ℝ)
    (hsa : s ≤ a) {D : Finset V} (hD : D ∈ componentsOn I T s) :
    componentMap I T a D ∈ componentsOn I T a := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
  rw [componentMap_coarsen I T s a hsa hx]
  exact componentOn_mem_componentsOn I T a hx

theorem componentMap_coarsen_surjective (I : Instance V) (T : Finset V) (s a : ℝ)
    (hsa : s ≤ a) {C : Finset V} (hC : C ∈ componentsOn I T a) :
    ∃ D ∈ componentsOn I T s, componentMap I T a D = C := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨componentOn I T s x, componentOn_mem_componentsOn I T s hx,
    componentMap_coarsen I T s a hsa hx⟩

/-- Exact coarse components split by the finer terminal threshold. This finite
set is independent of every retained cover and its randomness. -/
noncomputable def phaseBad (I : Instance V) (T : Finset V) (s a : ℝ) :
    Finset (Finset V) :=
  (componentsOn I T a).filter (fun C =>
    ∃ x ∈ C, ∃ y ∈ C, ¬ (thresholdOn I T s).Reachable x y)

theorem phaseBad_subset (I : Instance V) (T : Finset V) (s a : ℝ) :
    phaseBad I T s a ⊆ componentsOn I T a := Finset.filter_subset _ _

theorem phaseBad_fiber (I : Instance V) (T : Finset V) (s a : ℝ) (hsa : s ≤ a)
    {C : Finset V} (hC : C ∈ phaseBad I T s a) :
    2 ≤ ((componentsOn I T s).filter (fun D => componentMap I T a D = C)).card := by
  classical
  obtain ⟨hCcomp, x, hx, y, hy, hxy⟩ := Finset.mem_filter.mp hC
  have hxT := componentsOn_subset I T a hCcomp hx
  have hyT := componentsOn_subset I T a hCcomp hy
  let D := componentOn I T s x
  let E := componentOn I T s y
  have hD : D ∈ (componentsOn I T s).filter (fun D => componentMap I T a D = C) :=
    Finset.mem_filter.mpr ⟨componentOn_mem_componentsOn I T s hxT,
      (componentMap_coarsen I T s a hsa hxT).trans
        (componentOn_eq_of_mem I T a hCcomp hx)⟩
  have hE : E ∈ (componentsOn I T s).filter (fun D => componentMap I T a D = C) :=
    Finset.mem_filter.mpr ⟨componentOn_mem_componentsOn I T s hyT,
      (componentMap_coarsen I T s a hsa hyT).trans
        (componentOn_eq_of_mem I T a hCcomp hy)⟩
  have hDE : D ≠ E := fun he => hxy ((componentOn_eq_iff I T s hyT).mp he)
  have hpair : ({D, E} : Finset (Finset V)) ⊆
      (componentsOn I T s).filter (fun D => componentMap I T a D = C) := by
    intro F hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact hD
    · exact (Finset.mem_singleton.mp hF) ▸ hE
  have hcard := Finset.card_le_card hpair
  simpa only [Finset.card_pair hDE] using hcard

theorem bad_fibers_card_le {A B : Type*} (S : Finset A) (T bad : Finset B)
    (f : A → B) (hmap : ∀ x ∈ S, f x ∈ T)
    (hsurj : ∀ y ∈ T, ∃ x ∈ S, f x = y) (hbadT : bad ⊆ T)
    (hbad : ∀ y ∈ bad, 2 ≤ (S.filter (fun x => f x = y)).card) :
    bad.card ≤ S.card - T.card := by
  classical
  have hsum : S.card = ∑ y ∈ T, (S.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hpoint (y : B) (hy : y ∈ T) :
      1 + (if y ∈ bad then 1 else 0) ≤ (S.filter (fun x => f x = y)).card := by
    by_cases hby : y ∈ bad
    · simpa only [hby, ↓reduceIte] using hbad y hby
    · obtain ⟨x, hx, hxy⟩ := hsurj y hy
      have hpos : 0 < (S.filter (fun x => f x = y)).card := Finset.card_pos.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, hxy⟩⟩
      simp only [hby, ↓reduceIte, Nat.add_zero]
      omega
  have hbadSum : (∑ y ∈ T, if y ∈ bad then (1 : ℕ) else 0) = bad.card := by
    rw [← Finset.sum_filter]
    have he : T.filter (fun y => y ∈ bad) = bad := by
      ext y
      exact ⟨fun h => (Finset.mem_filter.mp h).2,
        fun h => Finset.mem_filter.mpr ⟨hbadT h, h⟩⟩
    simp [he]
  have hlower := Finset.sum_le_sum hpoint
  rw [← hsum, Finset.sum_add_distrib, hbadSum] at hlower
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hlower
  omega

theorem phaseBad_card_le_drop (I : Instance V) (T : Finset V) (s a : ℝ) (hsa : s ≤ a) :
    (phaseBad I T s a).card ≤ (componentsOn I T s).card - (componentsOn I T a).card :=
  bad_fibers_card_le (componentsOn I T s) (componentsOn I T a) (phaseBad I T s a)
    (componentMap I T a)
    (fun _ hD => componentMap_coarsen_mem I T s a hsa hD)
    (fun _ hC => componentMap_coarsen_surjective I T s a hsa hC)
    (phaseBad_subset I T s a)
    (fun _ hC => by
      convert phaseBad_fiber I T s a hsa hC using 1 <;> congr 1 <;> ext D <;> simp)

/-- Exact components that split under the pulled-back retained partition. -/
noncomputable def nonpersistent (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (a : ℝ) : Finset (Finset V) :=
  (componentsOn I T a).filter (fun C =>
    ∃ x ∈ C, ∃ y ∈ C, ¬ (thresholdOn I N a).Reachable
      (project I T N ρ hc x) (project I T N ρ hc y))

theorem nonpersistent_subset_phaseBad (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ) :
    nonpersistent I T N ρ hc a ⊆ phaseBad I T (a - 2 * ρ) a := by
  classical
  intro C hC
  obtain ⟨hCcomp, x, hx, y, hy, hn⟩ := Finset.mem_filter.mp hC
  exact Finset.mem_filter.mpr ⟨hCcomp, x, hx, y, hy,
    fun h => hn (project_reachable I T N ρ hc hρ a h)⟩

/-- The persistence-failure count is bounded by an exact-terminal phase drop,
uniformly over every cover. No conditioning or shift independence is used. -/
theorem nonpersistent_card_le_drop (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hρ : 0 ≤ ρ) (a : ℝ) :
    (nonpersistent I T N ρ hc a).card ≤
      (componentsOn I T (a - 2 * ρ)).card - (componentsOn I T a).card :=
  (Finset.card_le_card (nonpersistent_subset_phaseBad I T N ρ hc hρ a)).trans
    (phaseBad_card_le_drop I T (a - 2 * ρ) a (by linarith))

theorem pullback_eq_of_not_phaseBad (I : Instance V) (T N : Finset V) (ρ : ℝ)
    (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {C : Finset V} (hC : C ∈ componentsOn I T a)
    (hgood : C ∉ phaseBad I T (a - 2 * ρ) a) {x : V} (hx : x ∈ C) :
    pullbackComponent I T N ρ hc a x = C := by
  classical
  have hxT := componentsOn_subset I T a hC hx
  apply Finset.Subset.antisymm
  · intro y hy
    have h := (component_sandwich I T N ρ hc hNT hρ a hρa hxT).2 hy
    rwa [componentOn_eq_of_mem I T a hC hx] at h
  · intro y hy
    have hxy : (thresholdOn I T (a - 2 * ρ)).Reachable x y := by
      by_contra hn
      exact hgood (Finset.mem_filter.mpr ⟨hC, x, hx, y, hy, hn⟩)
    exact Finset.mem_filter.mpr ⟨componentsOn_subset I T a hC hy,
      project_reachable I T N ρ hc hρ a hxy⟩

/-- Away from the deterministic terminal phase-bad set, the corresponding
retained component is exactly the intersection of the exact component with
the retained set. -/
theorem retained_component_eq_inter_of_not_phaseBad (I : Instance V)
    (T N : Finset V) (ρ : ℝ) (hc : CoverOn I T N ρ) (hNT : N ⊆ T) (hρ : 0 ≤ ρ)
    (a : ℝ) (hρa : ρ < a) {C : Finset V} (hC : C ∈ componentsOn I T a)
    (hgood : C ∉ phaseBad I T (a - 2 * ρ) a) {x : V} (hx : x ∈ C) :
    componentOn I N a (project I T N ρ hc x) = N ∩ C := by
  classical
  have he := pullback_eq_of_not_phaseBad I T N ρ hc hNT hρ a hρa hC hgood hx
  ext y
  constructor
  · intro hy
    obtain ⟨hyN, hxy⟩ := (mem_componentOn I N a _ y).mp hy
    refine Finset.mem_inter.mpr ⟨hyN, ?_⟩
    rw [← he]
    apply Finset.mem_filter.mpr
    exact ⟨hNT hyN, by simpa only [project_fix I T N ρ hc hyN] using hxy⟩
  · intro hy
    obtain ⟨hyN, hyC⟩ := Finset.mem_inter.mp hy
    rw [← he] at hyC
    have hxy := (Finset.mem_filter.mp hyC).2
    rw [project_fix I T N ρ hc hyN] at hxy
    exact (mem_componentOn I N a _ y).mpr ⟨hyN, hxy⟩

end SteinerUpperBound.Covers.Geometry

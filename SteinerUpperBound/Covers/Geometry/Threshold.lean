module

public import SteinerUpperBound.Model

@[expose] public section

namespace SteinerUpperBound.Covers.Geometry

open scoped Classical BigOperators

variable {V : Type*}

/-- Strict threshold edges on an explicit finite vertex set. Vertices outside
the set are isolated and do not occur in `componentsOn`. -/
noncomputable def thresholdOn (I : Instance V) (S : Finset V) (a : ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => x ∈ S ∧ y ∈ S ∧ I.distance x y < a)

theorem thresholdOn_adj (I : Instance V) (S : Finset V) (a : ℝ) (x y : V) :
    (thresholdOn I S a).Adj x y ↔
      x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ I.distance x y < a := by
  simp [thresholdOn, SimpleGraph.fromRel, I.distance_comm, and_comm, and_left_comm, and_assoc]

theorem thresholdOn_mono (I : Instance V) {S T : Finset V} (hST : S ⊆ T)
    {a b : ℝ} (hab : a ≤ b) : thresholdOn I S a ≤ thresholdOn I T b := by
  intro x y hxy
  obtain ⟨hne, hx, hy, hd⟩ := (thresholdOn_adj I S a x y).mp hxy
  exact (thresholdOn_adj I T b x y).mpr ⟨hne, hST hx, hST hy, hd.trans_le hab⟩

theorem reachable_mono (I : Instance V) {S T : Finset V} (hST : S ⊆ T)
    {a b : ℝ} (hab : a ≤ b) {x y : V}
    (hxy : (thresholdOn I S a).Reachable x y) :
    (thresholdOn I T b).Reachable x y :=
  SimpleGraph.Reachable.mono (thresholdOn_mono I hST hab) hxy

noncomputable def componentOn (I : Instance V) (S : Finset V) (a : ℝ) (x : V) : Finset V :=
  S.filter (fun y => (thresholdOn I S a).Reachable x y)

noncomputable def componentsOn (I : Instance V) (S : Finset V) (a : ℝ) :
    Finset (Finset V) :=
  S.image (componentOn I S a)

theorem mem_componentOn (I : Instance V) (S : Finset V) (a : ℝ) (x y : V) :
    y ∈ componentOn I S a x ↔ y ∈ S ∧ (thresholdOn I S a).Reachable x y := by
  classical
  exact Finset.mem_filter

theorem componentOn_subset (I : Instance V) (S : Finset V) (a : ℝ) (x : V) :
    componentOn I S a x ⊆ S := Finset.filter_subset _ _

theorem componentOn_self (I : Instance V) (S : Finset V) (a : ℝ) {x : V}
    (hx : x ∈ S) : x ∈ componentOn I S a x :=
  (mem_componentOn I S a x x).mpr ⟨hx, SimpleGraph.Reachable.refl x⟩

theorem componentOn_eq_of_reachable (I : Instance V) (S : Finset V) (a : ℝ)
    {x y : V} (hxy : (thresholdOn I S a).Reachable x y) :
    componentOn I S a x = componentOn I S a y := by
  ext z
  rw [mem_componentOn, mem_componentOn]
  exact and_congr_right (fun _ =>
    ⟨fun h => hxy.symm.trans h, fun h => hxy.trans h⟩)

theorem componentOn_eq_iff (I : Instance V) (S : Finset V) (a : ℝ)
    {x y : V} (hy : y ∈ S) :
    componentOn I S a x = componentOn I S a y ↔
      (thresholdOn I S a).Reachable x y := by
  constructor
  · intro he
    have h := componentOn_self I S a hy
    rw [← he] at h
    exact ((mem_componentOn I S a x y).mp h).2
  · exact componentOn_eq_of_reachable I S a

theorem componentOn_mem_componentsOn (I : Instance V) (S : Finset V) (a : ℝ)
    {x : V} (hx : x ∈ S) : componentOn I S a x ∈ componentsOn I S a := by
  classical
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem componentsOn_nonempty (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) : C.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨x, componentOn_self I S a hx⟩

theorem componentsOn_subset (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) : C ⊆ S := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hC
  exact componentOn_subset I S a x

theorem componentOn_eq_of_mem (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) {x : V} (hx : x ∈ C) :
    componentOn I S a x = C := by
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hC
  exact (componentOn_eq_of_reachable I S a ((mem_componentOn I S a r x).mp hx).2).symm

theorem componentOn_pair_reachable (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) : (thresholdOn I S a).Reachable x y := by
  have he := componentOn_eq_of_mem I S a hC hx
  rw [← he] at hy
  exact ((mem_componentOn I S a x y).mp hy).2

theorem componentOn_closed (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) {t : ℝ} (hta : t ≤ a)
    {x y : V} (hx : x ∈ C) (hxy : (thresholdOn I S t).Adj x y) : y ∈ C := by
  have hyS := ((thresholdOn_adj I S t x y).mp hxy).2.2.1
  have hreach := reachable_mono I (Finset.Subset.refl S) hta hxy.reachable
  rw [← componentOn_eq_of_mem I S a hC hx]
  exact (mem_componentOn I S a x y).mpr ⟨hyS, hreach⟩

theorem reachable_restrict (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) {t : ℝ} (hta : t ≤ a)
    {x y : V} (hx : x ∈ C) (hxy : (thresholdOn I S t).Reachable x y) :
    (thresholdOn I C t).Reachable x y := by
  have hwalk : ∀ {u v : V}, (thresholdOn I S t).Walk u v → u ∈ C →
      (thresholdOn I C t).Reachable u v := by
    intro u v p
    induction p with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons u v z huv p ih =>
      intro hu
      have hv := componentOn_closed I S a hC hta hu huv
      have hedge : (thresholdOn I C t).Adj u v := by
        obtain ⟨hne, _, _, hd⟩ := (thresholdOn_adj I S t u v).mp huv
        exact (thresholdOn_adj I C t u v).mpr ⟨hne, hu, hv, hd⟩
      exact hedge.reachable.trans (ih hv)
  exact hxy.elim (fun p => hwalk p hx)

theorem componentOn_connected (I : Instance V) (S : Finset V) (a : ℝ)
    {C : Finset V} (hC : C ∈ componentsOn I S a) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) : (thresholdOn I C a).Reachable x y :=
  reachable_restrict I S a hC le_rfl hx (componentOn_pair_reachable I S a hC hx hy)

/-- An exact component map, defined on all finite sets to permit `Finset.image`.
Its empty-set value is irrelevant on the component families. -/
noncomputable def componentMap (I : Instance V) (T : Finset V) (a : ℝ)
    (C : Finset V) : Finset V :=
  if hC : C.Nonempty then componentOn I T a (Classical.choose hC) else ∅

theorem componentMap_eq (I : Instance V) (T : Finset V) (a : ℝ)
    {S C : Finset V} (hC : C ∈ componentsOn I S a) (hST : S ⊆ T)
    {x : V} (hx : x ∈ C) :
    componentMap I T a C = componentOn I T a x := by
  have hn := componentsOn_nonempty I S a hC
  have hrep := Classical.choose_spec hn
  have hr := componentOn_pair_reachable I S a hC hrep hx
  rw [componentMap, dif_pos hn]
  exact componentOn_eq_of_reachable I T a (reachable_mono I hST le_rfl hr)

theorem componentMap_mem (I : Instance V) (T : Finset V) (a : ℝ)
    {S C : Finset V} (hST : S ⊆ T) (hC : C ∈ componentsOn I S a) :
    componentMap I T a C ∈ componentsOn I T a := by
  obtain ⟨x, hx⟩ := componentsOn_nonempty I S a hC
  rw [componentMap_eq I T a hC hST hx]
  exact componentOn_mem_componentsOn I T a (hST (componentsOn_subset I S a hC hx))

end SteinerUpperBound.Covers.Geometry

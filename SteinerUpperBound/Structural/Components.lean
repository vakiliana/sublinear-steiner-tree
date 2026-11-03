module

public import SteinerUpperBound.Structural.Statistics

@[expose] public section

namespace SteinerUpperBound.Structural

open scoped Classical BigOperators

variable {V : Type*} [Fintype V]

theorem component_ne_of_not_reachable (I : Instance V) (a : ℝ) {x y : V}
    (hy : y ∈ I.terminals) (hxy : ¬ (threshold I a).Reachable x y) :
    component I a x ≠ component I a y := by
  intro he
  have hym : y ∈ component I a x := by rw [he]; exact component_self I a hy
  exact hxy ((mem_component I a x y).mp hym).2

theorem component_mem_components (I : Instance V) (a : ℝ) {x : V}
    (hx : x ∈ I.terminals) : component I a x ∈ components I a :=
  Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem component_eq_of_member (I : Instance V) (a : ℝ) {C : Finset V}
    (hC : C ∈ components I a) {x : V} (hx : x ∈ C) :
    C = component I a x := by
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hC
  exact component_eq_of_reachable I a ((mem_component I a y x).mp hx).2

theorem component_mem_row (I : Instance V) (a : ℝ) (v : V) {x : V}
    (hx : x ∈ I.terminals) (hd : I.distance v x ≤ 3 * a / 5) :
    component I a x ∈ row I a v :=
  Finset.mem_filter.mpr ⟨component_mem_components I a hx, x, component_self I a hx, hd⟩

theorem row_eligible_of_three (I : Instance V) (a : ℝ) (v : V) {x y z : V}
    (hx : x ∈ I.terminals) (hy : y ∈ I.terminals) (hz : z ∈ I.terminals)
    (hdx : I.distance v x ≤ 3 * a / 5) (hdy : I.distance v y ≤ 3 * a / 5)
    (hdz : I.distance v z ≤ 3 * a / 5)
    (hxy : ¬ (threshold I a).Reachable x y)
    (hxz : ¬ (threshold I a).Reachable x z)
    (hyz : ¬ (threshold I a).Reachable y z) : v ∈ eligible I a := by
  classical
  have hCxy := component_ne_of_not_reachable I a hy hxy
  have hCxz := component_ne_of_not_reachable I a hz hxz
  have hCyz := component_ne_of_not_reachable I a hz hyz
  have hsub : {component I a x, component I a y, component I a z} ⊆ row I a v := by
    intro C hC
    simp only [Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with rfl | rfl | rfl
    · exact component_mem_row I a v hx hdx
    · exact component_mem_row I a v hy hdy
    · exact component_mem_row I a v hz hdz
  have hcard := Finset.card_le_card hsub
  have hthree : ({component I a x, component I a y, component I a z} : Finset (Finset V)).card = 3 := by
    simp [Finset.card_insert_of_notMem, hCxy, hCxz, hCyz]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩

end SteinerUpperBound.Structural

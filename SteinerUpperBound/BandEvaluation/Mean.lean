module

public import SteinerUpperBound.BandEvaluation.Guarded
public import SteinerUpperBound.SavingScores.Partition
public import SteinerUpperBound.Covers.Rejection

@[expose] public section

namespace SteinerUpperBound.BandEvaluation

open SteinerLowerBound QueryProgram Covers.Geometry
open scoped Classical BigOperators

variable {V Q : Type*} [Fintype V]

noncomputable def smallBandSum (I : Instance V) (N : Finset V) (a rho tau : ℝ) (B : ℕ) : ℝ :=
  ∑ C ∈ (componentsOn I N a).filter (fun C => C.card ≤ B), Band.score I C a rho tau

abbrev Parts (I : Instance V) (N : Finset V) (a : ℝ) := ↥(componentsOn I N a)

noncomputable def componentPart (I : Instance V) (N : Finset V) (a : ℝ) : ↥N → Parts I N a :=
  fun x => ⟨componentOn I N a x.val, componentOn_mem_componentsOn I N a x.property⟩

omit [Fintype V] in
theorem componentPart_surjective (I : Instance V) (N : Finset V) (a : ℝ) :
    Function.Surjective (componentPart I N a) := by
  intro C
  obtain ⟨x, hx⟩ := componentsOn_nonempty I N a C.property
  refine ⟨⟨x, componentsOn_subset I N a C.property hx⟩, ?_⟩
  exact Subtype.ext (componentOn_eq_of_mem I N a C.property hx)

omit [Fintype V] in
theorem componentPart_fiber (I : Instance V) (N : Finset V) (a : ℝ) (C : Parts I N a) :
    SavingScores.partSize (componentPart I N a) C = C.val.card := by
  classical
  let : DecidableEq (Parts I N a) := Classical.decEq _
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    have he := congrArg Subtype.val (Finset.mem_filter.mp hx).2
    exact he ▸ componentOn_self I N a x.property
  · intro x _ y _ he
    exact Subtype.ext he
  · intro x hx
    let x' : ↥N := ⟨x, componentsOn_subset I N a C.property hx⟩
    have he : componentPart I N a x' = C := Subtype.ext (componentOn_eq_of_mem I N a C.property hx)
    exact ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩

noncomputable def uniformPoints (N : Finset V) (hN : N.Nonempty) : Law ↥N := by
  letI : Nonempty ↥N := ⟨⟨hN.choose, hN.choose_spec⟩⟩
  exact Law.uniform _

omit [Fintype V] in
theorem uniformPoints_expect (N : Finset V) (hN : N.Nonempty) (f : V → ℝ) :
    (uniformPoints N hN).expect (fun x => f x.val) = (∑ x ∈ N, f x) / (N.card : ℝ) := by
  let : Nonempty ↥N := ⟨⟨hN.choose, hN.choose_spec⟩⟩
  change (Law.uniform ↥N).expect (fun x => f x.val) = _
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.sum_coe_sort] using
    SavingScores.uniform_expect (fun x : ↥N => f x.val)

theorem uniform_component_mean (I : Instance V) (N : Finset V) (hN : N.Nonempty)
    (a rho tau : ℝ) (B : ℕ) :
    (uniformPoints N hN).expect (fun x => pointScore I N a rho tau B x.val) =
      smallBandSum I N a rho tau B / (3 * a * N.card) := by
  classical
  let : Nonempty ↥N := ⟨⟨hN.choose, hN.choose_spec⟩⟩
  let w : Parts I N a → ℝ := fun C => if C.val.card ≤ B then Band.score I C.val a rho tau / (3 * a) else 0
  have hp (x : ↥N) : pointScore I N a rho tau B x.val =
      w (componentPart I N a x) / (SavingScores.partSize (componentPart I N a) (componentPart I N a x) : ℝ) := by
    rw [componentPart_fiber]
    dsimp only [w, componentPart, pointScore]
    split_ifs
    · rw [div_div]
    · simp
  have hs : (∑ C : Parts I N a, w C) = smallBandSum I N a rho tau B / (3 * a) := by
    change (∑ C : ↥(componentsOn I N a),
      (fun C : Finset V => if C.card ≤ B then Band.score I C a rho tau / (3 * a) else 0) C.val) = _
    rw [Finset.sum_coe_sort (componentsOn I N a)
      (fun C : Finset V => if C.card ≤ B then Band.score I C a rho tau / (3 * a) else 0)]
    simp only [smallBandSum, Finset.sum_filter, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro C _
    split_ifs <;> simp
  change (Law.uniform ↥N).expect (fun x => pointScore I N a rho tau B x.val) = _
  simp_rw [hp]
  rw [SavingScores.uniform_part_mean (componentPart I N a) (componentPart_surjective I N a) w, hs]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, div_div]

theorem smallBandSum_nonneg (I : Instance V) (N : Finset V) (a rho tau : ℝ) (B : ℕ) :
    0 ≤ smallBandSum I N a rho tau B :=
  Finset.sum_nonneg (fun C _ => Band.score_nonneg I C a rho tau)

variable {U : Type*} [Fintype U]

theorem uniformRetained_expect (p : U → Bool) (hp : (Covers.Rejection.retained p).Nonempty) (f : U → ℝ) :
    (Covers.Rejection.uniformRetained p hp).expect f =
      (∑ u ∈ Covers.Rejection.retained p, f u) / ((Covers.Rejection.retained p).card : ℝ) := by
  classical
  simp only [Law.expect, Covers.Rejection.uniformRetained, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  change (∑ u ∈ Covers.Rejection.retained p, ((Covers.Rejection.retained p).card : ℝ)⁻¹ * f u) = _
  rw [← Finset.mul_sum]
  ring

variable {n : ℕ}

theorem labels_in_terminals (label : U → Fin n) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) (u : U) : label u ∈ terminals := by
  have hh : label u ∈ FiniteMST.labels label := (FiniteMST.mem_labels label _).mpr ⟨u, rfl⟩
  rw [henum] at hh
  exact List.mem_toFinset.mp hh

theorem retained_labels_image (b : Q → Bool) (label : U → Fin n) (key : Fin n → Q)
    (terminals : List (Fin n)) (henum : FiniteMST.labels label = terminals.toFinset) :
    (Covers.Rejection.retained (fun u => b (key (label u)))).image label = retainedSet b key terminals := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hb : b (key (label u)) = true := (Finset.mem_filter.mp hu).2
    refine Finset.mem_filter.mpr ⟨?_, hb⟩
    simpa only [List.mem_toFinset] using labels_in_terminals label terminals henum u
  · intro hx
    obtain ⟨hxT, hxB⟩ := Finset.mem_filter.mp hx
    have hxl : x ∈ FiniteMST.labels label := by
      rw [henum]
      simpa only [List.mem_toFinset] using hxT
    obtain ⟨u, hu⟩ := (FiniteMST.mem_labels label x).mp hxl
    refine Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hu⟩
    simpa only [hu] using hxB

theorem retained_labels_card (b : Q → Bool) (label : U → Fin n) (hlabel : Function.Injective label)
    (key : Fin n → Q) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset) :
    (Covers.Rejection.retained (fun u => b (key (label u)))).card = (retainedSet b key terminals).card := by
  have hh := Finset.card_image_of_injective (Covers.Rejection.retained (fun u => b (key (label u)))) hlabel
  rw [retained_labels_image b label key terminals henum] at hh
  exact hh.symm

theorem uniform_retained_mean (I : Instance (Fin n)) (b : Q → Bool) (label : U → Fin n)
    (hlabel : Function.Injective label) (key : Fin n → Q) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (a rho tau : ℝ) (B : ℕ) :
    (Covers.Rejection.uniformRetained (fun u => b (key (label u))) hb).expect
      (fun u => pointScore I (retainedSet b key terminals) a rho tau B (label u)) =
      smallBandSum I (retainedSet b key terminals) a rho tau B /
        (3 * a * (Covers.Rejection.retained (fun u => b (key (label u)))).card) := by
  classical
  let p := fun u => b (key (label u))
  let N := retainedSet b key terminals
  have himage : (Covers.Rejection.retained p).image label = N := retained_labels_image b label key terminals henum
  have hN : N.Nonempty := himage ▸ hb.image label
  have hcard : (Covers.Rejection.retained p).card = N.card := by
    have hh := Finset.card_image_of_injective (Covers.Rejection.retained p) hlabel
    rw [himage] at hh
    exact hh.symm
  have hsum : (∑ u ∈ Covers.Rejection.retained p, pointScore I N a rho tau B (label u)) =
      ∑ x ∈ N, pointScore I N a rho tau B x := by
    rw [← himage, Finset.sum_image]
    intro u _ v _ h
    exact hlabel h
  have hmean := uniform_component_mean I N hN a rho tau B
  rw [uniformPoints_expect] at hmean
  rw [uniformRetained_expect]
  change (∑ u ∈ Covers.Rejection.retained p, pointScore I N a rho tau B (label u)) /
    ((Covers.Rejection.retained p).card : ℝ) = _
  rw [hsum, hcard]
  simpa only [hcard] using hmean

theorem uniform_retained_mean_points (I : Instance (Fin n)) (b : Q → Bool) (label : U → Fin n)
    (hlabel : Function.Injective label) (key : Fin n → Q) (terminals : List (Fin n))
    (henum : FiniteMST.labels label = terminals.toFinset)
    (hb : (Covers.Rejection.retained (fun u => b (key (label u)))).Nonempty)
    (a rho tau : ℝ) (B : ℕ) :
    (Covers.Rejection.uniformRetained (fun u => b (key (label u))) hb).expect
      (fun u => pointScore I (retainedSet b key terminals) a rho tau B (label u)) =
      smallBandSum I (retainedSet b key terminals) a rho tau B /
        (3 * a * (retainedSet b key terminals).card) := by
  simpa only [retained_labels_card b label hlabel key terminals henum] using
    uniform_retained_mean I b label hlabel key terminals henum hb a rho tau B

end SteinerUpperBound.BandEvaluation

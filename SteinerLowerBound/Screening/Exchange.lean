module

public import SteinerLowerBound.Screening.Locality

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

inductive Query (T C : Type*)
  | tt : T → T → Query T C
  | ct : C → T → Query T C
  | cc : C → C → Query T C
  deriving DecidableEq, Fintype

inductive Reply
  | diagonal | cluster | unit | far
  deriving DecidableEq

instance : Fintype Reply where
  elems := {.diagonal, .cluster, .unit, .far}
  complete x := by cases x <;> simp

def centerHistory {T C : Type*} (h : List (Query T C)) : List (C × T) :=
  h.filterMap fun
    | .ct c u => some (c, u)
    | _ => none

theorem mem_centerHistory {T C : Type*} (h : List (Query T C)) (c : C) (u : T) :
    (c, u) ∈ centerHistory h ↔ Query.ct c u ∈ h := by
  induction h with
  | nil => simp [centerHistory]
  | cons a h ih => cases a <;> simp_all [centerHistory, List.filterMap_cons]

theorem centerHistory_take_subset {T C : Type*} (h : List (Query T C)) (n : ℕ) :
    ∀ z ∈ centerHistory (h.take n), z ∈ centerHistory h := by
  rintro ⟨c, u⟩ hz
  exact (mem_centerHistory h c u).mpr
    (List.mem_of_mem_take ((mem_centerHistory _ c u).mp hz))

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

abbrev Terminal (S G I : Type*) := S ⊕ (G × I)

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

def specialPosition : Terminal S G I → Prop
  | .inl _ => True
  | .inr _ => False

def clusterPosition : Terminal S G I → Option G
  | .inl _ => none
  | .inr (g, _) => some g

def SameCluster (π : Equiv.Perm (Terminal S G I)) (u v : Terminal S G I) : Prop :=
  ∃ g, clusterPosition (π u) = some g ∧ clusterPosition (π v) = some g

noncomputable def specialLabels (π : Equiv.Perm (Terminal S G I)) :
    Finset (Terminal S G I) :=
  (Finset.univ.map (Function.Embedding.inl : S ↪ Terminal S G I)).map π.symm.toEmbedding

noncomputable def ordinaryLabels (π : Equiv.Perm (Terminal S G I)) :
    Finset (Terminal S G I) :=
  (Finset.univ.map (Function.Embedding.inr : G × I ↪ Terminal S G I)).map π.symm.toEmbedding

noncomputable def clusterLabels (π : Equiv.Perm (Terminal S G I)) (g : G) :
    Finset (Terminal S G I) :=
  Finset.univ.map
    ⟨fun i : I => π.symm (.inr (g, i)), by
      intro i j hij
      exact (Prod.mk.inj (Sum.inr_injective (π.symm.injective hij))).2⟩

@[simp]
theorem mem_specialLabels (π : Equiv.Perm (Terminal S G I)) (u : Terminal S G I) :
    u ∈ specialLabels π ↔ specialPosition (π u) := by
  classical
  unfold specialLabels
  rw [Finset.mem_map_equiv]
  simp only [Equiv.symm_symm, Finset.mem_map, Finset.mem_univ, true_and]
  change (∃ s : S, Sum.inl s = π u) ↔ specialPosition (π u)
  cases π u <;> simp [specialPosition]

@[simp]
theorem mem_ordinaryLabels (π : Equiv.Perm (Terminal S G I)) (u : Terminal S G I) :
    u ∈ ordinaryLabels π ↔ ¬specialPosition (π u) := by
  classical
  unfold ordinaryLabels
  rw [Finset.mem_map_equiv]
  simp only [Equiv.symm_symm, Finset.mem_map, Finset.mem_univ, true_and]
  change (∃ p : G × I, Sum.inr p = π u) ↔ ¬specialPosition (π u)
  cases π u <;> simp [specialPosition]

@[simp]
theorem card_specialLabels (π : Equiv.Perm (Terminal S G I)) :
    (specialLabels π).card = Fintype.card S := by simp [specialLabels]

@[simp]
theorem card_ordinaryLabels (π : Equiv.Perm (Terminal S G I)) :
    (ordinaryLabels π).card = Fintype.card G * Fintype.card I := by simp [ordinaryLabels]

@[simp]
theorem card_clusterLabels (π : Equiv.Perm (Terminal S G I)) (g : G) :
    (clusterLabels π g).card = Fintype.card I := by simp [clusterLabels]

@[simp]
theorem mem_clusterLabels (π : Equiv.Perm (Terminal S G I)) (g : G)
    (u : Terminal S G I) :
    u ∈ clusterLabels π g ↔ clusterPosition (π u) = some g := by
  classical
  simp only [clusterLabels, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨i, hi⟩
    have he : π u = .inr (g, i) := (Equiv.symm_apply_eq π).mp hi |>.symm
    simp [he, clusterPosition]
  · intro hu
    cases he : π u with
    | inl s => simp [he, clusterPosition] at hu
    | inr p =>
        have hp : p.1 = g := by simpa [he, clusterPosition] using hu
        exact ⟨p.2, (Equiv.symm_apply_eq π).mpr (by simp [← hp, he])⟩

noncomputable def queryAnswer (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C)) :
    Query (Terminal S G I) C → Reply
  | .tt u v => if u = v then .diagonal else if SameCluster π u v then .cluster else .far
  | .ct c u =>
      if TwoAnchor.answer (relabel π F) (relabel π H) (centerHistory h) c u then .unit
      else .far
  | .cc c c' => if c = c' then .diagonal else .far

noncomputable def observations (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C)) :
    Fin h.length → Reply :=
  fun i => queryAnswer π F H (h.take i.val) (h.get i)

theorem observations_congr (π π' : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (hTT : ∀ u v, Query.tt u v ∈ h → u ≠ v →
      (SameCluster π u v ↔ SameCluster π' u v))
    (hF : TwoAnchor.AgreesOn (centerHistory h) (relabel π F) (relabel π' F))
    (hH : TwoAnchor.AgreesOn (centerHistory h) (relabel π H) (relabel π' H)) :
    observations π F H h = observations π' F H h := by
  classical
  funext i
  have hi : h.get i ∈ h := List.get_mem h i
  cases he : h.get i with
  | tt u v =>
      by_cases huv : u = v
      · simp only [observations, he, queryAnswer, huv, ↓reduceIte]
      · simp only [observations, he, queryAnswer, huv, ↓reduceIte,
          hTT u v (he ▸ hi) huv]
  | cc c c' => simp only [observations, he, queryAnswer]
  | ct c u =>
      have hm : (c, u) ∈ centerHistory h := (mem_centerHistory h c u).mpr (he ▸ hi)
      have restrict {L L' : C → Finset (Terminal S G I)}
          (hL : TwoAnchor.AgreesOn (centerHistory h) L L') :
          TwoAnchor.AgreesOn (centerHistory (h.take i.val)) L L' :=
        ⟨hL.1, fun c u hu => hL.2 c u (centerHistory_take_subset h _ _ hu)⟩
      have ha := TwoAnchor.answer_congr (restrict hF) (restrict hH) c u
        (hF.2 c u hm) (hH.2 c u hm)
      simp only [observations, he, queryAnswer, ha]

section WeightedSwitches

variable {T Ξ : Type*} [Fintype T] [Fintype Ξ]

noncomputable def shuffledLaw (μ : Law Ξ) : Law (Ξ × Equiv.Perm T) where
  mass ω := μ.mass ω.1 * (Fintype.card (Equiv.Perm T) : ℝ)⁻¹
  nonneg ω := mul_nonneg (μ.nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg _))
  total := by
    have hn : (Fintype.card (Equiv.Perm T) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = ∑ ξ, μ.mass ξ := by
        apply Finset.sum_congr rfl
        intro ξ _
        field_simp
      _ = 1 := μ.total

noncomputable def switch (ω : Ξ × Equiv.Perm T) (u x : T) : Ξ × Equiv.Perm T :=
  (ω.1, exchangeLabels ω.2 u x)

@[simp]
theorem switch_involutive (ω : Ξ × Equiv.Perm T) (u x : T) :
    switch (switch ω u x) u x = ω := by simp [switch]

theorem switch_injective (ω : Ξ × Equiv.Perm T) (u : T) :
    Function.Injective (switch ω u) := by
  intro x y he
  exact exchangeLabels_injective ω.2 u (congrArg Prod.snd he)

theorem shuffledLaw_switch_mass (μ : Law Ξ) (ω : Ξ × Equiv.Perm T) (u x : T) :
    (shuffledLaw (T := T) μ).mass (switch ω u x) = (shuffledLaw (T := T) μ).mass ω := rfl

theorem switching (μ : Law Ξ) (E P : Set (Ξ × Equiv.Perm T)) (u : T)
    (good inverse : Ξ × Equiv.Perm T → Finset T) (F B : ℝ)
    (hF : ∀ ω ∈ E, F ≤ (good ω).card)
    (hB : ∀ z, ((inverse z).card : ℝ) ≤ B)
    (hpreserve : ∀ ω ∈ E, ∀ x ∈ good ω, switch ω u x ∈ P)
    (hinverse : ∀ ω ∈ E, ∀ x ∈ good ω, x ∈ inverse (switch ω u x)) :
    F * (shuffledLaw (T := T) μ).prob E ≤ B * (shuffledLaw (T := T) μ).prob P := by
  classical
  let moves := fun ω => (good ω).image (switch ω u)
  apply Law.exchange _ E P moves F B
  · intro ω hω
    simpa [moves, Finset.card_image_of_injective _ (switch_injective ω u)] using hF ω hω
  · intro z
    have hs : (Finset.univ.filter fun ω => ω ∈ E ∧ z ∈ moves ω) ⊆
        (inverse z).image (switch z u) := by
      intro ω hω
      obtain ⟨hE, hmove⟩ := (Finset.mem_filter.mp hω).2
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hmove
      have hx' : x ∈ inverse z := he ▸ hinverse ω hE x hx
      apply Finset.mem_image.mpr
      refine ⟨x, hx', ?_⟩
      rw [← he, switch_involutive]
    have hc : (Finset.univ.filter fun ω => ω ∈ E ∧ z ∈ moves ω).card ≤
        (inverse z).card := (Finset.card_le_card hs).trans Finset.card_image_le
    have hc' : ((Finset.univ.filter fun ω => ω ∈ E ∧ z ∈ moves ω).card : ℝ) ≤
        ((inverse z).card : ℝ) := by exact_mod_cast hc
    convert hc'.trans (hB z) using 1
    apply congrArg (fun s : Finset (Ξ × Equiv.Perm T) => (s.card : ℝ))
    ext ω
    simp
  · intro ω hω z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hpreserve ω hω x hx
  · intro ω _ z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    rfl

end WeightedSwitches

end Screening

end SteinerLowerBound

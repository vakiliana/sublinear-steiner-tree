module

public import SteinerUpperBound.TreeGeometry.Packing
public import SteinerLowerBound.IndependentTrials
public import SteinerLowerBound.Caching

@[expose] public section

namespace SteinerUpperBound.Covers

open SteinerLowerBound
open scoped Classical BigOperators

namespace ClosedRelation

variable {U : Type*} [Fintype U]

noncomputable def neighborhood (R : U → U → Prop) (x : U) : Finset U :=
  Finset.univ.filter (R x)

noncomputable def degree (R : U → U → Prop) (x : U) : ℕ :=
  (neighborhood R x).card

theorem degree_pos (R : U → U → Prop) (hrefl : ∀ x, R x x) (x : U) :
    0 < degree R x := by
  classical
  exact Finset.card_pos.mpr ⟨x, by simp [neighborhood, hrefl]⟩

/-- Minimum original degree deletion, with the original degrees kept fixed. -/
theorem reciprocal_packing (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (hsymm : Symmetric R) (S : Finset U) :
    ∃ P : Finset U, P ⊆ S ∧
      (P : Set U).Pairwise (fun x y => ¬ R x y) ∧
      (∑ x ∈ S, (degree R x : ℝ)⁻¹) ≤ (P.card : ℝ) := by
  classical
  suffices ∀ n, ∀ S : Finset U, S.card = n →
      ∃ P : Finset U, P ⊆ S ∧
        (P : Set U).Pairwise (fun x y => ¬ R x y) ∧
        (∑ x ∈ S, (degree R x : ℝ)⁻¹) ≤ (P.card : ℝ) from
    this S.card S rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hcard
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx, hmin⟩ := S.exists_min_image (degree R) hS
      let D := S.filter (R x)
      let E := S.filter (fun y => ¬ R x y)
      have hES : E ⊆ S := Finset.filter_subset _ _
      have hxE : x ∉ E := by simp [E, hrefl]
      have hlt : E.card < n := by
        rw [← hcard]
        apply Finset.card_lt_card
        exact Finset.ssubset_iff_subset_ne.mpr ⟨hES, by
          intro he
          exact hxE (he ▸ hx)⟩
      obtain ⟨P, hPE, hPsep, hPsum⟩ := ih E.card hlt E rfl
      have hxP : x ∉ P := fun hp => hxE (hPE hp)
      have hdpos : (0 : ℝ) < degree R x := by
        exact_mod_cast degree_pos R hrefl x
      have hDcard : D.card ≤ degree R x := by
        apply Finset.card_le_card
        intro y hy
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
      have hDsum : (∑ y ∈ D, (degree R y : ℝ)⁻¹) ≤ 1 := by
        calc
          _ ≤ ∑ _y ∈ D, (degree R x : ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro y hy
            apply inv_anti₀ hdpos
            exact_mod_cast hmin y (Finset.mem_filter.mp hy).1
          _ = (D.card : ℝ) * (degree R x : ℝ)⁻¹ := by simp
          _ ≤ (degree R x : ℝ) * (degree R x : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hDcard) (by positivity)
          _ = 1 := mul_inv_cancel₀ hdpos.ne'
      refine ⟨insert x P, Finset.insert_subset_iff.mpr ⟨hx, hPE.trans hES⟩, ?_, ?_⟩
      · intro a ha b hb hab
        by_cases hax : a = x
        · subst a
          have hbP : b ∈ P := (Finset.mem_insert.mp hb).resolve_left (Ne.symm hab)
          exact (Finset.mem_filter.mp (hPE hbP)).2
        · have haP : a ∈ P := (Finset.mem_insert.mp ha).resolve_left hax
          by_cases hbx : b = x
          · subst b
            exact fun h => (Finset.mem_filter.mp (hPE haP)).2 (hsymm h)
          · exact hPsep haP ((Finset.mem_insert.mp hb).resolve_left hbx) hab
      · have hsplit :
            (∑ y ∈ D, (degree R y : ℝ)⁻¹) +
              (∑ y ∈ E, (degree R y : ℝ)⁻¹) =
                ∑ y ∈ S, (degree R y : ℝ)⁻¹ :=
          Finset.sum_filter_add_sum_filter_not S (R x) _
        rw [Finset.card_insert_of_notMem hxP, Nat.cast_add, Nat.cast_one]
        linarith
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end ClosedRelation

abbrev Terminal {V : Type*} (I : Instance V) := {x : V // x ∈ I.terminals}

def near {V : Type*} (I : Instance V) (r : ℝ) (x y : Terminal I) : Prop :=
  I.distance x.val y.val ≤ r

theorem near_refl {V : Type*} (I : Instance V) {r : ℝ} (hr : 0 ≤ r) :
    ∀ x, near I r x x := by
  intro x
  simpa [near, I.distance_self] using hr

theorem near_symm {V : Type*} (I : Instance V) (r : ℝ) : Symmetric (near I r) := by
  intro x y h
  simpa only [near, I.distance_comm x.val y.val] using h

theorem reciprocal_degree_bound {V : Type*} [Fintype V] (I : Instance V)
    (r : ℝ) (hr : 0 < r) :
    (∑ x : Terminal I, (ClosedRelation.degree (near I r) x : ℝ)⁻¹) ≤
      1 + 2 * I.mst / r := by
  classical
  obtain ⟨P, _, hsep, hsum⟩ := ClosedRelation.reciprocal_packing
    (near I r) (near_refl I hr.le) (near_symm I r) Finset.univ
  let Q : Finset V := P.image Subtype.val
  have hQT : Q ⊆ I.terminals := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    exact y.property
  have hQsep : (Q : Set V).Pairwise (fun x y => r < I.distance x y) := by
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    exact lt_of_not_ge (hsep ha hb (fun h => hxy (congrArg Subtype.val h)))
  have hcard : Q.card = P.card := Finset.card_image_of_injective _ Subtype.val_injective
  exact hsum.trans (by
    rw [← hcard]
    exact TreeGeometry.separated_terminal_packing_lt I Q hQT r hr hQsep)

end SteinerUpperBound.Covers

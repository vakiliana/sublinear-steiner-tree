module

public import SteinerUpperBound.SetSystem.Basic
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U : Type*}

structure IncidenceCap (allRows : Finset R) (rows : R → Finset U)
    (A : Finset U) (b : ℕ) where
  lists : U → Finset R
  sound : ∀ x ∈ A, ∀ r ∈ lists x, r ∈ allRows ∧ x ∈ rows r
  card_le : ∀ x ∈ A, (lists x).card ≤ b
  complete : ∀ x ∈ A, (lists x).card < b →
    ∀ r ∈ allRows, x ∈ rows r → r ∈ lists x

noncomputable def firstIncident (order : List R) (rows : R → Finset U)
    (b : ℕ) (x : U) : Finset R :=
  ((order.filter (fun r => x ∈ rows r)).take b).toFinset

noncomputable def orderedCap (order : List R) (horder : order.Nodup)
    (rows : R → Finset U) (A : Finset U) (b : ℕ) :
    IncidenceCap order.toFinset rows A b where
  lists := firstIncident order rows b
  sound := by
    classical
    intro x _ r hr
    have hh := List.mem_of_mem_take (List.mem_toFinset.mp hr)
    have hh' : r ∈ order ∧ x ∈ rows r := by simpa using hh
    exact ⟨List.mem_toFinset.mpr hh'.1, hh'.2⟩
  card_le := by
    classical
    intro x _
    exact (List.toFinset_card_le _).trans (List.length_take_le _ _)
  complete := by
    classical
    intro x _ hx r hr hxr
    let l := order.filter (fun r => x ∈ rows r)
    have hnd : l.Nodup := horder.filter _
    have hcard : (firstIncident order rows b x).card = min b l.length := by
      rw [firstIncident, List.toFinset_card_of_nodup (hnd.take (i := b)), List.length_take]
    have hlen : l.length ≤ b := by omega
    change r ∈ (l.take b).toFinset
    rw [List.take_of_length_le hlen]
    apply List.mem_toFinset.mpr
    simpa [l] using (show r ∈ order ∧ x ∈ rows r from
      ⟨List.mem_toFinset.mp hr, hxr⟩)

noncomputable def mutualGraph (A : Finset U) (E : Finset R)
    (L : U → Finset R) : SimpleGraph U where
  Adj x y := x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ ∃ r ∈ E, r ∈ L x ∧ r ∈ L y
  symm := ⟨by
    rintro x y ⟨hx, hy, hxy, r, hr, hrx, hry⟩
    exact ⟨hy, hx, hxy.symm, r, hr, hry, hrx⟩⟩
  loopless := ⟨by
    rintro x ⟨_, _, h, _⟩
    exact h rfl⟩

def IsIndependent (G : SimpleGraph U) (I : Finset U) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬G.Adj x y

theorem mutualCap_fiber_card_le (allRows E : Finset R) (rows : R → Finset U)
    (A : Finset U) (b : ℕ) (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (I : Finset U) (hIA : I ⊆ A)
    (hI : IsIndependent (mutualGraph A E cap.lists) I)
    (r : R) (hr : r ∈ allRows) :
    (I.filter (fun x => r ∈ cap.lists x)).card ≤ 2 := by
  classical
  by_cases hrE : r ∈ E
  · apply (show (I.filter (fun x => r ∈ cap.lists x)).card ≤ 1 from ?_).trans
      (by omega)
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hxI, hrx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyI, hry⟩ := Finset.mem_filter.mp hy
    by_contra hxy
    exact hI x hxI y hyI hxy ⟨hIA hxI, hIA hyI, hxy, r, hrE, hrx, hry⟩
  · have hsub : I.filter (fun x => r ∈ cap.lists x) ⊆ A ∩ rows r := by
      intro x hx
      obtain ⟨hxI, hrx⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_inter.mpr ⟨hIA hxI, (cap.sound x (hIA hxI) r hrx).2⟩
    exact (Finset.card_le_card hsub).trans (hineligible r hr hrE)

theorem mutualCap_incidence_sum_le (allRows E : Finset R) (rows : R → Finset U)
    (A : Finset U) (b : ℕ) (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (I : Finset U) (hIA : I ⊆ A)
    (hI : IsIndependent (mutualGraph A E cap.lists) I) :
    ∑ x ∈ I, (cap.lists x).card ≤ 2 * allRows.card := by
  classical
  have hlist (x : U) (hx : x ∈ I) :
      allRows.bipartiteAbove (fun x r => r ∈ cap.lists x) x = cap.lists x := by
    ext r
    simp only [Finset.mem_bipartiteAbove]
    exact ⟨And.right, fun hr => ⟨(cap.sound x (hIA hx) r hr).1, hr⟩⟩
  calc
    _ = ∑ x ∈ I, (allRows.bipartiteAbove (fun x r => r ∈ cap.lists x) x).card :=
      Finset.sum_congr rfl (fun x hx => congrArg Finset.card (hlist x hx).symm)
    _ = ∑ r ∈ allRows, (I.filter (fun x => r ∈ cap.lists x)).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow _
    _ ≤ ∑ _r ∈ allRows, 2 := Finset.sum_le_sum (fun r hr =>
      mutualCap_fiber_card_le allRows E rows A b cap hineligible I hIA hI r hr)
    _ = _ := by simp [Nat.mul_comm]

noncomputable def fullLists {allRows : Finset R} {rows : R → Finset U}
    {A : Finset U} {b : ℕ} (cap : IncidenceCap allRows rows A b) (I : Finset U) :
    Finset U := I.filter (fun x => (cap.lists x).card = b)

theorem mutualCap_full_card (allRows E : Finset R) (rows : R → Finset U)
    (A : Finset U) (b : ℕ) (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (I : Finset U) (hIA : I ⊆ A)
    (hI : IsIndependent (mutualGraph A E cap.lists) I) :
    b * (fullLists cap I).card ≤ 2 * allRows.card := by
  classical
  calc
    _ = ∑ x ∈ fullLists cap I, (cap.lists x).card := by
      calc
        _ = ∑ _x ∈ fullLists cap I, b := by simp [Nat.mul_comm]
        _ = _ := Finset.sum_congr rfl (fun x hx =>
          (Finset.mem_filter.mp hx).2.symm)
    _ ≤ ∑ x ∈ I, (cap.lists x).card :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ _ := mutualCap_incidence_sum_le allRows E rows A b cap hineligible I hIA hI

theorem mutualCap_nonfull_sparse (allRows E : Finset R) (rows : R → Finset U)
    (hE : E ⊆ allRows) (A : Finset U) (b : ℕ)
    (cap : IncidenceCap allRows rows A b) (I : Finset U) (hIA : I ⊆ A)
    (hI : IsIndependent (mutualGraph A E cap.lists) I) :
    ∀ r ∈ E, ((I \ fullLists cap I) ∩ rows r).card ≤ 1 := by
  classical
  intro r hr
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxJ, hxr⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyJ, hyr⟩ := Finset.mem_inter.mp hy
  obtain ⟨hxI, hxF⟩ := Finset.mem_sdiff.mp hxJ
  obtain ⟨hyI, hyF⟩ := Finset.mem_sdiff.mp hyJ
  have hxlt : (cap.lists x).card < b := by
    have hle := cap.card_le x (hIA hxI)
    have hne : (cap.lists x).card ≠ b :=
      fun he => hxF (Finset.mem_filter.mpr ⟨hxI, he⟩)
    omega
  have hylt : (cap.lists y).card < b := by
    have hle := cap.card_le y (hIA hyI)
    have hne : (cap.lists y).card ≠ b :=
      fun he => hyF (Finset.mem_filter.mpr ⟨hyI, he⟩)
    omega
  have hrx := cap.complete x (hIA hxI) hxlt r (hE hr) hxr
  have hry := cap.complete y (hIA hyI) hylt r (hE hr) hyr
  by_contra hxy
  exact hI x hxI y hyI hxy ⟨hIA hxI, hIA hyI, hxy, r, hr, hrx, hry⟩

theorem mutualCap_independent_bound (allRows E : Finset R) (rows : R → Finset U)
    (hE : E ⊆ allRows) (A : Finset U) (b : ℕ) (hb : 1 ≤ b)
    (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (I : Finset U) (hIA : I ⊆ A)
    (hI : IsIndependent (mutualGraph A E cap.lists) I) :
    saving E rows A ≤ (A.card : ℝ) - I.card + 2 * allRows.card / b := by
  classical
  have hs := saving_le_of_sparse E rows A (I \ fullLists cap I)
    (Finset.sdiff_subset.trans hIA)
    (mutualCap_nonfull_sparse allRows E rows hE A b cap I hIA hI)
  have hf := mutualCap_full_card allRows E rows A b cap hineligible I hIA hI
  have hf' : (b : ℝ) * (fullLists cap I).card ≤ 2 * (allRows.card : ℝ) := by
    exact_mod_cast hf
  have hb' : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hfdiv : ((fullLists cap I).card : ℝ) ≤ 2 * allRows.card / b :=
    (le_div_iff₀ hb').mpr (by nlinarith)
  have hd := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset (fun x => (cap.lists x).card = b) I)
  have hd' : ((I \ fullLists cap I).card : ℝ) + (fullLists cap I).card = I.card := by
    exact_mod_cast hd
  linarith

end SteinerUpperBound.SetSystem

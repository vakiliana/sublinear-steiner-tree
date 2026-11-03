module

public import SteinerUpperBound.ReusableSample.Procedure

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

noncomputable def acceptances {n : ℕ} (T : Fin n → Bool) : ℕ :=
  ∑ j, if T j then 1 else 0

theorem acceptances_succ {n : ℕ} (T : Fin (n + 1) → Bool) :
    acceptances T = (if T 0 then 1 else 0) + acceptances (fun j => T j.succ) := by
  exact Fin.sum_univ_succ _

noncomputable def selectedRows {n : ℕ} (T : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun j => T j = true

theorem card_selectedRows {n : ℕ} (T : Fin n → Bool) :
    (selectedRows T).card = acceptances T := by
  rw [selectedRows, Finset.card_filter, acceptances]

def tested : {n : ℕ} → ℕ → (Fin n → Bool) → Fin n → Prop
  | 0, _, _, j => Fin.elim0 j
  | _ + 1, t, T, j => Fin.cases (t ≠ 0)
      (tested (if T 0 then t - 1 else t) (fun i => T i.succ)) j

theorem not_tested_zero {n : ℕ} (T : Fin n → Bool) (j : Fin n) : ¬ tested 0 T j := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases (by simp [tested]) (fun k => ?_) j
      simpa only [tested, Fin.cases_succ, Nat.zero_sub, ite_self] using
        ih (fun i => T i.succ) k

theorem all_tested {n : ℕ} (T : Fin n → Bool) (t : ℕ) (h : acceptances T < t) :
    ∀ j, tested t T j := by
  induction n generalizing t with
  | zero => intro j; exact Fin.elim0 j
  | succ n ih =>
      rw [acceptances_succ] at h
      refine Fin.cases (by dsimp [tested]; omega) (fun j => ?_)
      dsimp [tested]
      apply ih
      cases hb : T 0 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

theorem accepted_tested {n : ℕ} (T : Fin n → Bool) (t : ℕ)
    (h : acceptances T ≤ t) (j : Fin n) (hj : T j = true) : tested t T j := by
  induction n generalizing t with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      rw [acceptances_succ] at h
      refine Fin.cases (fun hj => ?_) (fun k hj => ?_) j hj
      · dsimp [tested]
        simp only [hj, ↓reduceIte] at h
        omega
      · dsimp [tested]
        apply ih (fun i => T i.succ) _ _ k hj
        cases hb : T 0 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

section Sets

variable {U : Type*}

noncomputable def previousUnion :
    {n : ℕ} → (Fin n → Finset U) → (Fin n → Bool) → Finset U → Fin n → Finset U
  | 0, _, _, _, j => Fin.elim0 j
  | _ + 1, R, T, C, j => Fin.cases C
      (previousUnion (fun i => R i.succ) (fun i => T i.succ)
        (if T 0 then C ∪ R 0 else C)) j

noncomputable def fresh {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) (j : Fin n) : Finset U :=
  R j \ previousUnion R T C j

noncomputable def finalUnion :
    {n : ℕ} → (Fin n → Finset U) → (Fin n → Bool) → Finset U → Finset U
  | 0, _, _, C => C
  | _ + 1, R, T, C => finalUnion (fun i => R i.succ) (fun i => T i.succ)
      (if T 0 then C ∪ R 0 else C)

theorem mem_finalUnion {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) (x : U) :
    x ∈ finalUnion R T C ↔ x ∈ C ∨ ∃ j, T j = true ∧ x ∈ R j := by
  induction n generalizing C with
  | zero => simp [finalUnion]
  | succ n ih =>
      simp only [finalUnion, ih, Fin.exists_fin_succ]
      cases T 0 <;> simp only [Bool.false_eq_true, false_and, false_or,
        ↓reduceIte, true_and, Finset.mem_union, or_assoc]

theorem finalUnion_eq_biUnion {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) :
    finalUnion R T C = C ∪ (selectedRows T).biUnion R := by
  ext x
  simp only [mem_finalUnion, Finset.mem_union, Finset.mem_biUnion, selectedRows,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_previousUnion {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) (j : Fin n) (x : U) :
    x ∈ previousUnion R T C j ↔
      x ∈ C ∨ ∃ i, i < j ∧ T i = true ∧ x ∈ R i := by
  induction n generalizing C with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases ?_ (fun k => ?_) j
      · simp [previousUnion]
      · have hk : (0 : Fin (n + 1)) < k.succ := Nat.zero_lt_succ _
        simp only [previousUnion, Fin.cases_succ, ih, Fin.exists_fin_succ,
          hk, true_and, Fin.succ_lt_succ_iff]
        cases T 0 <;> simp only [Bool.false_eq_true, false_and, false_or,
          ↓reduceIte, true_and, Finset.mem_union, or_assoc]

theorem initial_subset_final {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) : C ⊆ finalUnion R T C := by
  induction n generalizing C with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
      simp only [finalUnion]
      have hc : C ⊆ if T 0 then C ∪ R 0 else C := by
        cases T 0 <;> simp
      exact hc.trans (ih _ _ _)

theorem row_subset_final {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) (j : Fin n) (hj : T j = true) : R j ⊆ finalUnion R T C := by
  induction n generalizing C with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases (fun hj => ?_) (fun k hj => ?_) j hj
      · simp only [finalUnion]
        rw [hj]
        simp only [↓reduceIte]
        exact Finset.subset_union_right.trans (initial_subset_final _ _ _)
      · exact ih (fun i => R i.succ) (fun i => T i.succ)
          (if T 0 then C ∪ R 0 else C) k hj

theorem previous_subset_final {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool)
    (C : Finset U) (j : Fin n) : previousUnion R T C j ⊆ finalUnion R T C := by
  induction n generalizing C with
  | zero => exact Fin.elim0 j
  | succ n ih =>
      refine Fin.cases (initial_subset_final R T C) (fun k => ?_) j
      exact ih _ _ _ k

theorem final_card {n : ℕ} (R : Fin n → Finset U) (T : Fin n → Bool) (C : Finset U) :
    (finalUnion R T C).card = C.card +
      ∑ j, if T j then (fresh R T C j).card else 0 := by
  induction n generalizing C with
  | zero => simp [finalUnion]
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      change (finalUnion (fun i => R i.succ) (fun i => T i.succ)
        (if T 0 then C ∪ R 0 else C)).card = _
      rw [ih]
      cases hb : T 0
      · simp only [fresh, previousUnion, Fin.cases_succ,
          hb, Bool.false_eq_true, ↓reduceIte, zero_add]
      · simp only [fresh, previousUnion, Fin.cases_succ, Fin.cases_zero, hb, ↓reduceIte]
        have hc := Finset.card_sdiff_add_card (R 0) C
        rw [Finset.union_comm] at hc
        change (C ∪ R 0).card + _ = C.card + ((R 0 \ C).card + _)
        omega

theorem accepts_cover [Fintype U] {n : ℕ} (R : Fin n → Finset U)
    (T : Fin n → Bool) (t : ℕ) (ht : 0 < t) (hc : acceptances T = t)
    (h : ∀ j, T j = true →
      (Fintype.card U : ℝ) / t ≤ (fresh R T ∅ j).card) :
    finalUnion R T ∅ = Finset.univ := by
  have hs : (t : ℝ) * ((Fintype.card U : ℝ) / t) ≤
      ∑ j, if T j then ((fresh R T ∅ j).card : ℝ) else 0 := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => show
        (if T j then ((Fintype.card U : ℝ) / t) else 0) ≤
          (if T j then ((fresh R T ∅ j).card : ℝ) else 0) from by
      cases hj : T j
      · simp
      · simpa only [hj, ↓reduceIte] using h j hj)
    have he : (∑ j, if T j then ((Fintype.card U : ℝ) / t) else 0) =
        (acceptances T : ℝ) * ((Fintype.card U : ℝ) / t) := by
      rw [acceptances, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      cases T j <;> simp
    rwa [he, hc] at hsum
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [mul_div_cancel₀ _ ht'] at hs
  have hcard := final_card R T ∅
  have hr : ((finalUnion R T ∅).card : ℝ) =
      ∑ j, if T j then ((fresh R T ∅ j).card : ℝ) else 0 := by
    rw [hcard]
    push_cast
    simp
  rw [← hr] at hs
  apply Finset.eq_univ_of_card
  exact le_antisymm (Finset.card_le_univ _) (by exact_mod_cast hs)

def Specification [Fintype U] {n : ℕ} (R : Fin n → Finset U) (t : ℕ)
    (T : Fin n → Bool) : Prop :=
  acceptances T ≤ t ∧
    (∀ j, T j = true → (Fintype.card U : ℝ) / t ≤ (fresh R T ∅ j).card) ∧
    ∀ j, ((R j \ finalUnion R T ∅).card : ℝ) ≤ 4 * Fintype.card U / t

theorem specification_of_decisions [Fintype U] {n : ℕ} (R : Fin n → Finset U)
    (T : Fin n → Bool) (t : ℕ) (ht : 0 < t) (hc : acceptances T ≤ t)
    (ha : ∀ j, T j = true → (Fintype.card U : ℝ) / t ≤ (fresh R T ∅ j).card)
    (hr : ∀ j, tested t T j → T j = false →
      ((fresh R T ∅ j).card : ℝ) ≤ 4 * Fintype.card U / t) :
    Specification R t T := by
  refine ⟨hc, ha, fun j => ?_⟩
  by_cases he : acceptances T = t
  · rw [accepts_cover R T t ht he ha]
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ (R j))]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hj := all_tested T t (lt_of_le_of_ne hc he)
    cases hb : T j
    · have hsub : R j \ finalUnion R T ∅ ⊆ fresh R T ∅ j :=
        Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (previous_subset_final _ _ _ j)
      have hc' : ((R j \ finalUnion R T ∅).card : ℝ) ≤ (fresh R T ∅ j).card := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc'.trans (hr j (hj j) hb)
    · rw [Finset.sdiff_eq_empty_iff_subset.mpr (row_subset_final R T ∅ j hb)]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity

end Sets

section Support

variable {U I : Type*} [Fintype I]

theorem rejectAll_support {n : ℕ} (T : Fin n → Bool)
    (h : 0 < (rejectAll n).law.mass T) : acceptances T = 0 := by
  induction n with
  | zero => simp [acceptances]
  | succ n ih =>
      have he : (rejectAll (n + 1)).law =
          (rejectAll n).law.map (Tree.prepend false) := by
        apply LawOperations.ext_mass
        intro v
        simp [rejectAll, Tree.law, zeroRate, Law.mix]
      rw [he] at h
      have hex : ∃ v, Tree.prepend false v = T ∧ 0 < (rejectAll n).law.mass v := by
        by_contra hn
        push Not at hn
        have hz : ((rejectAll n).law.map (Tree.prepend false)).mass T ≤ 0 := by
          apply Finset.sum_nonpos
          intro v _
          split_ifs with hv
          · exact hn v hv
          · rfl
        linarith
      obtain ⟨v, rfl, hv⟩ := hex
      simpa [acceptances_succ, Tree.prepend] using ih v hv

theorem node_support {n : ℕ} (p : Rate) (l r : Tree n) (T : Fin (n + 1) → Bool)
    (h : 0 < (Tree.node p l r).law.mass T) :
    (T 0 = true ∧ 0 < r.law.mass (fun i => T i.succ)) ∨
      (T 0 = false ∧ 0 < l.law.mass (fun i => T i.succ)) := by
  have hm (s : Tree n) (b : Bool) :
      (s.law.map (Tree.prepend b)).mass T =
        if T 0 = b then s.law.mass (fun i => T i.succ) else 0 := by
    unfold Law.map
    have he (v : Fin n → Bool) :
        Tree.prepend b v = T ↔ T 0 = b ∧ v = fun i => T i.succ := by
      constructor
      · intro hv
        have hh := congrFun hv 0
        have ht := funext fun i : Fin n => congrFun hv i.succ
        exact ⟨by simpa [Tree.prepend] using hh.symm, by simpa [Tree.prepend] using ht⟩
      · rintro ⟨hb, rfl⟩
        simpa only [Tree.prepend, Fin.tail_def, hb] using Fin.cons_self_tail T
    simp only [he, ite_and]
    by_cases hb : T 0 = b <;> simp [hb]
  change 0 < (p : ℝ) * (r.law.map (Tree.prepend true)).mass T +
    (1 - (p : ℝ)) * (l.law.map (Tree.prepend false)).mass T at h
  rw [hm, hm] at h
  cases hb : T 0
  · right
    refine ⟨rfl, ?_⟩
    simp only [hb, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add] at h
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr p.property.2) (le_of_not_gt hn)
    linarith
  · left
    refine ⟨rfl, ?_⟩
    simp only [hb, Bool.true_eq_false, ↓reduceIte, mul_zero, add_zero] at h
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos p.property.1 (le_of_not_gt hn)
    linarith

theorem poolTree_support (b H : ℝ) (X : I → Option U) {n : ℕ}
    (R : Fin n → Finset U) (t : ℕ) (C : Finset U) (T : Fin n → Bool)
    (h : 0 < (poolTree b H X R t C).law.mass T) : acceptances T ≤ t := by
  induction n generalizing t C with
  | zero => simp [acceptances]
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [poolTree, ht, ↓reduceIte] at h
        simp only [ht, rejectAll_support T h, le_refl]
      · simp only [poolTree, ht, ↓reduceIte] at h
        obtain (⟨hb, hh⟩ | ⟨hb, hh⟩) := node_support _ _ _ T h
        · have hi := ih (fun j => R j.succ) (t - 1) (C ∪ R 0) _ hh
          rw [acceptances_succ]
          simp only [hb, ↓reduceIte]
          omega
        · have hi := ih (fun j => R j.succ) t C _ hh
          rw [acceptances_succ]
          simpa only [hb, Bool.false_eq_true, ↓reduceIte, zero_add] using hi

noncomputable def membershipWork (Ns t : ℕ) {n : ℕ} (T : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun j => tested t T j).card * Ns

theorem membershipWork_le (Ns t : ℕ) {n : ℕ} (T : Fin n → Bool) :
    membershipWork Ns t T ≤ n * Ns := by
  exact Nat.mul_le_mul_right Ns (by
    simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) (tested t T))

end Support

end SteinerUpperBound.ReusableSample

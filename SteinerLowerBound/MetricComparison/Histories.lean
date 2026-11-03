module

public import SteinerLowerBound.MetricComparison.Observation
public import SteinerLowerBound.Sampling
public import SteinerLowerBound.TwoAnchor

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

structure History (S : Type*) where
  positive : Finset S
  negative : Finset S
  anchors : Finset S
  blocked : Finset S

namespace History

variable {S : Type*}

def initial : History S := ⟨∅, ∅, ∅, ∅⟩

def Valid (h : History S) : Prop :=
  Disjoint h.positive h.negative ∧
    h.anchors ⊆ h.positive ∧ h.anchors.card = min h.positive.card 2 ∧
    h.blocked ⊆ h.negative ∧ (h.positive.card ≤ 1 → h.blocked = ∅)

def Fresh (h : History S) (u : S) : Prop :=
  u ∉ h.positive ∧ u ∉ h.negative

noncomputable def update (h : History S) (u : S) (b : Bool) : History S :=
  if b then
    ⟨insert u h.positive, h.negative,
      if h.positive.card < 2 then insert u h.anchors else h.anchors,
      if h.positive.card = 1 then h.negative else h.blocked⟩
  else ⟨h.positive, insert u h.negative, h.anchors, h.blocked⟩

theorem valid_initial : (initial : History S).Valid := by
  simp [Valid, initial]

theorem anchors_eq (h : History S) (hv : h.Valid) (hp : h.positive.card ≤ 2) :
    h.anchors = h.positive := by
  apply Finset.eq_of_subset_of_card_le hv.2.1
  rw [hv.2.2.1, min_eq_left hp]

theorem update_valid (h : History S) (u : S) (b : Bool)
    (hv : h.Valid) (hf : h.Fresh u) : (h.update u b).Valid := by
  classical
  obtain ⟨hd, ha, hc, hb, hz⟩ := hv
  obtain ⟨hup, hun⟩ := hf
  cases b
  · simp only [update, Bool.false_eq_true, ↓reduceIte, Valid]
    refine ⟨Finset.disjoint_insert_right.mpr ⟨hup, hd⟩, ha, hc,
      hb.trans (Finset.subset_insert _ _), hz⟩
  · simp only [update, ↓reduceIte, Valid, Finset.card_insert_of_notMem hup]
    have hau : u ∉ h.anchors := fun hu => hup (ha hu)
    refine ⟨Finset.disjoint_insert_left.mpr ⟨hun, hd⟩, ?_, ?_, ?_, ?_⟩
    · split_ifs
      · exact Finset.insert_subset_insert _ ha
      · exact ha.trans (Finset.subset_insert _ _)
    · split_ifs with hp
      · rw [Finset.card_insert_of_notMem hau, hc]
        omega
      · rw [hc]
        omega
    · split_ifs
      · exact Finset.Subset.refl _
      · exact hb
    · intro hp
      have hp₀ : h.positive.card = 0 := by omega
      simp [hp₀, hz (by omega)]

@[reducible] noncomputable def memory (S : Type*) : Memory S (History S) where
  initial := initial
  update := update
  Valid := Valid
  Fresh := Fresh
  initial_valid := valid_initial
  update_valid := update_valid

def compatible (h : History S) (N : Finset S) : Prop :=
  h.positive ⊆ N ∧ Disjoint N h.negative

theorem compatible_update (h : History S) (u : S) (b : Bool) (N : Finset S) :
    (h.update u b).compatible N ↔ h.compatible N ∧ decide (u ∈ N) = b := by
  classical
  cases b <;>
    simp only [update, Bool.false_eq_true, ↓reduceIte, compatible,
      Finset.disjoint_insert_right, Finset.insert_subset_iff, decide_eq_false_iff_not,
      decide_eq_true_eq] <;> tauto

noncomputable def staticObserver {Ω : Type*} [Fintype S]
    (k : Setup S Ω) (w : S → Ω) : Observer (memory S) (State S k.d) where
  law := k.centerLaw w
  accepts h x := h.compatible (neighbors k.d x)
  answer x _ u := decide (u ∈ neighbors k.d x)
  initial_accepts x := by simp [compatible, memory, initial]
  transition h u b _ _ x := compatible_update h u b (neighbors k.d x)

def gatedCompatible (h : History S) (F J : Finset S) : Prop :=
  if h.positive.card ≤ 1 then h.compatible F
  else if h.positive.card = 2 then
    F = h.positive ∧ (Disjoint J h.blocked → Disjoint J h.negative)
  else F = h.anchors ∧ h.compatible J

noncomputable def gatedAnswer (h : History S) (F J : Finset S) (u : S) : Bool :=
  decide (u ∈ F ∨ (2 ≤ h.positive.card ∧ Disjoint J h.blocked ∧ u ∈ J))

theorem disjoint_of_subset_right {A B D : Finset S} (hd : Disjoint A B) (hD : D ⊆ B) :
    Disjoint A D := Finset.disjoint_of_subset_right hD hd

theorem insert_eq_of_two {F P : Finset S} {u : S}
    (hF : F.card ≤ 2) (hP : P.card = 1) (hu : u ∉ P)
    (hPF : P ⊆ F) (huF : u ∈ F) : F = insert u P := by
  classical
  have hs : insert u P ⊆ F := Finset.insert_subset_iff.mpr ⟨huF, hPF⟩
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  rw [Finset.card_insert_of_notMem hu, hP]
  exact hF

theorem gatedCompatible_update (h : History S) (u : S) (b : Bool)
    (hv : h.Valid) (hf : h.Fresh u) (F J : Finset S)
    (hF : F.card ≤ 2) (hFJ : F ⊆ J) :
    (h.update u b).gatedCompatible F J ↔
      h.gatedCompatible F J ∧ h.gatedAnswer F J u = b := by
  classical
  obtain ⟨hd, ha, hc, hb, hz⟩ := hv
  obtain ⟨hup, hun⟩ := hf
  have hcb : Disjoint J h.negative → Disjoint J h.blocked :=
    fun hd => disjoint_of_subset_right hd hb
  by_cases hp : h.positive.card ≤ 1
  · have hnactive : ¬2 ≤ h.positive.card := by omega
    cases b
    · simp only [update, Bool.false_eq_true, ↓reduceIte, gatedCompatible, hp,
        compatible, Finset.disjoint_insert_right, gatedAnswer, hnactive, false_and,
        or_false, decide_eq_false_iff_not]
      tauto
    · by_cases hp₀ : h.positive.card = 0
      · have hi : (insert u h.positive).card ≤ 1 := by
          rw [Finset.card_insert_of_notMem hup, hp₀]
        simp only [update, ↓reduceIte, gatedCompatible, hi, hp,
          compatible, Finset.insert_subset_iff, gatedAnswer, hnactive, false_and,
          or_false, decide_eq_true_eq]
        tauto
      · have hp₁ : h.positive.card = 1 := by omega
        have hi : (insert u h.positive).card = 2 := by
          rw [Finset.card_insert_of_notMem hup, hp₁]
        simp only [update, ↓reduceIte, gatedCompatible, hi, show ¬2 ≤ 1 by omega,
          hp₁, hp, compatible, gatedAnswer, hnactive, false_and, or_false,
          decide_eq_true_eq, ↓reduceIte]
        constructor
        · rintro ⟨he, _⟩
          subst F
          exact ⟨⟨Finset.subset_insert _ _,
            Finset.disjoint_insert_left.mpr ⟨hun, hd⟩⟩, Finset.mem_insert_self _ _⟩
        · rintro ⟨⟨hPF, _⟩, huF⟩
          exact ⟨insert_eq_of_two hF hp₁ hup hPF huF, fun h => h⟩
  · have hp₂ : 2 ≤ h.positive.card := by omega
    by_cases htwo : h.positive.card = 2
    · have he : h.anchors = h.positive :=
        anchors_eq h ⟨hd, ha, hc, hb, hz⟩ (by omega)
      cases b
      · simp only [update, Bool.false_eq_true, ↓reduceIte, gatedCompatible, hp, htwo,
          gatedAnswer, hp₂, show (2 : ℕ) ≤ 2 by omega, true_and, decide_eq_false_iff_not,
          Finset.disjoint_insert_right]
        constructor
        · rintro ⟨hFP, hnew⟩
          refine ⟨⟨hFP, fun h => (hnew h).2⟩, ?_⟩
          subst F
          exact fun h => h.elim hup (fun h => (hnew h.1).1 h.2)
        · rintro ⟨⟨hFP, hold⟩, hno⟩
          exact ⟨hFP, fun h => ⟨fun huJ => hno (Or.inr ⟨h, huJ⟩), hold h⟩⟩
      · have hi : (insert u h.positive).card = 3 := by
          rw [Finset.card_insert_of_notMem hup, htwo]
        simp only [update, ↓reduceIte, gatedCompatible, hi,
          show ¬3 ≤ 1 by omega, show ¬3 = 2 by omega,
          hp, htwo, show ¬2 < 2 by omega, show ¬2 = 1 by omega, he,
          compatible, Finset.insert_subset_iff, gatedAnswer, hp₂,
          show (2 : ℕ) ≤ 2 by omega, true_and,
          decide_eq_true_eq, ↓reduceIte]
        constructor
        · rintro ⟨hFP, ⟨huJ, hPJ⟩, hJB⟩
          exact ⟨⟨hFP, fun _ => hJB⟩, Or.inr ⟨hcb hJB, huJ⟩⟩
        · rintro ⟨⟨hFP, hcond⟩, huF | ⟨hJb, huJ⟩⟩
          · exact False.elim (hup (hFP ▸ huF))
          · exact ⟨hFP, ⟨huJ, hFP ▸ hFJ⟩, hcond hJb⟩
    · have hp₃ : 3 ≤ h.positive.card := by omega
      have hFnot : F = h.anchors → u ∉ F := by
        intro he huF
        exact hup (ha (he ▸ huF))
      cases b
      · simp only [update, Bool.false_eq_true, ↓reduceIte, gatedCompatible, hp, htwo,
          compatible, Finset.disjoint_insert_right, gatedAnswer, hp₂, true_and,
          decide_eq_false_iff_not]
        constructor
        · rintro ⟨he, hPJ, huJ, hJB⟩
          exact ⟨⟨he, hPJ, hJB⟩, fun h =>
            h.elim (hFnot he) (fun h => huJ h.2)⟩
        · rintro ⟨⟨he, hPJ, hJB⟩, hno⟩
          exact ⟨he, hPJ, (fun huJ => hno (Or.inr ⟨hcb hJB, huJ⟩)), hJB⟩
      · have hi₁ : ¬(insert u h.positive).card ≤ 1 := by
          rw [Finset.card_insert_of_notMem hup]
          omega
        have hi₂ : ¬(insert u h.positive).card = 2 := by
          rw [Finset.card_insert_of_notMem hup]
          omega
        simp only [update, ↓reduceIte, gatedCompatible, hp, htwo, hi₁, hi₂,
          show ¬h.positive.card < 2 by omega, show ¬h.positive.card = 1 by omega,
          compatible, Finset.insert_subset_iff, gatedAnswer, hp₂, true_and,
          decide_eq_true_eq, ↓reduceIte]
        constructor
        · rintro ⟨he, ⟨huJ, hPJ⟩, hJB⟩
          exact ⟨⟨he, hPJ, hJB⟩, Or.inr ⟨hcb hJB, huJ⟩⟩
        · rintro ⟨⟨he, hPJ, hJB⟩, huF | ⟨_, huJ⟩⟩
          · exact False.elim (hFnot he huF)
          · exact ⟨he, ⟨huJ, hPJ⟩, hJB⟩

end History

end SteinerLowerBound.MetricComparison

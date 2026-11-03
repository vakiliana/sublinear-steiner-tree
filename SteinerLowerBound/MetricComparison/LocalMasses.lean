module

public import SteinerLowerBound.MetricComparison.Experiments

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical
open HardDistribution

variable {S Ω : Type*} [Fintype S]

theorem fillerNeighbors_eq_pair (f : Filler S) (e : Subsets S 2) :
    fillerNeighbors f = e.val ↔ f = .inr (.inr e) := by
  classical
  rcases f with (_ | u | e')
  · have hn : (∅ : Finset S) ≠ e.val := by
      intro he
      have := congrArg Finset.card he
      simp [e.property] at this
    simp [fillerNeighbors, hn]
  · have hn : ({u} : Finset S) ≠ e.val := by
      intro he
      have := congrArg Finset.card he
      simp [e.property] at this
    simp [fillerNeighbors, hn]
  · simp only [fillerNeighbors, Sum.inr.injEq]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩

theorem gated_pair_slice (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (e : Subsets S 2)
    (P : Finset S → Prop) :
    (gatedCenterLaw k w hsmall).prob
        {x | fillerNeighbors x.1 = e.val ∧ P (jointSupport x)} =
      beta S * (markLaw k w hsmall (.inr (.inr e))).prob
        {H | P (e.val ∪ potentialSupport H)} := by
  classical
  have he : {x : GatedState S k.d |
      fillerNeighbors x.1 = e.val ∧ P (jointSupport x)} =
      {x | x.1 = .inr (.inr e) ∧ P (e.val ∪ potentialSupport x.2)} := by
    ext x
    simp only [Set.mem_ofPred_eq, fillerNeighbors_eq_pair]
    constructor <;> rintro ⟨hf, hp⟩ <;> refine ⟨hf, ?_⟩
    · simpa only [jointSupport, hf, fillerNeighbors] using hp
    · simpa only [jointSupport, hf, fillerNeighbors] using hp
  rw [he, gatedCenterLaw]
  simpa only [Set.mem_ofPred_eq, fillerLaw] using
    Law.prob_step_slice
      (fillerLaw (by have := k.d_ge_three; have := k.enough_special; omega))
      (markLaw k w hsmall) (.inr (.inr e))
      {H | P (e.val ∪ potentialSupport H)}

theorem mark_discard_probability (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (e : Subsets S 2)
    (B₀ B : Finset S) (hB : B₀ ⊆ B) (heB : Disjoint e.val B) :
    beta S * (markLaw k w hsmall (.inr (.inr e))).prob
        {H | Disjoint (e.val ∪ potentialSupport H) B₀ →
          Disjoint (e.val ∪ potentialSupport H) B} =
      beta S +
        (∑ H : Subsets S k.d, if e.val ⊆ H.val ∧ Disjoint H.val B then
          starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0) -
        (∑ H : Subsets S k.d, if e.val ⊆ H.val ∧ Disjoint H.val B₀ then
          starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0) := by
  classical
  have hβ : beta S ≠ 0 :=
    (beta_pos (by have := k.d_ge_three; have := k.enough_special; omega)).ne'
  let a := fun H : Subsets S k.d =>
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H
  let p := fun H : Subsets S k.d => if e.val ⊆ H.val then a H / beta S else 0
  have hnone : (Disjoint (e.val ∪ potentialSupport (none : Option (Subsets S k.d))) B₀ →
      Disjoint (e.val ∪ potentialSupport (none : Option (Subsets S k.d))) B) := by
    simpa [potentialSupport] using fun _ => heB
  have hi (H : Subsets S k.d) :
      beta S * ((if Disjoint (e.val ∪ H.val) B₀ →
          Disjoint (e.val ∪ H.val) B then p H else 0) - p H) =
        (if e.val ⊆ H.val ∧ Disjoint H.val B then a H else 0) -
          (if e.val ⊆ H.val ∧ Disjoint H.val B₀ then a H else 0) := by
    by_cases hs : e.val ⊆ H.val
    · rw [Finset.union_eq_right.mpr hs]
      have hd : Disjoint H.val B → Disjoint H.val B₀ :=
        fun h => Finset.disjoint_of_subset_right hB h
      by_cases h₀ : Disjoint H.val B₀
      · by_cases h₁ : Disjoint H.val B
        · simp [p, hs, h₀, h₁]
        · simp only [p, hs, h₀, h₁, and_self, true_and, true_implies, ↓reduceIte]
          field_simp [hβ]
          <;> ring
      · have h₁ : ¬Disjoint H.val B := fun h => h₀ (hd h)
        simp [p, hs, h₀, h₁]
    · simp [p, hs]
  have hprob :
      (markLaw k w hsmall (.inr (.inr e))).prob
        {H | Disjoint (e.val ∪ potentialSupport H) B₀ →
          Disjoint (e.val ∪ potentialSupport H) B} =
        1 + (∑ H, ((if Disjoint (e.val ∪ H.val) B₀ →
          Disjoint (e.val ∪ H.val) B then p H else 0) - p H)) := by
    simp only [markLaw, potentialLaw, Law.prob, Law.withNone, Fintype.sum_option,
      Set.mem_ofPred_eq]
    simp only [potentialSupport, Finset.union_empty, heB, implies_true, ↓reduceIte]
    change (1 - ∑ H, p H) +
      (∑ H, if Disjoint (e.val ∪ H.val) B₀ →
        Disjoint (e.val ∪ H.val) B then p H else 0) = _
    rw [Finset.sum_sub_distrib]
    ring
  rw [hprob, mul_add, mul_one, Finset.mul_sum]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  dsimp only [a]
  ring_nf

theorem gated_evidence_two (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (h : History S) (hv : h.Valid) (hp : h.positive.card = 2) :
    (gatedObserver k w hsmall).evidence h =
      beta S + starEvidence k w h - activationMass k w h := by
  classical
  let e : Subsets S 2 := ⟨h.positive, hp⟩
  have he : h.anchors = e.val := h.anchors_eq hv (by omega)
  change (gatedCenterLaw k w hsmall).prob
    {x | h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)} = _
  have hs : {x : GatedState S k.d |
      h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)} =
      {x | fillerNeighbors x.1 = e.val ∧
        (Disjoint (jointSupport x) h.blocked → Disjoint (jointSupport x) h.negative)} := by
    ext x
    simp [History.gatedCompatible, hp, e]
  rw [hs, gated_pair_slice k w hsmall e
    (fun J => Disjoint J h.blocked → Disjoint J h.negative),
    mark_discard_probability k w hsmall e
    h.blocked h.negative hv.2.2.2.1 hv.1]
  simp only [starEvidence, activationMass, History.compatible, he, e]
  congr 2
  apply Finset.sum_congr rfl
  intro H _
  by_cases hh : h.positive ⊆ H.val ∧ Disjoint H.val h.negative
  · simp only [hh, ↓reduceIte]
  · simp only [hh, ↓reduceIte]

theorem mark_positive_probability (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (e : Subsets S 2) (h : History S) (hp : 3 ≤ h.positive.card)
    (he : e.val ⊆ h.positive) :
    beta S * (markLaw k w hsmall (.inr (.inr e))).prob
        {H | h.compatible (e.val ∪ potentialSupport H)} =
      starEvidence k w h := by
  classical
  have hβ : beta S ≠ 0 :=
    (beta_pos (by have := k.d_ge_three; have := k.enough_special; omega)).ne'
  have hn : ¬h.compatible e.val := by
    intro hc
    have := Finset.card_le_card hc.1
    rw [e.property] at this
    omega
  have ht (H : Subsets S k.d) :
      beta S * (if h.compatible (e.val ∪ H.val) then
        (if e.val ⊆ H.val then
          starMass k.d k.H0 k.R (fun u => k.value (w u)) H / beta S else 0) else 0) =
        if h.compatible H.val then
          starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0 := by
    by_cases hs : e.val ⊆ H.val
    · simp only [Finset.union_eq_right.mpr hs, hs, ↓reduceIte]
      split_ifs <;> simp [hβ, mul_div_cancel₀]
    · have hnot : ¬h.compatible H.val := fun hc => hs (he.trans hc.1)
      simp [hs, hnot]
  simp only [markLaw, potentialLaw, Law.prob, Law.withNone, Fintype.sum_option,
    Set.mem_ofPred_eq, potentialSupport,
    Finset.union_empty, hn, ↓reduceIte, zero_add, Finset.mul_sum]
  simp_rw [ht]
  rfl

theorem gated_evidence_many (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (h : History S) (hv : h.Valid) (hp : 3 ≤ h.positive.card) :
    (gatedObserver k w hsmall).evidence h = starEvidence k w h := by
  classical
  let e : Subsets S 2 := ⟨h.anchors, by rw [hv.2.2.1, min_eq_right (by omega)]⟩
  change (gatedCenterLaw k w hsmall).prob
    {x | h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)} = _
  have hs : {x : GatedState S k.d |
      h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)} =
      {x | fillerNeighbors x.1 = e.val ∧ h.compatible (jointSupport x)} := by
    ext x
    simp [History.gatedCompatible, show ¬h.positive.card ≤ 1 by omega,
      show ¬h.positive.card = 2 by omega, e]
  rw [hs, gated_pair_slice k w hsmall e (fun J => h.compatible J),
    mark_positive_probability k w hsmall e h hp hv.2.1]

end SteinerLowerBound.MetricComparison

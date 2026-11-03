module

public import SteinerLowerBound.MetricComparison.Histories

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Law

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem prob_step (μ : Law Ω) (k : Ω → Law Γ) (E : Set (Ω × Γ)) :
    (μ.step k).prob E = μ.expect (fun ω => (k ω).prob {γ | (ω, γ) ∈ E}) := by
  classical
  simp only [prob, step, expect, Fintype.sum_prod_type, Finset.mul_sum, Set.mem_ofPred_eq]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro γ _
  split_ifs <;> simp

theorem prob_step_slice (μ : Law Ω) (k : Ω → Law Γ) (ω : Ω) (E : Set Γ) :
    (μ.step k).prob {x | x.1 = ω ∧ x.2 ∈ E} = μ.mass ω * (k ω).prob E := by
  classical
  rw [prob_step]
  unfold expect
  calc
    _ = ∑ z, if z = ω then μ.mass ω * (k ω).prob E else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z = ω
      · subst z
        simp
      · have he : {γ | z = ω ∧ γ ∈ E} = ∅ := by ext γ; simp [hz]
        simp [hz, he]
    _ = _ := by simp

end Law

namespace MetricComparison

open HardDistribution

variable {S Ω : Type*} [Fintype S]

abbrev GatedState (S : Type*) (d : ℕ) := Filler S × Option (Subsets S d)

@[reducible] def potentialSupport {d : ℕ} : Option (Subsets S d) → Finset S
  | none => ∅
  | some H => H.val

@[reducible] noncomputable def jointSupport {d : ℕ} (x : GatedState S d) : Finset S :=
  fillerNeighbors x.1 ∪ potentialSupport x.2

noncomputable def markLaw (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) (f : Filler S) :
    Law (Option (Subsets S k.d)) :=
  match f with
  | .inl _ => Law.pure none
  | .inr (.inl _) => Law.pure none
  | .inr (.inr e) =>
    potentialLaw k.d k.H0 k.R (fun u => k.value (w u)) e
      (by have := k.d_ge_three; omega) k.enough_special
      k.H0_nonneg k.R_pos (fun u => (k.bounded (w u)).1)
      k.M (fun u => (k.bounded (w u)).2) hsmall

noncomputable def gatedCenterLaw (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) : Law (GatedState S k.d) :=
  Law.step (fillerLaw (by have := k.d_ge_three; have := k.enough_special; omega))
    (markLaw k w hsmall)

noncomputable def gatedCentersLaw {C : Type*} [Fintype C]
    (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    Law (C → GatedState S k.d) :=
  Law.pi (fun _ : C => gatedCenterLaw k w hsmall)

noncomputable def gatedObserver (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1) :
    Observer (History.memory S) (GatedState S k.d) where
  law := gatedCenterLaw k w hsmall
  accepts h x := h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)
  answer x h u := h.gatedAnswer (fillerNeighbors x.1) (jointSupport x) u
  initial_accepts x := by
    simp [History.gatedCompatible, History.compatible, History.memory, History.initial]
  transition h u b hv hf x :=
    History.gatedCompatible_update h u b hv hf _ _
      (filler_card_le_two x.1) Finset.subset_union_left

noncomputable def fillerEvidence (hm : 2 ≤ Fintype.card S) (h : History S) : ℝ :=
  (fillerLaw hm).prob {f | h.compatible (fillerNeighbors f)}

noncomputable def starEvidence (k : Setup S Ω) (w : S → Ω) (h : History S) : ℝ :=
  ∑ H : Subsets S k.d, if h.compatible H.val then
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0

noncomputable def activationMass (k : Setup S Ω) (w : S → Ω) (h : History S) : ℝ :=
  ∑ H : Subsets S k.d, if h.anchors ⊆ H.val ∧ Disjoint H.val h.blocked then
    starMass k.d k.H0 k.R (fun u => k.value (w u)) H else 0

theorem static_evidence (k : Setup S Ω) (w : S → Ω) (h : History S) :
    (History.staticObserver k w).evidence h =
      fillerEvidence (by have := k.d_ge_three; have := k.enough_special; omega) h +
        starEvidence k w h -
          if h.positive = ∅ then starTotal k.d k.H0 k.R (fun u => k.value (w u)) else 0 := by
  classical
  simp only [Observer.evidence, History.staticObserver, Setup.centerLaw,
    fillerEvidence, Law.prob, staticLaw, fillerLaw, Set.mem_ofPred_eq, neighbors, fillerNeighbors,
    Fintype.sum_sum_type, Fintype.sum_unique, starEvidence]
  have he : h.compatible ∅ ↔ h.positive = ∅ := by simp [History.compatible]
  by_cases hp : h.positive = ∅ <;> simp only [he, hp, ↓reduceIte] <;>
    ring_nf <;> congr 1

theorem gated_evidence_low (k : Setup S Ω) (w : S → Ω)
    (hsmall : anchorConstant k.d k.H0 k.M / k.R ≤ 1)
    (h : History S) (hp : h.positive.card ≤ 1) :
    (gatedObserver k w hsmall).evidence h =
      fillerEvidence (by have := k.d_ge_three; have := k.enough_special; omega) h := by
  classical
  change (gatedCenterLaw k w hsmall).prob
    {x | h.gatedCompatible (fillerNeighbors x.1) (jointSupport x)} = _
  rw [gatedCenterLaw, Law.prob_step]
  unfold fillerEvidence
  rw [Law.prob_eq_expect]
  apply congrArg (Law.expect (fillerLaw _))
  funext f
  by_cases hf : h.compatible (fillerNeighbors f)
  · have he : {γ : Option (Subsets S k.d) |
        h.gatedCompatible (fillerNeighbors f) (jointSupport (f, γ))} =
        Set.univ := by ext γ; simp [History.gatedCompatible, hp, hf]
    simp only [Set.mem_ofPred_eq, he, Law.prob_univ, hf, ↓reduceIte]
  · have he : {γ : Option (Subsets S k.d) |
        h.gatedCompatible (fillerNeighbors f) (jointSupport (f, γ))} =
        ∅ := by ext γ; simp [History.gatedCompatible, hp, hf]
    simp only [Set.mem_ofPred_eq, he, Law.prob_empty, hf, ↓reduceIte]

end MetricComparison

end SteinerLowerBound

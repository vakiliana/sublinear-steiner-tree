module

public import SteinerLowerBound.Simulation.Notices
public import SteinerLowerBound.VisibleMass
public import SteinerLowerBound.MetricComparison.PublicQueries
public import SteinerLowerBound.Screening.Bookkeeping

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical
open HardDistribution
open MetricComparison.Public

namespace Public

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I] [Fintype C]

abbrev Terminal := Screening.Terminal
abbrev Query := Screening.Query
abbrev Reply := Screening.Reply
abbrev Candidate (S C : Type*) (d : ℕ) := C × Subsets S d

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

noncomputable def pull (π : Equiv.Perm (Terminal S G I))
    (Q : Finset (Terminal S G I)) : Finset S :=
  Finset.univ.filter (fun s => specialLabel π s ∈ Q)

@[simp]
theorem mem_pull (π : Equiv.Perm (Terminal S G I))
    (Q : Finset (Terminal S G I)) (s : S) :
    s ∈ pull π Q ↔ specialLabel π s ∈ Q := by simp [pull]

theorem pull_mono (π : Equiv.Perm (Terminal S G I)) : Monotone (pull π) := by
  intro Q Q' h s hs
  exact (mem_pull _ _ _).mpr (h ((mem_pull _ _ _).mp hs))

theorem pull_card_le (π : Equiv.Perm (Terminal S G I))
    (Q : Finset (Terminal S G I)) : (pull π Q).card ≤ Q.card := by
  classical
  have hs : (pull π Q).map (specialLabel π) ⊆ Q := by
    rintro u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hu
    exact (mem_pull _ _ _).mp hs
  simpa only [Finset.card_map] using Finset.card_le_card hs

noncomputable def support (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (x : Candidate S C d) : Finset (Terminal S G I) :=
  x.2.val.map (specialLabel π)

@[simp]
theorem support_card (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (x : Candidate S C d) :
    (support π d x).card = d := by simp [support, x.2.property]

noncomputable def fillers (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S) (c : C) :
    Finset (Terminal S G I) :=
  (fillerNeighbors (F c)).map (specialLabel π)

noncomputable def stars (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (H : C → Option (Subsets S d)) (c : C) : Finset (Terminal S G I) :=
  (H c).elim ∅ (fun h => h.val.map (specialLabel π))

noncomputable def bits (d : ℕ) (H : C → Option (Subsets S d)) (x : Candidate S C d) : Bool :=
  decide (H x.1 = some x.2)

def Anchored (d : ℕ) (F : C → Filler S) (H : C → Option (Subsets S d)) : Prop :=
  ∀ c h, H c = some h → fillerNeighbors (F c) ⊆ h.val

noncomputable def access (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (Q : Finset (Terminal S G I)) : Finset (Candidate S C d) :=
  VisibleMass.region d F (pull π Q)

theorem mem_region (d : ℕ) (F : C → Filler S) (Q : Finset S) (x : Candidate S C d) :
    x ∈ VisibleMass.region d F Q ↔
      FillerSparsity.isPair (F x.1) = true ∧ fillerNeighbors (F x.1) ⊆ Q ∧
        fillerNeighbors (F x.1) ⊆ x.2.val ∧ 3 ≤ (x.2.val ∩ Q).card := by
  classical
  constructor
  · intro hx
    obtain ⟨c, hc, hH⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hH
    exact ⟨(Finset.mem_filter.mp hc).2.1, (Finset.mem_filter.mp hc).2.2,
      (Finset.mem_filter.mp hh).2⟩
  · intro hx
    exact Finset.mem_biUnion.mpr ⟨x.1,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1, hx.2.1⟩,
      Finset.mem_image.mpr ⟨x.2, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hx.2.2⟩, rfl⟩⟩

theorem region_mono (d : ℕ) (F : C → Filler S) : Monotone (VisibleMass.region d F) := by
  intro Q Q' h x hx
  obtain ⟨hp, hf, hh, hv⟩ := (mem_region _ _ _ _).mp hx
  exact (mem_region _ _ _ _).mpr ⟨hp, hf.trans h, hh,
    hv.trans (Finset.card_le_card (Finset.inter_subset_inter_left h))⟩

theorem access_mono (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S) :
    Monotone (access π d F) := (region_mono d F).comp (pull_mono π)

@[simp]
theorem access_empty (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S) :
    access π d F ∅ = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := (mem_region _ _ _ _).mp hx
  have hp : pull π ∅ = ∅ := by ext s; simp
  rw [hp, Finset.inter_empty, Finset.card_empty] at hh
  omega

theorem pair_iff_card (f : Filler S) :
    FillerSparsity.isPair f = true ↔ (fillerNeighbors f).card = 2 := by
  classical
  rcases f with _ | (s | h)
  · simp [FillerSparsity.isPair, fillerNeighbors]
  · simp [FillerSparsity.isPair, fillerNeighbors]
  · simp [FillerSparsity.isPair, fillerNeighbors, h.property]

theorem inter_pull (π : Equiv.Perm (Terminal S G I))
    (H : Finset S) (Q : Finset (Terminal S G I)) :
    H.map (specialLabel π) ∩ Q = (H ∩ pull π Q).map (specialLabel π) := by
  classical
  ext u
  simp only [Finset.mem_inter, Finset.mem_map]
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hq⟩
    exact ⟨s, ⟨hs, (mem_pull _ _ _).mpr hq⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hq⟩, rfl⟩
    exact ⟨⟨s, hs, rfl⟩, (mem_pull _ _ _).mp hq⟩

theorem filler_subset_pull (π : Equiv.Perm (Terminal S G I))
    (F : C → Filler S) (Q : Finset (Terminal S G I)) (c : C) :
    fillerNeighbors (F c) ⊆ pull π Q ↔ fillers π F c ⊆ Q := by
  classical
  constructor
  · intro h u hu
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hu
    exact (mem_pull _ _ _).mp (h hs)
  · intro h s hs
    exact (mem_pull _ _ _).mpr (h (Finset.mem_map.mpr ⟨s, hs, rfl⟩))

theorem candidate_visible (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d))
    (Q : Finset (Terminal S G I)) (x : Candidate S C d)
    (hx : x ∈ access π d F Q) (hb : bits d H x = true) :
    TwoAnchor.Visible (fillers π F) (stars π d H) Q x.1 ∧
      support π d x = stars π d H x.1 := by
  classical
  have he : H x.1 = some x.2 := by simpa [bits] using hb
  have ha := (mem_region _ _ _ _).mp hx
  have hs : stars π d H x.1 = support π d x := by simp [stars, support, he]
  refine ⟨⟨?_, (filler_subset_pull _ _ _ _).mp ha.2.1, ?_⟩, hs.symm⟩
  · simpa [fillers] using (pair_iff_card (F x.1)).mp ha.1
  · have hsub : (x.2.val ∩ pull π Q).map (specialLabel π) ⊆
        stars π d H x.1 ∩ Q := by
      intro u hu
      obtain ⟨s, hs', rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨hsH, hsQ⟩ := Finset.mem_inter.mp hs'
      refine Finset.mem_inter.mpr ⟨?_, (mem_pull _ _ _).mp hsQ⟩
      rw [hs]
      exact Finset.mem_map.mpr ⟨s, hsH, rfl⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_map] at hc
    exact ha.2.2.2.trans hc

theorem visible_candidate (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H)
    (Q : Finset (Terminal S G I)) (c : C)
    (hv : TwoAnchor.Visible (fillers π F) (stars π d H) Q c) :
    ∃ x ∈ access π d F Q, x.1 = c ∧ bits d H x = true ∧
      support π d x = stars π d H c := by
  classical
  cases he : H c with
  | none => simp [TwoAnchor.Visible, stars, he] at hv
  | some h =>
      refine ⟨(c, h), ?_, rfl, ?_, ?_⟩
      · apply (mem_region _ _ _ _).mpr
        refine ⟨(pair_iff_card _).mpr ?_, (filler_subset_pull _ _ _ _).mpr hv.2.1,
          ha c h he, ?_⟩
        · simpa [fillers] using hv.1
        · have hsub : stars π d H c ∩ Q ⊆
              (h.val ∩ pull π Q).map (specialLabel π) := by
            intro u hu
            obtain ⟨huH, huQ⟩ := Finset.mem_inter.mp hu
            simp only [stars, he, Option.elim_some] at huH
            obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp huH
            exact Finset.mem_map.mpr
              ⟨s, Finset.mem_inter.mpr ⟨hs, (mem_pull _ _ _).mpr huQ⟩, rfl⟩
          have hc := Finset.card_le_card hsub
          rw [Finset.card_map] at hc
          exact hv.2.2.trans hc
      · simp [bits, he]
      · simp [support, stars, he]

theorem fillers_eq_relabel (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S) :
    fillers π F = Screening.relabel π (internalSupport (fun c => fillerNeighbors (F c))) := by
  rw [relabel_internalSupport]
  rfl

theorem stars_eq_relabel (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (H : C → Option (Subsets S d)) :
    stars π d H = Screening.relabel π (internalSupport (fun c => (H c).elim ∅ Subtype.val)) := by
  rw [relabel_internalSupport]
  funext c
  cases he : H c <;> simp [stars, he, MetricComparison.PartialEmbedding.lift, labelEmbedding]

theorem stars_anchored (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (H : C → Option (Subsets S d)) (ha : Anchored d F H) (c : C) :
    (stars π d H c).Nonempty → fillers π F c ⊆ stars π d H c := by
  intro hn
  cases he : H c with
  | none => simp [stars, he] at hn
  | some h =>
      intro u hu
      obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp hu
      simp only [stars, he, Option.elim_some]
      exact Finset.mem_map.mpr ⟨s, ha c h he hs, rfl⟩

end Public

end SteinerLowerBound.Simulation

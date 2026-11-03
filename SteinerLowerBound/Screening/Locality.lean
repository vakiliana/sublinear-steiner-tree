module

public import SteinerLowerBound.Exposure
public import SteinerLowerBound.Distributions
public import SteinerLowerBound.ProductProbability

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace TwoAnchor

variable {T C : Type*} [Fintype T]

def AgreesOn (h : List (C × T)) (F F' : C → Finset T) : Prop :=
  (∀ c, (F c).card = (F' c).card) ∧
    ∀ c u, (c, u) ∈ h → (u ∈ F c ↔ u ∈ F' c)

theorem agreesOn_take {h : List (C × T)} {F F' : C → Finset T}
    (hF : AgreesOn h F F') (n : ℕ) : AgreesOn (h.take n) F F' :=
  ⟨hF.1, fun c u hu => hF.2 c u (List.mem_of_mem_take hu)⟩

theorem active_congr {h : List (C × T)} {F F' : C → Finset T}
    (hF : AgreesOn h F F') (c : C) : active F h c ↔ active F' h c := by
  classical
  have hi : F c ∩ queried h c = F' c ∩ queried h c := by
    ext u
    by_cases hq : u ∈ queried h c
    · have hmem : (c, u) ∈ h := (Finset.mem_filter.mp hq).2
      simp [hq, hF.2 c u hmem]
    · simp [hq]
  have hsub {L L' Q : Finset T} (hc : L.card = L'.card)
      (hi : L ∩ Q = L' ∩ Q) (hs : L ⊆ Q) : L' ⊆ Q := by
    have hcard : (L' ∩ Q).card = L'.card := by
      rw [← hi, Finset.inter_eq_left.mpr hs, hc]
    have he := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hcard.ge
    rw [← he]
    exact Finset.inter_subset_right
  exact ⟨fun h => ⟨(hF.1 c) ▸ h.1, hsub (hF.1 c) hi h.2⟩,
    fun h => ⟨(hF.1 c).symm ▸ h.1, hsub (hF.1 c).symm hi.symm h.2⟩⟩

theorem blocked_subset_queried (F : C → Finset T) (h : List (C × T)) (c : C) :
    blocked F h c ⊆ queried h c := by
  intro u hu
  obtain ⟨_, i, hi, _⟩ := (Finset.mem_filter.mp hu).2
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hi ▸ List.get_mem h i⟩

theorem blocked_congr {h : List (C × T)} {F F' : C → Finset T}
    (hF : AgreesOn h F F') (c : C) : blocked F h c = blocked F' h c := by
  classical
  have transfer {L L' : C → Finset T} (hL : AgreesOn h L L') :
      blocked L h c ⊆ blocked L' h c := by
    intro u hu
    obtain ⟨huL, i, hi, ha⟩ := (Finset.mem_filter.mp hu).2
    have hmem : (c, u) ∈ h := hi ▸ List.get_mem h i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    refine ⟨fun hv => huL ((hL.2 c u hmem).mpr hv), i, hi, ?_⟩
    exact fun hv => ha ((active_congr (agreesOn_take hL _) c).mpr hv)
  exact Finset.Subset.antisymm (transfer hF)
    (transfer ⟨fun c => (hF.1 c).symm, fun c u hu => (hF.2 c u hu).symm⟩)

theorem disjoint_blocked_congr {h : List (C × T)} {F F' H H' : C → Finset T}
    (hF : AgreesOn h F F') (hH : AgreesOn h H H') (c : C) :
    Disjoint (H c) (blocked F h c) ↔ Disjoint (H' c) (blocked F' h c) := by
  classical
  rw [← blocked_congr hF c]
  simp only [Finset.disjoint_left]
  constructor
  · intro hd u hu hb
    have hm : (c, u) ∈ h := (Finset.mem_filter.mp
      (blocked_subset_queried F h c hb)).2
    exact hd ((hH.2 c u hm).mpr hu) hb
  · intro hd u hu hb
    have hm : (c, u) ∈ h := (Finset.mem_filter.mp
      (blocked_subset_queried F h c hb)).2
    exact hd ((hH.2 c u hm).mp hu) hb

theorem answer_congr {h : List (C × T)} {F F' H H' : C → Finset T}
    (hF : AgreesOn h F F') (hH : AgreesOn h H H') (c : C) (u : T)
    (hFu : u ∈ F c ↔ u ∈ F' c) (hHu : u ∈ H c ↔ u ∈ H' c) :
    answer F H h c u = answer F' H' h c u := by
  unfold answer
  simp only [hFu, hHu, active_congr hF c, disjoint_blocked_congr hF hH c]

theorem observations_congr {h : List (C × T)} {F F' H H' : C → Finset T}
    (hF : AgreesOn h F F') (hH : AgreesOn h H H') :
    observations F H h = observations F' H' h := by
  funext i
  have hm : ((h.get i).1, (h.get i).2) ∈ h := List.get_mem h i
  exact answer_congr (agreesOn_take hF _) (agreesOn_take hH _) _ _
    (hF.2 _ _ hm) (hH.2 _ _ hm)

end TwoAnchor

namespace Screening

variable {T C : Type*} [Fintype T]

noncomputable def relabel (π : Equiv.Perm T) (F : C → Finset T) (c : C) : Finset T :=
  (F c).map π.symm.toEmbedding

@[simp]
theorem mem_relabel (π : Equiv.Perm T) (F : C → Finset T) (c : C) (u : T) :
    u ∈ relabel π F c ↔ π u ∈ F c := by
  classical
  simp [relabel]

@[simp]
theorem card_relabel (π : Equiv.Perm T) (F : C → Finset T) (c : C) :
    (relabel π F c).card = (F c).card := by
  classical
  simp [relabel]

noncomputable def exchangeLabels (π : Equiv.Perm T) (u x : T) : Equiv.Perm T :=
  (Equiv.swap u x).trans π

@[simp]
theorem exchangeLabels_apply (π : Equiv.Perm T) (u x v : T) :
    exchangeLabels π u x v = π (Equiv.swap u x v) := rfl

@[simp]
theorem exchangeLabels_involutive (π : Equiv.Perm T) (u x : T) :
    exchangeLabels (exchangeLabels π u x) u x = π := by
  classical
  ext v
  simp [exchangeLabels, Equiv.trans_apply]

theorem exchangeLabels_injective (π : Equiv.Perm T) (u : T) :
    Function.Injective (exchangeLabels π u) := by
  classical
  intro x y he
  have hv := congrArg (fun σ : Equiv.Perm T => π.symm (σ u)) he
  simpa using hv

theorem relabel_agrees_of_avoids (π : Equiv.Perm T) (F : C → Finset T)
    (h : List (C × T)) (u x : T)
    (ha : ∀ c v, (c, v) ∈ h → v = u ∨ v = x → π u ∉ F c ∧ π x ∉ F c) :
    TwoAnchor.AgreesOn h (relabel π F) (relabel (exchangeLabels π u x) F) := by
  classical
  refine ⟨fun c => by simp, ?_⟩
  intro c v hv
  simp only [mem_relabel, exchangeLabels_apply]
  by_cases hu : v = u
  · subst v
    obtain ⟨h1, h2⟩ := ha c u hv (Or.inl rfl)
    simp [h1, h2]
  · by_cases hx : v = x
    · subst v
      obtain ⟨h1, h2⟩ := ha c x hv (Or.inr rfl)
      simp [h1, h2]
    · rw [Equiv.swap_apply_of_ne_of_ne hu hx]

theorem exchange_preserves_center_observations (π : Equiv.Perm T)
    (F H : C → Finset T) (h : List (C × T)) (u x : T)
    (hF : ∀ c v, (c, v) ∈ h → v = u ∨ v = x → π u ∉ F c ∧ π x ∉ F c)
    (hH : ∀ c v, (c, v) ∈ h → v = u ∨ v = x → π u ∉ H c ∧ π x ∉ H c) :
    TwoAnchor.observations (relabel π F) (relabel π H) h =
      TwoAnchor.observations (relabel (exchangeLabels π u x) F)
        (relabel (exchangeLabels π u x) H) h :=
  TwoAnchor.observations_congr (relabel_agrees_of_avoids π F h u x hF)
    (relabel_agrees_of_avoids π H h u x hH)

end Screening

end SteinerLowerBound

module

public import SteinerLowerBound.TwoAnchor

@[expose] public section

namespace SteinerLowerBound

open scoped Classical

namespace TwoAnchor

variable {S C : Type*} [Fintype S]

def Visible (F H : C → Finset S) (Q : Finset S) (c : C) : Prop :=
  (F c).card = 2 ∧ F c ⊆ Q ∧ 3 ≤ (H c ∩ Q).card

def Closed (F H : C → Finset S) (Q : Finset S) : Prop :=
  ∀ c, Visible F H Q c → H c ⊆ Q

noncomputable def closure (F H : C → Finset S) (Q : Finset S) : Finset S :=
  Finset.univ.filter (fun u => ∀ R : Finset S, Q ⊆ R → Closed F H R → u ∈ R)

omit [Fintype S] in
theorem visible_mono (F H : C → Finset S) {Q R : Finset S} (hQR : Q ⊆ R) (c : C)
    (h : Visible F H Q c) : Visible F H R c := by
  refine ⟨h.1, h.2.1.trans hQR, h.2.2.trans ?_⟩
  exact Finset.card_le_card (Finset.inter_subset_inter_left hQR)

theorem subset_closure (F H : C → Finset S) (Q : Finset S) : Q ⊆ closure F H Q := by
  intro u hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun R hR _ => hR hu⟩

theorem closure_minimal (F H : C → Finset S) (Q R : Finset S)
    (hQR : Q ⊆ R) (hR : Closed F H R) : closure F H Q ⊆ R := by
  intro u hu
  exact (Finset.mem_filter.mp hu).2 R hQR hR

theorem closure_closed (F H : C → Finset S) (Q : Finset S) :
    Closed F H (closure F H Q) := by
  intro c hc u hu
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro R hQR hR
  exact hR c (visible_mono F H (closure_minimal F H Q R hQR hR) c hc) hu

theorem closure_mono (F H : C → Finset S) {Q R : Finset S} (hQR : Q ⊆ R) :
    closure F H Q ⊆ closure F H R :=
  closure_minimal F H Q _ (hQR.trans (subset_closure F H R)) (closure_closed F H R)

theorem closure_idempotent (F H : C → Finset S) (Q : Finset S) :
    closure F H (closure F H Q) = closure F H Q :=
  Finset.Subset.antisymm
    (closure_minimal F H _ _ Finset.Subset.rfl (closure_closed F H Q))
    (subset_closure F H _)

omit [Fintype S] in
theorem visible_of_third (F H : C → Finset S) (Q : Finset S) (c : C)
    (hF : (F c).card = 2) (hFQ : F c ⊆ Q) (hFH : F c ⊆ H c)
    (u : S) (huH : u ∈ H c) (huQ : u ∈ Q) (huF : u ∉ F c) :
    Visible F H Q c := by
  have hsub : insert u (F c) ⊆ H c ∩ Q := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨Finset.mem_inter.mpr ⟨huH, huQ⟩,
      fun v hv => Finset.mem_inter.mpr ⟨hFH hv, hFQ hv⟩⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem huF, hF] at hcard
  exact ⟨hF, hFQ, hcard⟩

noncomputable def visibleSupports (F H : C → Finset S) (Q : Finset S) (c : C) : Finset S :=
  if Visible F H Q c then H c else ∅

theorem simulate_answer (F H : C → Finset S) (Q : Finset S)
    (h : List (C × S)) (c : C) (u : S)
    (hanchors : active F h c → F c ⊆ Q)
    (hsupport : (H c).Nonempty → F c ⊆ H c)
    (hunlucky : u ∈ H c → u ∈ Q) :
    answer F (visibleSupports F H Q) h c u = answer F H h c u := by
  classical
  by_cases huF : u ∈ F c
  · simp [answer, huF]
  by_cases hactive : active F h c
  · by_cases hv : Visible F H Q c
    · simp [answer, visibleSupports, hv]
    · have huH : u ∉ H c := by
        intro hu
        exact hv (visible_of_third F H Q c hactive.1 (hanchors hactive)
          (hsupport ⟨u, hu⟩) u hu (hunlucky hu) huF)
      simp [answer, visibleSupports, hv, huF, huH]
  · simp [answer, huF, hactive]

end TwoAnchor

end SteinerLowerBound

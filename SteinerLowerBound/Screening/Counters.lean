module

public import SteinerLowerBound.Screening.Exchange

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {T C : Type*}

noncomputable def queryEndpoints : Query T C → List T
  | .tt u v => if u = v then [u] else [u, v]
  | .ct _ u => [u]
  | .cc _ _ => []

noncomputable def degree (h : List (Query T C)) (u : T) : ℕ :=
  (h.flatMap queryEndpoints).count u

noncomputable def neighborList (h : List (Query T C)) (u : T) : List T :=
  h.flatMap fun
    | .tt a b => if a = u then [b] else if b = u then [a] else []
    | _ => []

noncomputable def ttNeighbors [Fintype T] (h : List (Query T C)) (u : T) : Finset T :=
  (neighborList h u).toFinset

theorem neighborList_length_le_degree (h : List (Query T C)) (u : T) :
    (neighborList h u).length ≤ degree h u := by
  classical
  induction h with
  | nil => simp [neighborList, degree]
  | cons a h ih =>
      cases a with
      | tt a b =>
          simp only [neighborList, List.flatMap_cons, List.length_append,
            degree, queryEndpoints, List.count_append] at *
          by_cases ha : a = u <;> by_cases hb : b = u <;> by_cases hab : a = b <;>
            simp_all [List.count_cons] <;> omega
      | ct c v =>
          simp only [neighborList, List.flatMap_cons, List.nil_append,
            degree, queryEndpoints, List.count_append] at *
          omega
      | cc c c' => simpa [neighborList, degree, queryEndpoints] using ih

theorem ttNeighbors_card_le [Fintype T] (h : List (Query T C)) (u : T) :
    (ttNeighbors h u).card ≤ degree h u := by
  exact (List.toFinset_card_le (l := neighborList h u)).trans
    (neighborList_length_le_degree h u)

theorem mem_ttNeighbors [Fintype T] (h : List (Query T C)) (u v : T) :
    v ∈ ttNeighbors h u ↔ Query.tt u v ∈ h ∨ Query.tt v u ∈ h := by
  classical
  simp only [ttNeighbors, List.mem_toFinset, neighborList, List.mem_flatMap]
  constructor
  · rintro ⟨q, hq, hv⟩
    cases q with
    | ct => simp at hv
    | cc => simp at hv
    | tt a b =>
        by_cases ha : a = u <;> by_cases hb : b = u <;>
          simp_all <;> aesop
  · rintro (hv | hv)
    · exact ⟨.tt u v, hv, by simp⟩
    · exact ⟨.tt v u, hv, by by_cases h : v = u <;> simp [h]⟩

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

def Supported (F : C → Finset (Terminal S G I)) : Prop :=
  ∀ c v, v ∈ F c → specialPosition v

theorem clusterPosition_of_special {v : Terminal S G I} (hv : specialPosition v) :
    clusterPosition v = none := by cases v <;> simp_all [specialPosition, clusterPosition]

theorem not_sameCluster_of_special_left (π : Equiv.Perm (Terminal S G I))
    {u : Terminal S G I} (hu : specialPosition (π u)) (v : Terminal S G I) :
    ¬SameCluster π u v := by
  simp [SameCluster, clusterPosition_of_special hu]

theorem sameCluster_comm (π : Equiv.Perm (Terminal S G I)) (u v : Terminal S G I) :
    SameCluster π u v ↔ SameCluster π v u := by
  simp only [SameCluster, and_comm]

noncomputable def marked (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) : Finset (Terminal S G I) :=
  Finset.univ.filter fun u => ∃ a b, Query.tt a b ∈ h ∧ a ≠ b ∧
    SameCluster π a b ∧ (u = a ∨ u = b)

theorem unmarked_pair (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) {u v : Terminal S G I}
    (hu : u ∉ marked π h) (hne : u ≠ v)
    (hq : Query.tt u v ∈ h ∨ Query.tt v u ∈ h) : ¬SameCluster π u v := by
  classical
  intro hs
  apply hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rcases hq with hq | hq
  · exact ⟨u, v, hq, hne, hs, Or.inl rfl⟩
  · exact ⟨v, u, hq, hne.symm, (sameCluster_comm π _ _).mp hs, Or.inr rfl⟩

noncomputable def neighborClusters (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u : Terminal S G I) :
    Finset (Terminal S G I) :=
  (ttNeighbors h u).biUnion fun v =>
    match clusterPosition (π v) with
    | none => ∅
    | some g => clusterLabels π g

theorem mem_neighborClusters (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u x : Terminal S G I) :
    x ∈ neighborClusters π h u ↔
      ∃ v ∈ ttNeighbors h u, SameCluster π x v := by
  classical
  simp only [neighborClusters, Finset.mem_biUnion]
  constructor
  · rintro ⟨v, hv, hx⟩
    cases he : clusterPosition (π v) with
    | none => simp [he] at hx
    | some g =>
        have hx' : clusterPosition (π x) = some g := by simpa [he] using hx
        exact ⟨v, hv, g, hx', he⟩
  · rintro ⟨v, hv, g, hx, hg⟩
    exact ⟨v, hv, by simpa [hg] using (mem_clusterLabels π g x).mpr hx⟩

theorem neighborClusters_card_le (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) (u : Terminal S G I) :
    (neighborClusters π h u).card ≤ degree h u * Fintype.card I := by
  classical
  calc
    _ ≤ ∑ v ∈ ttNeighbors h u,
        (match clusterPosition (π v) with
          | none => (∅ : Finset (Terminal S G I))
          | some g => clusterLabels π g).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ ttNeighbors h u, Fintype.card I := by
      apply Finset.sum_le_sum
      intro v _
      cases clusterPosition (π v) <;> simp
    _ = (ttNeighbors h u).card * Fintype.card I := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ttNeighbors_card_le h u)

noncomputable def counterLabels (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) : Finset (Terminal S G I) :=
  (ordinaryLabels π).filter fun x => ∃ c, Query.ct c x ∈ h ∧ π u ∈ F c

def Quiet (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) : Prop :=
  ∀ c, Query.ct c u ∈ h → π u ∉ F c ∧ π u ∉ H c

noncomputable def specialExchanges (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) : Finset (Terminal S G I) :=
  ordinaryLabels π \ (marked π h ∪ neighborClusters π h u ∪
    counterLabels π F h u ∪ counterLabels π H h u)

theorem specialExchanges_card (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (h : List (Query (Terminal S G I) C))
    (u : Terminal S G I) :
    Fintype.card G * Fintype.card I ≤ (specialExchanges π F H h u).card +
      (marked π h).card + degree h u * Fintype.card I +
        (counterLabels π F h u).card + (counterLabels π H h u).card := by
  classical
  have hc := Finset.card_le_card_sdiff_add_card (s := ordinaryLabels π)
    (t := marked π h ∪ neighborClusters π h u ∪
      counterLabels π F h u ∪ counterLabels π H h u)
  have hu := Finset.card_union_le
    (marked π h ∪ neighborClusters π h u ∪ counterLabels π F h u)
    (counterLabels π H h u)
  have hu' := Finset.card_union_le (marked π h ∪ neighborClusters π h u)
    (counterLabels π F h u)
  have hu'' := Finset.card_union_le (marked π h) (neighborClusters π h u)
  have hn := neighborClusters_card_le π h u
  rw [card_ordinaryLabels] at hc
  change _ ≤ (specialExchanges π F H h u).card + _ at hc
  omega

end Screening

end SteinerLowerBound

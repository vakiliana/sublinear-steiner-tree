module

public import SteinerLowerBound.Screening.Clusters

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {T C : Type*} [Fintype T]

theorem degree_append (h k : List (Query T C)) (u : T) :
    degree (h ++ k) u = degree h u + degree k u := by
  classical
  simp [degree, List.flatMap_append, List.count_append]

theorem sum_degree_le (h : List (Query T C)) :
    ∑ u, degree h u ≤ 2 * h.length := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [degree]
  | append_singleton h q ih =>
      simp only [degree_append, Finset.sum_add_distrib, List.length_append,
        List.length_singleton]
      have hq : ∑ u, degree [q] u ≤ 2 := by
        cases q with
        | tt a b =>
            by_cases hab : a = b <;>
              simp [degree, queryEndpoints, hab, List.count_cons, Finset.sum_add_distrib]
        | ct c u => simp [degree, queryEndpoints, List.count_cons]
        | cc c c' => simp [degree, queryEndpoints]
      omega

variable {S G I : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _

theorem counterLabels_append (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I))
    (h k : List (Query (Terminal S G I) C)) (u : Terminal S G I) :
    counterLabels π F (h ++ k) u = counterLabels π F h u ∪ counterLabels π F k u := by
  classical
  ext x
  simp only [counterLabels, Finset.mem_filter, Finset.mem_union, List.mem_append]
  aesop

theorem counterLabels_singleton_ct (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (u x : Terminal S G I) (c : C) :
    counterLabels π F [Query.ct c x] u =
      if x ∈ ordinaryLabels π ∧ π u ∈ F c then {x} else ∅ := by
  classical
  ext y
  simp only [counterLabels, Finset.mem_filter, List.mem_singleton,
    Query.ct.injEq]
  split_ifs with hp
  · simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨_, c', ⟨hc, hy⟩, _⟩
      exact hy
    · intro hy
      subst y
      exact ⟨hp.1, c, ⟨rfl, rfl⟩, hp.2⟩
  · simp only [Finset.notMem_empty, iff_false]
    rintro ⟨hy, c', ⟨hc, hyx⟩, hu⟩
    subst y
    subst c'
    exact hp ⟨hy, hu⟩

theorem sum_counterLabels_le (π : Equiv.Perm (Terminal S G I))
    (F : C → Finset (Terminal S G I)) (hcard : ∀ c, (F c).card ≤ 2)
    (h : List (Query (Terminal S G I) C)) :
    ∑ u, (counterLabels π F h u).card ≤ 2 * h.length := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [counterLabels]
  | append_singleton h q ih =>
      have hq : ∑ u, (counterLabels π F [q] u).card ≤ 2 := by
        cases q with
        | tt a b => simp [counterLabels]
        | cc c c' => simp [counterLabels]
        | ct c x =>
            calc
              _ ≤ ∑ u, if π u ∈ F c then (1 : ℕ) else 0 := by
                apply Finset.sum_le_sum
                intro u _
                rw [counterLabels_singleton_ct]
                split_ifs <;> simp_all
              _ = (relabel π F c).card := by
                rw [← Finset.sum_filter]
                simp only [Finset.sum_const, smul_eq_mul, mul_one]
                congr 1
                ext u
                simp
              _ ≤ 2 := by simpa using hcard c
      calc
        _ ≤ ∑ u, ((counterLabels π F h u).card + (counterLabels π F [q] u).card) := by
          apply Finset.sum_le_sum
          intro u _
          rw [counterLabels_append]
          exact Finset.card_union_le _ _
        _ = _ := Finset.sum_add_distrib
        _ ≤ 2 * (h ++ [q]).length := by
          simp only [List.length_append, List.length_singleton]
          omega

theorem externalLabels_append (π : Equiv.Perm (Terminal S G I))
    (h k : List (Query (Terminal S G I) C)) (g : G) :
    externalLabels π (h ++ k) g = externalLabels π h g ∪ externalLabels π k g := by
  classical
  ext x
  simp only [externalLabels, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_union, List.mem_append]
  constructor
  · rintro ⟨hx, v, hv, hq⟩
    rcases hq with (hh | hk) | (hh | hk)
    · exact Or.inl ⟨hx, v, hv, Or.inl hh⟩
    · exact Or.inr ⟨hx, v, hv, Or.inl hk⟩
    · exact Or.inl ⟨hx, v, hv, Or.inr hh⟩
    · exact Or.inr ⟨hx, v, hv, Or.inr hk⟩
  · rintro (⟨hx, v, hv, hq⟩ | ⟨hx, v, hv, hq⟩)
    · exact ⟨hx, v, hv, hq.elim (fun h => Or.inl (Or.inl h))
        (fun h => Or.inr (Or.inl h))⟩
    · exact ⟨hx, v, hv, hq.elim (fun h => Or.inl (Or.inr h))
        (fun h => Or.inr (Or.inr h))⟩

theorem externalLabels_singleton_tt_subset (π : Equiv.Perm (Terminal S G I))
    (a b : Terminal S G I) (g : G) :
    externalLabels π [(Query.tt a b : Query (Terminal S G I) C)] g ⊆
      (if b ∈ clusterLabels π g then {a} else ∅) ∪
        (if a ∈ clusterLabels π g then {b} else ∅) := by
  classical
  intro x hx
  obtain ⟨_, v, hv, hq⟩ := (Finset.mem_filter.mp hx).2
  rcases hq with hq | hq
  · have hh := Query.tt.inj (List.mem_singleton.mp hq)
    obtain ⟨rfl, rfl⟩ := hh
    simp [hv]
  · have hh := Query.tt.inj (List.mem_singleton.mp hq)
    obtain ⟨rfl, rfl⟩ := hh
    simp [hv]

theorem sum_cluster_membership_le (π : Equiv.Perm (Terminal S G I))
    (v : Terminal S G I) :
    (∑ g, if v ∈ clusterLabels π g then (1 : ℕ) else 0) ≤ 1 := by
  classical
  simp only [mem_clusterLabels]
  cases clusterPosition (π v) <;> simp [eq_comm]

theorem sum_externalLabels_le (π : Equiv.Perm (Terminal S G I))
    (h : List (Query (Terminal S G I) C)) :
    ∑ g, (externalLabels π h g).card ≤ 2 * h.length := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [externalLabels]
  | append_singleton h q ih =>
      have hq : ∑ g, (externalLabels π [q] g).card ≤ 2 := by
        cases q with
        | ct c u => simp [externalLabels]
        | cc c c' => simp [externalLabels]
        | tt a b =>
            calc
              _ ≤ ∑ g, ((if b ∈ clusterLabels π g then (1 : ℕ) else 0) +
                  (if a ∈ clusterLabels π g then 1 else 0)) := by
                apply Finset.sum_le_sum
                intro g _
                have hc := (Finset.card_le_card
                  (externalLabels_singleton_tt_subset (C := C) π a b g)).trans
                    (Finset.card_union_le _ _)
                by_cases ha : a ∈ clusterLabels π g <;>
                  by_cases hb : b ∈ clusterLabels π g <;> simpa [ha, hb] using hc
              _ = _ := Finset.sum_add_distrib
              _ ≤ 2 := by
                have h1 := sum_cluster_membership_le π a
                have h2 := sum_cluster_membership_le π b
                omega
      calc
        _ ≤ ∑ g, ((externalLabels π h g).card + (externalLabels π [q] g).card) := by
          apply Finset.sum_le_sum
          intro g _
          rw [externalLabels_append]
          exact Finset.card_union_le _ _
        _ = _ := Finset.sum_add_distrib
        _ ≤ 2 * (h ++ [q]).length := by
          simp only [List.length_append, List.length_singleton]
          omega

end Screening

end SteinerLowerBound

module

public import SteinerLowerBound.MetricComparison.PublicModel

@[expose] public section

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical

structure PartialEmbedding (S T : Type*) where
  embed : S ↪ T
  project : T → Option S
  project_iff : ∀ t s, project t = some s ↔ t = embed s

namespace PartialEmbedding

variable {S T C : Type*} [Fintype S] [Fintype T]

def history (e : PartialEmbedding S T) (h : List (C × T)) : List (C × S) :=
  h.filterMap (fun q => (e.project q.2).map (fun s => (q.1, s)))

@[simp]
theorem history_append (e : PartialEmbedding S T) (h : List (C × T)) (q : C × T) :
    e.history (h ++ [q]) =
      e.history h ++ ((e.project q.2).map (fun s => (q.1, s))).toList := by
  simp only [history, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases e.project q.2 <;> rfl

theorem mem_history (e : PartialEmbedding S T) (h : List (C × T)) (c : C) (s : S) :
    (c, s) ∈ e.history h ↔ (c, e.embed s) ∈ h := by
  simp only [history, List.mem_filterMap]
  constructor
  · rintro ⟨⟨c', t⟩, hm, he⟩
    cases hp : e.project t with
    | none => simp [hp] at he
    | some s' =>
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have ht : t = e.embed s' := (e.project_iff t s').mp hp
      simpa only [ht] using hm
  · intro hm
    refine ⟨(c, e.embed s), hm, ?_⟩
    rw [(e.project_iff (e.embed s) s).mpr rfl]
    rfl

theorem mem_queried (e : PartialEmbedding S T) (h : List (C × T)) (c : C) (s : S) :
    s ∈ TwoAnchor.queried (e.history h) c ↔ e.embed s ∈ TwoAnchor.queried h c := by
  simp only [TwoAnchor.queried, Finset.mem_filter, Finset.mem_univ, true_and, e.mem_history]

noncomputable def lift (e : PartialEmbedding S T) (F : C → Finset S) (c : C) : Finset T :=
  (F c).map e.embed

@[simp]
theorem mem_lift (e : PartialEmbedding S T) (F : C → Finset S) (c : C) (s : S) :
    e.embed s ∈ e.lift F c ↔ s ∈ F c := by
  classical
  simp [lift]

theorem active (e : PartialEmbedding S T) (F : C → Finset S)
    (h : List (C × T)) (c : C) :
    TwoAnchor.active (e.lift F) h c ↔ TwoAnchor.active F (e.history h) c := by
  classical
  simp only [TwoAnchor.active, lift, Finset.card_map]
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro s hf
    exact (e.mem_queried h c s).mpr
      (hs (Finset.mem_map.mpr ⟨s, hf, rfl⟩))
  · rintro ⟨hc, hs⟩
    refine ⟨hc, ?_⟩
    intro t ht
    obtain ⟨s, hf, rfl⟩ := Finset.mem_map.mp ht
    exact (e.mem_queried h c s).mp (hs hf)

theorem mem_blocked (e : PartialEmbedding S T) (F : C → Finset S)
    (h : List (C × T)) (c : C) (s : S) :
    e.embed s ∈ TwoAnchor.blocked (e.lift F) h c ↔
      s ∈ TwoAnchor.blocked F (e.history h) c := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp [TwoAnchor.blocked, history]
  | append_singleton h q ih =>
    rcases q with ⟨c', t⟩
    rw [e.history_append]
    cases hp : e.project t with
    | none =>
      have ht : t ≠ e.embed s := by
        intro he
        have hh := (e.project_iff t s).mpr he
        rw [hp] at hh
        cases hh
      simp only [hp, Option.map_none, Option.toList_none, List.append_nil,
        blocked_append_mem, ih, Prod.mk.injEq, ht, and_false, false_and, or_false]
    | some s' =>
      have ht : t = e.embed s' := (e.project_iff t s').mp hp
      simp only [hp, Option.map_some, Option.toList_some, ht, blocked_append_mem, ih,
        Prod.mk.injEq, e.embed.injective.eq_iff, e.mem_lift, e.active]

theorem disjoint_blocked (e : PartialEmbedding S T) (F H : C → Finset S)
    (h : List (C × T)) (c : C) :
    Disjoint (e.lift H c) (TwoAnchor.blocked (e.lift F) h c) ↔
      Disjoint (H c) (TwoAnchor.blocked F (e.history h) c) := by
  classical
  simp only [Finset.disjoint_left]
  constructor
  · intro hd s hs hb
    exact hd ((e.mem_lift H c s).mpr hs) ((e.mem_blocked F h c s).mpr hb)
  · intro hd t ht hb
    obtain ⟨s, hs, rfl⟩ := Finset.mem_map.mp ht
    exact hd hs ((e.mem_blocked F h c s).mp hb)

theorem answer (e : PartialEmbedding S T) (F H : C → Finset S)
    (h : List (C × T)) (c : C) (s : S) :
    TwoAnchor.answer (e.lift F) (e.lift H) h c (e.embed s) =
      TwoAnchor.answer F H (e.history h) c s := by
  simp only [TwoAnchor.answer, e.mem_lift, e.active, e.disjoint_blocked]

theorem answer_outside (e : PartialEmbedding S T) (F H : C → Finset S)
    (h : List (C × T)) (c : C) (t : T) (ht : e.project t = none) :
    TwoAnchor.answer (e.lift F) (e.lift H) h c t = false := by
  classical
  have hn (L : C → Finset S) : t ∉ e.lift L c := by
    intro hm
    obtain ⟨s, _, hs⟩ := Finset.mem_map.mp hm
    have hp := (e.project_iff t s).mpr hs.symm
    rw [ht] at hp
    cases hp
  simp [TwoAnchor.answer, hn F, hn H]

end PartialEmbedding

end SteinerLowerBound.MetricComparison

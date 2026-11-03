module

public import SteinerUpperBound.Matching.Padded.CacheFacts

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

structure Records (s : Cache S Q) : Prop where
  unique : ∀ v, ((s.known v).map Entry.edge).Nodup
  valid : ∀ v x, x ∈ s.known v →
    x.source.1 = v ∧ EntryValid S Q x ∧ s.assigned x.edge = some x.rank
  complete : ∀ v e, e ∈ (s.known v).map Entry.edge ↔
    s.assigned e ≠ none ∧ G.Incident e v

theorem empty_records : Records S Q (empty S Q) := by
  constructor <;> simp [empty]

theorem incident_test {source reverse : Slot S.length} {e : E}
    (ht : S.test source = some (e, reverse)) (v : V) :
    G.Incident e v ↔ v = source.1 ∨ v = reverse.1 := by
  obtain ⟨d, hd, he, hr⟩ := S.test_complete source e reverse ht
  rw [← hd, ← hr, S.place_vertex, S.place_vertex, Padded.tail_reverse, ← he]
  cases d with | mk f b => cases b <;> simp [Graph.Incident, Graph.tail, Graph.head, eq_comm, or_comm]

theorem assign_known_edges (s : Cache S Q) {source reverse : Slot S.length} {e : E}
    (r : Fin Q) (ht : S.test source = some (e, reverse)) (v : V) :
    ((assign S Q s source reverse e r).known v).map Entry.edge =
      if G.Incident e v then e :: (s.known v).map Entry.edge else (s.known v).map Entry.edge := by
  classical
  have hne := (S.test_incident ht).2.2
  have hsource := (S.test_incident ht).1
  have hreverse := (S.test_incident ht).2.1
  by_cases hv : v = source.1
  · have hvr : v ≠ reverse.1 := fun h => hne (hv.symm.trans h)
    have hi : G.Incident e v := by rw [hv]; exact (S.test_incident ht).1
    simp [assign, hv, hne, hsource]
  · by_cases hvr : v = reverse.1
    · have hi : G.Incident e v := by rw [hvr]; exact (S.test_incident ht).2.1
      simp [assign, hvr, hreverse]
    · have hi : ¬ G.Incident e v := by
        rw [incident_test S ht v]
        exact not_or.mpr ⟨hv, hvr⟩
      simp [assign, Function.update_of_ne hv, Function.update_of_ne hvr, hi]

theorem assign_records (s : Cache S Q) (hs : Records S Q s)
    {source reverse : Slot S.length} {e : E} (r : Fin Q)
    (ht : S.test source = some (e, reverse)) (hn : s.assigned e = none) :
    Records S Q (assign S Q s source reverse e r) := by
  classical
  have hne := (S.test_incident ht).2.2
  have habsent (v : V) : e ∉ (s.known v).map Entry.edge :=
    fun h => ((hs.complete v e).mp h).1 hn
  have hold (v : V) (x : Entry S Q) (hx : x ∈ s.known v) :
      x.source.1 = v ∧ EntryValid S Q x ∧
        (assign S Q s source reverse e r).assigned x.edge = some x.rank := by
    have hp := hs.valid v x hx
    exact ⟨hp.1, hp.2.1, assign_extends S Q s source reverse e r hn x.edge x.rank hp.2.2⟩
  constructor
  · intro v
    rw [assign_known_edges S Q s r ht v]
    split_ifs
    · exact List.nodup_cons.mpr ⟨habsent v, hs.unique v⟩
    · exact hs.unique v
  · intro v x hx
    by_cases hv : v = source.1
    · have hvr : v ≠ reverse.1 := fun h => hne (hv.symm.trans h)
      have hm : x = (⟨source, reverse, e, r⟩ : Entry S Q) ∨ x ∈ s.known v := by
        simpa [assign, hv, hne] using hx
      rcases hm with heq | hm
      · subst x
        exact ⟨hv.symm, ht, by simp [assign]⟩
      · exact hold v x hm
    · by_cases hvr : v = reverse.1
      · have hm : x = (⟨reverse, source, e, r⟩ : Entry S Q) ∨ x ∈ s.known v := by
          simpa [assign, hvr] using hx
        rcases hm with heq | hm
        · subst x
          exact ⟨hvr.symm, S.test_reverse ht, by simp [assign]⟩
        · exact hold v x hm
      · have hm : x ∈ s.known v := by
          simpa [assign, Function.update_of_ne hv, Function.update_of_ne hvr] using hx
        exact hold v x hm
  · intro v f
    rw [assign_known_edges S Q s r ht v]
    by_cases hfe : f = e
    · subst f
      by_cases hi : G.Incident e v <;> simp [hi, habsent v, assign, hn]
    · by_cases hi : G.Incident e v <;>
        simp only [hi, ↓reduceIte, List.mem_cons, hfe, false_or, hs.complete,
          assign, Function.update_of_ne hfe]

theorem known_length_le [Fintype E] (s : Cache S Q) (hs : Records S Q s) (v : V) :
    (s.known v).length ≤ Fintype.card E := by
  simpa only [List.length_map] using (hs.unique v).length_le_card

end SteinerUpperBound.Matching.Padded.Cache

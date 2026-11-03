module

public import SteinerUpperBound.Matching.Padded.IdealFacts

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Cache

open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ)

structure Ready (s : Cache S Q) : Prop where
  unique : ∀ v, ((s.ready v).toList.map Entry.edge).Nodup
  valid : ∀ v x, x ∈ (s.ready v).toList →
    x.source.1 = v ∧ EntryValid S Q x ∧ s.assigned x.edge = some x.rank
  ordered : ∀ v, (s.ready v).toList.Pairwise (fun x y => x.rank.val ≤ y.rank.val)
  covers : ∀ v x, x ∈ s.known v → x.rank.val < boundary S Q s v →
    ∃ y ∈ (s.ready v).toList, y.edge = x.edge

theorem empty_ready : Ready S Q (empty S Q) := by
  constructor <;> simp [empty]

theorem assign_ready (s : Cache S Q) (hs : Ready S Q s)
    {source reverse : Slot S.length} {e : E} (r : Fin Q)
    (ht : S.test source = some (e, reverse)) (hn : s.assigned e = none)
    (hr : lower S Q s e ≤ r.val) :
    Ready S Q (assign S Q s source reverse e r) := by
  classical
  have hne := (S.test_incident ht).2.2
  have hsource : boundary S Q s source.1 ≤ r.val :=
    (lower_at_endpoint S Q s e source.1 (S.test_incident ht).1).trans hr
  have hreverse : boundary S Q s reverse.1 ≤ r.val :=
    (lower_at_endpoint S Q s e reverse.1 (S.test_incident ht).2.1).trans hr
  refine ⟨hs.unique, ?_, hs.ordered, ?_⟩
  · intro v x hx
    have hp := hs.valid v x hx
    exact ⟨hp.1, hp.2.1, assign_extends S Q s source reverse e r hn x.edge x.rank hp.2.2⟩
  · intro v x hx hlow
    change x.rank.val < boundary S Q s v at hlow
    have hxold : x ∈ s.known v := by
      by_cases hv : v = source.1
      · have hm : x = (⟨source, reverse, e, r⟩ : Entry S Q) ∨ x ∈ s.known v := by
          simpa [assign, hv, hne] using hx
        rcases hm with heq | hm
        · subst x
          rw [hv] at hlow
          change r.val < boundary S Q s source.1 at hlow
          omega
        · exact hm
      · by_cases hvr : v = reverse.1
        · have hm : x = (⟨reverse, source, e, r⟩ : Entry S Q) ∨ x ∈ s.known v := by
            simpa [assign, hvr] using hx
          rcases hm with heq | hm
          · subst x
            rw [hvr] at hlow
            change r.val < boundary S Q s reverse.1 at hlow
            omega
          · exact hm
        · simpa [assign, Function.update_of_ne hv, Function.update_of_ne hvr] using hx
    exact hs.covers v x hxold hlow

noncomputable def rebuild (height : ℕ) (v : V) (newLevel : ℕ) (s : Cache S Q) : Cache S Q :=
  let sorted := Sort.array (fun x y : Entry S Q => decide (x.rank.val ≤ y.rank.val)) height (s.known v)
  { s with level := Function.update s.level v newLevel,
           ready := Function.update s.ready v sorted.value }

theorem rebuild_ready (height : ℕ) (v : V) (newLevel : ℕ) (s : Cache S Q)
    (hs : Ready S Q s) (hr : Records S Q s) (hlen : (s.known v).length ≤ 2 ^ height) :
    Ready S Q (rebuild S Q height v newLevel s) := by
  classical
  let : IsTrans (Entry S Q) (fun x y => x.rank.val ≤ y.rank.val) :=
    ⟨fun _ _ _ h h' => h.trans h'⟩
  let : Std.Total (fun x y : Entry S Q => x.rank.val ≤ y.rank.val) :=
    ⟨fun _ _ => le_total _ _⟩
  let sorted := Sort.array (fun x y : Entry S Q => decide (x.rank.val ≤ y.rank.val)) height (s.known v)
  have hp : sorted.value.toList.Perm (s.known v) := Sort.array_perm _ height _
  have ho : sorted.value.toList.Pairwise (fun x y => x.rank.val ≤ y.rank.val) :=
    Sort.array_pairwise _ height _ hlen
  constructor
  · intro u
    by_cases hu : u = v
    · have huniq := (hp.map Entry.edge).nodup_iff.mpr (hr.unique v)
      simpa only [rebuild, hu, Function.update_self] using huniq
    · simpa only [rebuild, Function.update_of_ne hu] using hs.unique u
  · intro u x hx
    by_cases hu : u = v
    · have hm : x ∈ sorted.value.toList := by
        simpa only [rebuild, hu, Function.update_self] using hx
      have hv := hr.valid v x (hp.mem_iff.mp hm)
      simpa only [rebuild, hu] using hv
    · have hm : x ∈ (s.ready u).toList := by
        simpa only [rebuild, Function.update_of_ne hu] using hx
      exact hs.valid u x hm
  · intro u
    by_cases hu : u = v
    · simpa only [rebuild, hu, Function.update_self] using ho
    · simpa only [rebuild, Function.update_of_ne hu] using hs.ordered u
  · intro u x hx hlow
    by_cases hu : u = v
    · have hm : x ∈ s.known v := by simpa only [rebuild, hu] using hx
      refine ⟨x, ?_, rfl⟩
      have ha := hp.mem_iff.mpr hm
      simpa only [rebuild, hu, Function.update_self] using ha
    · have hm : x ∈ s.known u := hx
      have hl : x.rank.val < boundary S Q s u := by
        simpa only [boundary, rebuild, Function.update_of_ne hu] using hlow
      obtain ⟨y, hy, he⟩ := hs.covers u x hm hl
      refine ⟨y, ?_, he⟩
      simpa only [rebuild, Function.update_of_ne hu] using hy

end SteinerUpperBound.Matching.Padded.Cache

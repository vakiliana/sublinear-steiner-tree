module

public import SteinerUpperBound.Matching.Padded.RefinementTypes

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T)

theorem CacheMatch.withMemory {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (memory : I.Memory) :
    J.CacheMatch I s { t with memory := memory } :=
  ⟨h.level, h.assigned, h.stored, h.known, h.ready, h.prepared, h.requests⟩

theorem CacheMatch.available {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) (cursor : ℕ) :
    Runtime.available C I (J.vertex v) cursor t =
      (Cache.available S C.rankCard v cursor s).map J.liftEntry := by
  unfold Runtime.available Cache.available
  rw [h.ready_lookup J I v cursor, h.boundary J I v]
  cases hx : (s.ready v)[cursor]? with
  | none => rfl
  | some x =>
    by_cases hr : x.rank.val < Cache.boundary S C.rankCard s v <;>
      simp only [Option.map_some, Option.map_none, Option.bind_some, liftEntry, hr, ↓reduceIte]

theorem finish_match {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) (xs : List (Entry S C.rankCard)) (memory : I.Memory) :
    J.CacheMatch I (Cache.finish S C.rankCard C.sortHeight v s xs).value
      (Runtime.finish C I (J.vertex v) t memory (xs.map J.liftEntry)).value ∧
      (Runtime.finish C I (J.vertex v) t memory (xs.map J.liftEntry)).operations =
        (Cache.finish S C.rankCard C.sortHeight v s xs).operations := by
  classical
  let a := Cache.commit S C.rankCard s xs
  let b := (xs.map J.liftEntry).foldl (Runtime.assign C I) { t with memory := memory }
  have hc : J.CacheMatch I a b := (h.withMemory J I memory).commit J I xs
  have hs := Sort.array_map J.liftEntry
    (fun x y : Entry S C.rankCard => decide (x.rank.val ≤ y.rank.val))
    (fun x y : Runtime.Copy C (Label := Label) => decide (x.rank.val ≤ y.rank.val))
    (fun _ _ => rfl) C.sortHeight (a.known v)
  have hb : b.known (J.vertex v) = (a.known v).map J.liftEntry := hc.known v
  constructor
  · constructor
    · intro u
      dsimp only [Runtime.finish, Cache.finish]
      by_cases hu : u = v
      · subst u
        simp only [Function.update_self, h.level]
      · have hraw : J.vertex u ≠ J.vertex v := J.vertex.injective.ne hu
        simpa only [Function.update_of_ne hu, Function.update_of_ne hraw] using hc.level u
    · intro e
      exact hc.assigned e
    · intro source
      exact hc.stored source
    · intro u
      exact hc.known u
    · intro u
      dsimp only [Runtime.finish, Cache.finish]
      by_cases hu : u = v
      · subst u
        simp only [Function.update_self]
        change (Sort.array _ C.sortHeight (b.known (J.vertex v))).value.toList = _
        rw [hb]
        exact hs.1
      · have hraw : J.vertex u ≠ J.vertex v := J.vertex.injective.ne hu
        simpa only [Function.update_of_ne hu, Function.update_of_ne hraw] using hc.ready u
    · intro u
      exact hc.prepared u
    · intro u
      exact hc.requests u
  · dsimp only [Runtime.finish, Cache.finish]
    change 32 * (xs.map J.liftEntry).length +
      (Sort.array _ C.sortHeight (b.known (J.vertex v))).operations + 4 = _
    rw [hb, List.length_map, hs.2]

theorem CacheMatch.requests_update {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) :
    J.CacheMatch I { s with requests := Function.update s.requests v (s.requests v + 1) }
      { t with requests := Function.update t.requests (J.vertex v) (t.requests (J.vertex v) + 1) } := by
  classical
  refine ⟨h.level, h.assigned, h.stored, h.known, h.ready, h.prepared, ?_⟩
  intro u
  by_cases hu : u = v
  · subst u; simp only [Function.update_self, h.requests]
  · have hraw : J.vertex u ≠ J.vertex v := J.vertex.injective.ne hu
    simpa only [Function.update_of_ne hu, Function.update_of_ne hraw] using h.requests u

theorem CacheMatch.prepared_update {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) (memory : I.Memory) :
    J.CacheMatch I { s with prepared := Function.update s.prepared v true }
      { t with prepared := Function.update t.prepared (J.vertex v) true, memory := memory } := by
  classical
  refine ⟨h.level, h.assigned, h.stored, h.known, h.ready, ?_, h.requests⟩
  intro u
  by_cases hu : u = v
  · subst u; simp only [Function.update_self]
  · have hraw : J.vertex u ≠ J.vertex v := J.vertex.injective.ne hu
    simpa only [Function.update_of_ne hu, Function.update_of_ne hraw] using h.prepared u

variable (m : M → ℝ) (bits : T → Bool) (K : J.Contract I m bits)

theorem StateMatch.requests_update {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.StateMatch I m bits K s t) (v : V) :
    J.StateMatch I m bits K { s with requests := Function.update s.requests v (s.requests v + 1) }
      { t with requests := Function.update t.requests (J.vertex v) (t.requests (J.vertex v) + 1) } :=
  ⟨h.cache.requests_update J I v, h.memory⟩

theorem StateMatch.prepared_update {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.StateMatch I m bits K s t) (v : V) (memory : I.Memory)
    (hmemory : K.Inv memory ∧ K.Ready memory v ∧
      ∀ u, K.Ready t.memory u → K.Ready memory u) :
    J.StateMatch I m bits K { s with prepared := Function.update s.prepared v true }
      { t with prepared := Function.update t.prepared (J.vertex v) true, memory := memory } := by
  classical
  refine ⟨h.cache.prepared_update J I v memory, hmemory.1, ?_⟩
  intro u hu
  by_cases huv : u = v
  · subst u
    exact hmemory.2.1
  · have hold : s.prepared u = true := by simpa only [Function.update_of_ne huv] using hu
    exact hmemory.2.2 u (h.memory.2 u hold)

end SteinerUpperBound.Matching.Padded.Presentation

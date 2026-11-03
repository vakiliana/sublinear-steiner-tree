module

public import SteinerUpperBound.Matching.Padded.PrimitiveDomination
public import SteinerUpperBound.Matching.Padded.SortMap

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open _root_.SteinerUpperBound.Matching.Graph
open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)

def parameters : Parameters S :=
  ⟨C.Nstar, by rw [← J.size_eq]; exact P.two_le, by rw [← J.size_eq]; exact P.size_le⟩

theorem parameters_rankCard : J.parameters.rankCard = C.rankCard := rfl

def liftEntry (x : Entry S C.rankCard) : Runtime.Copy C (Label := Label) :=
  ⟨J.slot x.source, J.slot x.reverse, J.label x.edge, x.rank⟩

def liftDirected (d : Directed E) : Label × Vertex := (J.label d.1, J.vertex (G.head d))

theorem liftDirected_injective : Function.Injective J.liftDirected := by
  intro d e h
  have he : d.1 = e.1 := J.label.injective (congrArg Prod.fst h)
  have hh : G.head d = G.head e := J.vertex.injective (congrArg Prod.snd h)
  exact G.directed_eq_of_head he hh

def liftInvocation (c : Invocation E) : RawCausal.Invocation Label Vertex :=
  ⟨J.liftDirected c.state, c.ancestors.map J.liftDirected, c.cached⟩

variable (I : Runtime.Primitives C.length Label M T)

structure CacheMatch (s : Cache S C.rankCard) (t : Runtime.State C I) : Prop where
  level : ∀ v, t.level (J.vertex v) = s.level v
  assigned : ∀ e, t.assigned (J.label e) = s.assigned e
  stored : ∀ a, t.stored (J.slot a) = s.stored a
  known : ∀ v, t.known (J.vertex v) = (s.known v).map J.liftEntry
  ready : ∀ v, (t.ready (J.vertex v)).toList = (s.ready v).toList.map J.liftEntry
  prepared : ∀ v, t.prepared (J.vertex v) = s.prepared v
  requests : ∀ v, t.requests (J.vertex v) = s.requests v

variable (m : M → ℝ) (b : T → Bool) (K : J.Contract I m b)

def MemoryMatch (s : Cache S C.rankCard) (memory : I.Memory) : Prop :=
  K.Inv memory ∧ ∀ v, s.prepared v = true → K.Ready memory v

structure StateMatch (s : Cache S C.rankCard) (t : Runtime.State C I) : Prop where
  cache : J.CacheMatch I s t
  memory : J.MemoryMatch I m b K s t.memory

theorem empty_match :
    J.StateMatch I m b K (Cache.empty S C.rankCard) (Runtime.empty C I) := by
  refine ⟨?_, K.initial, ?_⟩
  · constructor <;> intro x <;> rfl
  · intro v hv
    cases hv

theorem CacheMatch.boundary {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) :
    Runtime.boundary C I t (J.vertex v) = Cache.boundary S C.rankCard s v := by
  simp only [Runtime.boundary, Cache.boundary, h.level]

theorem CacheMatch.ready_lookup {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (v : V) (cursor : ℕ) :
    (t.ready (J.vertex v))[cursor]? = ((s.ready v)[cursor]?).map J.liftEntry := by
  rw [← Array.getElem?_toList, h.ready, List.getElem?_map, Array.getElem?_toList]

theorem CacheMatch.assign {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (x : Entry S C.rankCard) :
    J.CacheMatch I (Cache.assign S C.rankCard s x.source x.reverse x.edge x.rank)
      (Runtime.assign C I t (J.liftEntry x)) := by
  classical
  constructor
  · intro v
    exact h.level v
  · intro e
    simp only [Runtime.assign, Cache.assign, liftEntry, Function.update_apply]
    by_cases he : e = x.edge
    · subst e; simp
    · have hlabel : J.label e ≠ J.label x.edge := J.label.injective.ne he
      simp only [he, hlabel, ↓reduceIte]
      exact h.assigned e
  · intro a
    simp only [Runtime.assign, Cache.assign, liftEntry, Function.update_apply]
    by_cases har : a = x.reverse
    · subst a; simp
    · have hr : J.slot a ≠ J.slot x.reverse := J.slot_injective.ne har
      by_cases has : a = x.source
      · subst a; simp only [hr, har, ↓reduceIte]
      · have hs : J.slot a ≠ J.slot x.source := J.slot_injective.ne has
        simp only [hr, har, hs, has, ↓reduceIte]
        exact h.stored a
  · intro v
    by_cases hr : v = x.reverse.1
    · subst v
      simp only [Runtime.assign, Cache.assign, liftEntry, slot_vertex, Function.update_self,
        h.known, List.map_cons]
    · have hrawr : J.vertex v ≠ J.vertex x.reverse.1 := J.vertex.injective.ne hr
      by_cases hs : v = x.source.1
      · subst v
        simp only [Runtime.assign, Cache.assign, liftEntry, slot_vertex, Function.update_of_ne hr,
          Function.update_of_ne hrawr, Function.update_self, h.known, List.map_cons]
      · have hraws : J.vertex v ≠ J.vertex x.source.1 := J.vertex.injective.ne hs
        simpa only [Runtime.assign, Cache.assign, liftEntry, slot_vertex, Function.update_of_ne hr,
          Function.update_of_ne hs, Function.update_of_ne hrawr, Function.update_of_ne hraws] using h.known v
  · intro v
    exact h.ready v
  · intro v
    exact h.prepared v
  · intro v
    exact h.requests v

theorem memory_slot_preserved (s : Cache S C.rankCard) (memory memory' : I.Memory)
    (h : J.MemoryMatch I m b K s memory) (hi : K.Inv memory')
    (hr : ∀ v, K.Ready memory v → K.Ready memory' v) :
    J.MemoryMatch I m b K s memory' :=
  ⟨hi, fun v hv => hr v (h.2 v hv)⟩

theorem StateMatch.assign {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.StateMatch I m b K s t) (x : Entry S C.rankCard) :
    J.StateMatch I m b K (Cache.assign S C.rankCard s x.source x.reverse x.edge x.rank)
      (Runtime.assign C I t (J.liftEntry x)) :=
  ⟨h.cache.assign J I x, h.memory⟩

theorem CacheMatch.commit {s : Cache S C.rankCard} {t : Runtime.State C I}
    (h : J.CacheMatch I s t) (xs : List (Entry S C.rankCard)) :
    J.CacheMatch I (Cache.commit S C.rankCard s xs)
      ((xs.map J.liftEntry).foldl (Runtime.assign C I) t) := by
  induction xs generalizing s t with
  | nil => exact h
  | cons x xs ih => exact ih (h.assign J I x)

end SteinerUpperBound.Matching.Padded.Presentation

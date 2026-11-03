module

public import SteinerUpperBound.Matching.Padded.SelectedDomination
public import SteinerUpperBound.Matching.Padded.DominationTools
public import SteinerUpperBound.Matching.Padded.IteratorCorrect

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Runtime

variable {Vertex Label M T : Type*} (C : Config Vertex) (I : Primitives C.length Label M T)

theorem fold_assign_memory (xs : List (Copy C (Label := Label))) (t : State C I) :
    (xs.foldl (assign C I) t).memory = t.memory := by
  induction xs generalizing t with
  | nil => rfl
  | cons x xs ih => exact ih (assign C I t x)

theorem finish_memory (v : Vertex) (t : State C I) (memory : I.Memory)
    (xs : List (Copy C (Label := Label))) :
    (finish C I v t memory xs).value.memory = memory :=
  fold_assign_memory C I xs { t with memory := memory }

end SteinerUpperBound.Matching.Padded.Runtime

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (b : T → Bool)
    (K : J.Contract I m b) (D : J.Deterministic I m b K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m b K A counter)

include D resources

theorem collect_dominates (a stop : ℕ) (v : V)
    (s : Cache S C.rankCard) (t : Runtime.State C I)
    (hmatch : J.StateMatch I m b K s t) (hprepared : s.prepared v = true) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (Cache.collect S C.rankCard C.rankCard_pos a stop v s)
      (Runtime.collect C I a stop (J.vertex v) t)
      (fun entries answer => answer.1 = entries.map J.liftEntry ∧
        J.MemoryMatch I m b K s answer.2) := by
  rw [Cache.collect, Runtime.collect]
  rw [← J.length_eq v]
  apply Causal.Dominates.bind m b counter (Command.charge A) A.rate _ _ _ _ Eq _
    (Causal.compile_dominates m b counter A resources.rate _)
  intro selected rawSelected hselected
  subst rawSelected
  apply Causal.Dominates.forEach m b counter (Command.charge A) A.rate _ _ _
  · intro i _ entries answer h
    exact collectStep_dominates J I m b K D A counter resources a stop v i s t
      entries answer hmatch.cache h.2 hprepared h.1
  · exact ⟨rfl, hmatch.memory⟩

theorem extend_dominates (v : V) (s : Cache S C.rankCard) (t : Runtime.State C I)
    (hmatch : J.StateMatch I m b K s t) (hprepared : s.prepared v = true) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (Cache.extend S C.rankCard C.rankCard_pos C.sortHeight v s)
      (Runtime.extend C I (J.vertex v) t) (J.StateMatch I m b K) := by
  rw [Cache.extend, Runtime.extend]
  simp only [hmatch.cache.boundary J I v, hmatch.cache.level v]
  by_cases hb : Buckets.bound (s.level v + 1) ≤ C.rankCard
  · simp only [hb, ↓reduceIte]
    apply Causal.Dominates.bind m b counter (Command.charge A) A.rate _ _ _ _ _ _
      (collect_dominates J I m b K D A counter resources _ _ v s t hmatch hprepared)
    intro entries answer hanswer
    obtain ⟨rawEntries, memory⟩ := answer
    dsimp only at hanswer
    rcases hanswer with ⟨hentries, hmemory⟩
    subst rawEntries
    have hf := finish_match J I hmatch.cache v entries memory
    apply Causal.Dominates.spend m b counter (Command.charge A) A.rate
      (.arithmetic (Cache.finish S C.rankCard C.sortHeight v s entries).operations)
      (Runtime.finish C I (J.vertex v) t memory (entries.map J.liftEntry)).operations _ _ _
      (by simp only [Command.charge, hf.2, resources.rate, le_refl])
    apply Causal.Dominates.ret m b counter (Command.charge A) A.rate
    refine ⟨hf.1, ?_⟩
    rw [Runtime.finish_memory]
    have hp : (Cache.finish S C.rankCard C.sortHeight v s entries).value.prepared = s.prepared :=
      (Cache.commit_administration S C.rankCard s entries).1
    exact ⟨hmemory.1, fun u hu => hmemory.2 u (by simpa only [hp] using hu)⟩
  · simp only [hb, ↓reduceIte]
    exact Causal.Dominates.ret m b counter (Command.charge A) A.rate s t _ hmatch

end SteinerUpperBound.Matching.Padded.Presentation

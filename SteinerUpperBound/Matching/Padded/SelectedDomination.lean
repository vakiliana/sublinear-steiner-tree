module

public import SteinerUpperBound.Matching.Padded.RefinementMetadata

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Presentation

open scoped Classical

variable {V E Vertex Label M T : Type*} {G : Graph V E} {S : Slots G} [Fintype V]
    {P : Parameters S} {C : Runtime.Config Vertex} (J : Presentation (Label := Label) S P C)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (b : T → Bool)
    (K : J.Contract I m b) (D : J.Deterministic I m b K)
    (A : Account S) (counter : Causal.Counter) (resources : J.Resources I m b K A counter)

def HitMatch (s : Cache S C.rankCard) (hit : Option (Entry S C.rankCard))
    (answer : Option (Runtime.Copy C (Label := Label)) × I.Memory) : Prop :=
  answer.1 = hit.map J.liftEntry ∧ J.MemoryMatch I m b K s answer.2

include D resources

theorem selectedStep_dominates (a stop : ℕ) (v : V) (i : ℕ)
    (s : Cache S C.rankCard) (t : Runtime.State C I) (memory : I.Memory)
    (hcache : J.CacheMatch I s t) (hmemory : J.MemoryMatch I m b K s memory)
    (hprepared : s.prepared v = true) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (Cache.selectedStep S C.rankCard C.rankCard_pos a stop v i s)
      (Runtime.selectedStep C I a stop (J.vertex v) i t memory)
      (J.HitMatch I m b K s) := by
  classical
  by_cases hi : i < S.length v
  · have hri : i < C.length (J.vertex v) := by simpa only [← J.length_eq v] using hi
    let source : Slot S.length := ⟨v, ⟨i, hi⟩⟩
    have hsource : (⟨J.vertex v, ⟨i, hri⟩⟩ : Slot C.length) = J.slot source :=
      congrArg (Sigma.mk (J.vertex v)) (Fin.ext rfl)
    rw [Cache.selectedStep, Runtime.selectedStep]
    simp only [hi, hri, ↓reduceDIte]
    rw [hsource]
    apply Causal.Dominates.bind m b counter (Command.charge A) A.rate
      (Command.testSlot S source) (I.slot (J.slot source) memory) _ _ _ _
      (slot_dominates J I m b K D A counter resources source memory hmemory.1
        (hmemory.2 v hprepared))
    intro hit answer hhit
    have hmem : J.MemoryMatch I m b K s answer.2 :=
      memory_slot_preserved J I m b K s memory answer.2 hmemory hhit.2.1 hhit.2.2
    rw [hhit.1]
    cases hit with
    | none =>
      exact Causal.Dominates.ret m b counter _ _ none (none, answer.2) _
        ⟨rfl, hmem⟩
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      simp only [Option.map_some]
      apply Causal.Dominates.spend m b counter (Command.charge A) A.rate (.arithmetic 12) 12 _ _ _
        (by simp only [Command.charge, resources.rate, le_refl])
      have hboundary : Runtime.boundary C I t (J.slot reverse).1 =
          Cache.boundary S C.rankCard s reverse.1 := by
        rw [slot_vertex]
        exact hcache.boundary J I reverse.1
      simp only [hcache.assigned e, hboundary]
      by_cases he : s.assigned e = none ∧ Cache.boundary S C.rankCard s reverse.1 ≤ a
      · simp only [he, ↓reduceIte]
        apply Causal.Dominates.bind m b counter (Command.charge A) A.rate
          (Command.liftArithmetic (S := S) (Range.sample C.rankCard C.rankCard_pos a stop))
          (Causal.compile (Range.sample C.rankCard C.rankCard_pos a stop)) _ _ _ _
          (Causal.compile_dominates m b counter A resources.rate _)
        intro rank rawRank hrank
        subst rawRank
        exact Causal.Dominates.ret m b counter _ _
          (some (⟨source, reverse, e, rank⟩ : Entry S C.rankCard))
          (some (J.liftEntry ⟨source, reverse, e, rank⟩), answer.2) _
          ⟨rfl, hmem⟩
      · simp only [he, ↓reduceIte]
        exact Causal.Dominates.ret m b counter _ _ none (none, answer.2) _
          ⟨rfl, hmem⟩
  · have hri : ¬ i < C.length (J.vertex v) := by simpa only [← J.length_eq v] using hi
    simp only [Cache.selectedStep, Runtime.selectedStep, hi, hri, ↓reduceDIte]
    exact Causal.Dominates.ret m b counter _ _ none (none, memory) _ ⟨rfl, hmemory⟩

theorem collectStep_dominates (a stop : ℕ) (v : V) (i : ℕ)
    (s : Cache S C.rankCard) (t : Runtime.State C I)
    (xs : List (Entry S C.rankCard)) (ys : List (Runtime.Copy C (Label := Label)) × I.Memory)
    (hcache : J.CacheMatch I s t) (hmemory : J.MemoryMatch I m b K s ys.2)
    (hprepared : s.prepared v = true) (hlist : ys.1 = xs.map J.liftEntry) :
    Causal.Dominates m b counter (Command.charge A) A.rate
      (Cache.collectStep S C.rankCard C.rankCard_pos a stop v s i xs)
      (Runtime.collectStep C I a stop (J.vertex v) t i ys)
      (fun entries answer => answer.1 = entries.map J.liftEntry ∧
        J.MemoryMatch I m b K s answer.2) := by
  rw [Cache.collectStep, Runtime.collectStep]
  apply Causal.Dominates.bind m b counter (Command.charge A) A.rate _ _ _ _ _ _
    (selectedStep_dominates J I m b K D A counter resources a stop v i s t ys.2
      hcache hmemory hprepared)
  intro hit answer hhit
  apply Causal.Dominates.spend m b counter (Command.charge A) A.rate (.arithmetic 2) 2 _ _ _
    (by simp only [Command.charge, resources.rate, le_refl])
  apply Causal.Dominates.ret m b counter _ _
  refine ⟨?_, hhit.2⟩
  rw [hlist, hhit.1]
  cases hit <;> rfl

end SteinerUpperBound.Matching.Padded.Presentation

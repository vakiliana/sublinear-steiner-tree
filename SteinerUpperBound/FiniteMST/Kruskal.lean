module

public import SteinerUpperBound.FiniteMST.Sorting

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.FiniteMST

open SteinerLowerBound QueryProgram SmallCoverProgram
open scoped Classical

variable {M Q : Type*} {m : ℕ}

def addEdge (a : Closure.Dense Bool m) (e : Edge m) : Closure.Dense Bool m :=
  put (put a (finProdFinEquiv ((ends e).1, (ends e).2)) true)
    (finProdFinEquiv ((ends e).2, (ends e).1)) true

theorem entry_addEdge (a : Closure.Dense Bool m) (e : Edge m) (x y : Fin m) :
    Closure.entry (addEdge a e) x y = true ↔
      Closure.entry a x y = true ∨
        (x = (ends e).1 ∧ y = (ends e).2) ∨ (x = (ends e).2 ∧ y = (ends e).1) := by
  unfold Closure.entry addEdge
  simp only [get_put, Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  split_ifs <;> aesop

structure State (m : ℕ) where
  adjacency : Closure.Dense Bool m
  cost : ℝ

noncomputable def step (d : Matrix m) (s : State m) (e : Edge m) : Code M Q (State m) :=
  (Closure.closure s.adjacency).bind (fun connected =>
    .tick 63 (.pure (if Closure.entry connected (ends e).1 (ends e).2 then s
      else ⟨addEdge s.adjacency e, s.cost + edgeWeight d e⟩)))

def stepRun (d : Matrix m) (s : State m) (e : Edge m) : Outcome (State m) :=
  (Closure.computed s.adjacency).combine ((Outcome.pure
    (if Closure.entry (Closure.computed s.adjacency).value (ends e).1 (ends e).2 then s
      else ⟨addEdge s.adjacency e, s.cost + edgeWeight d e⟩)).add 64 0 0 0)

theorem step_evaluates (oracle : M → ℝ) (bits : Q → Bool)
    (d : Matrix m) (s : State m) (e : Edge m) :
    Code.Evaluates oracle bits (step d s e) (stepRun d s e) :=
  Code.Evaluates.bind _ _ _ _ _ _ (Closure.closure_evaluates _ _ _)
    (Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 63)

def Represents (d : Matrix m) (s : State m) (G : SimpleGraph (Fin m)) : Prop :=
  (∀ x y, Closure.entry s.adjacency x y = true ↔ G.Adj x y) ∧
    s.cost = GraphCost.cost (weight d) G

theorem step_represents (d : Matrix m) (s : State m) (G : SimpleGraph (Fin m))
    (hs : Represents d s G) (e : Edge m) (he : valid e) :
    Represents d (stepRun d s e).value (SpanningForest.step G (sym e)) := by
  have hc := Closure.computed_correct s.adjacency hs.1 (ends e).1 (ends e).2
  by_cases hr : G.Reachable (ends e).1 (ends e).2
  · have hb := hc.mpr hr
    simpa only [stepRun, Outcome.combine, Outcome.add, Outcome.pure, hb, ↓reduceIte,
      SpanningForest.step, sym, SpanningForest.linked_mk, hr, ↓reduceIte] using hs
  · have hb : Closure.entry (Closure.computed s.adjacency).value (ends e).1 (ends e).2 = false :=
      Bool.eq_false_iff.mpr (fun h => hr (hc.mp h))
    have hne : (ends e).1 ≠ (ends e).2 := ne_of_lt he
    have hstep : SpanningForest.step G (sym e) = G ⊔ SimpleGraph.edge (ends e).1 (ends e).2 := by
      simp only [SpanningForest.step, sym, SpanningForest.linked_mk, hr, ↓reduceIte, SimpleGraph.edge]
    rw [hstep]
    change Represents d
      (if Closure.entry (Closure.computed s.adjacency).value (ends e).1 (ends e).2 then s
      else ⟨addEdge s.adjacency e, s.cost + edgeWeight d e⟩) _
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · intro x y
      rw [entry_addEdge, hs.1 x y, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      aesop
    · have hcost := SpanningForest.cost_step (weight d) G (sym e)
      rw [hstep] at hcost
      simp only [sym, SpanningForest.linked_mk, hr, ↓reduceIte] at hcost
      change s.cost + edgeWeight d e = _
      rw [hs.2, ← weight_sym_valid d e he]
      exact hcost.symm

theorem folded_represents (d : Matrix m) (l : List (Edge m))
    (hv : ∀ e ∈ l, valid e) (s : State m) (G : SimpleGraph (Fin m)) (hs : Represents d s G) :
    Represents d (Code.folded (stepRun d) l s).value (SpanningForest.run (l.map sym) G) := by
  induction l generalizing s G with
  | nil => exact hs
  | cons e l ih =>
      have hh := step_represents d s G hs e (hv e List.mem_cons_self)
      have ht := ih (fun f hf => hv f (List.mem_cons_of_mem _ hf)) _ _ hh
      exact ht

theorem closure_work (a : Closure.Dense Bool m) :
    (Closure.computed a).work ≤ 32 * (m + 1) ^ 3 * (1 + Nat.log2 (m + 1)) := by
  by_cases hm : m = 0
  · subst m
    simp [Closure.computed, Closure.initialRun, Closure.iterated, Closure.squareRun,
      Closure.rounds, tabulated, Code.folded, allocated, Outcome.combine, Outcome.add, Outcome.pure]
  · exact (Closure.computed_work a (by omega)).trans (by gcongr; omega)

theorem stepRun_work (d : Matrix m) (s : State m) (e : Edge m) :
    (stepRun d s e).work ≤ 32 * (m + 1) ^ 3 * (1 + Nat.log2 (m + 1)) + 64 := by
  have hh := closure_work s.adjacency
  dsimp only [stepRun, Outcome.combine, Outcome.add, Outcome.pure]
  omega

theorem stepRun_resources (d : Matrix m) (s : State m) (e : Edge m) :
    (stepRun d s e).metricQueries = 0 ∧ (stepRun d s e).retentionQueries = 0 ∧
      (stepRun d s e).positiveReplies = 0 := by
  have hh := Closure.computed_resources s.adjacency
  simpa only [stepRun, Outcome.combine, Outcome.add, Outcome.pure, Nat.add_zero, Nat.zero_add] using hh

end SteinerUpperBound.FiniteMST

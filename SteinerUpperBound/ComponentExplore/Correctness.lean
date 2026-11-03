module

public import SteinerUpperBound.ComponentExplore.Loop

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open QueryProgram
open scoped Classical

set_option maxHeartbeats 800000

variable {V Q : Type*} [Fintype V]

theorem loop_projects (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V)
    (hroot : root ∈ retained b key l.toFinset) (fuel : ℕ) (s : Memory V Q)
    (hs : Memory.Valid b s)
    (hi : Invariant B (retainedGraph w b key l.toFinset a) l root s.graphState) :
    (loopResult w b key a B l fuel s).value.project =
      run B (retainedGraph w b key l.toFinset a) l fuel s.graphState := by
  induction fuel generalizing s with
  | zero =>
      have hcard := Memory.card_eq b s hs
      change s.points.toFinset.card = s.count at hcard
      by_cases hb : B < s.count <;>
        simp only [loopResult, run, hb, hcard, ite_true, ite_false, pending_value,
          Answer.project, Memory.graphState, Outcome.add, Outcome.combine, Outcome.pure]
  | succ fuel ih =>
      have hcard := Memory.card_eq b s hs
      change s.points.toFinset.card = s.count at hcard
      by_cases hb : B < s.count
      · simp only [loopResult, run, hb, hcard, ite_true, Answer.project, Memory.graphState,
          Outcome.add, Outcome.pure]
      · cases hp : (pendingResult s.points s.processed l).value with
        | none =>
            have hp' : pending l s.graphState.found s.graphState.done = none := by
              simpa only [Memory.graphState, pending_value] using hp
            change pending l s.points.toFinset s.processed.toFinset = none at hp'
            simp only [loopResult, run, hb, hcard, ite_false, hp, hp', Answer.project,
              Memory.graphState, Outcome.add, Outcome.combine, Outcome.pure]
        | some x =>
            have hp' : pending l s.graphState.found s.graphState.done = some x := by
              simpa only [Memory.graphState, pending_value] using hp
            change pending l s.points.toFinset s.processed.toFinset = some x at hp'
            obtain ⟨_, hx, hd⟩ := pendingResult_some s.points s.processed l hp
            have hxret := reachable_retained w b key l.toFinset a hroot (hi.reachable x hx)
            let n := (scanResult w b key a B x l (s.process x)).value
            have hvalid := scan_valid w b key a B x l (s.process x) (hs.process b s x hd)
            have hproj : n.graphState =
                ⟨scan B (retainedGraph w b key l.toFinset a) x l s.points.toFinset,
                  insert x s.processed.toFinset⟩ := by
              simpa only [n, Memory.process, List.toFinset_cons] using
                scan_projects w b key l.toFinset a B x l (s.process x)
                  (hs.process b s x hd) hxret hx (fun y hy => List.mem_toFinset.mpr hy)
            have hnext : Invariant B (retainedGraph w b key l.toFinset a) l root n.graphState := by
              rw [hproj]
              exact advance_invariant B _ l root s.graphState hi x hx
                (retainedGraph_support w b key l.toFinset a)
            have hr := ih n hvalid hnext
            rw [hproj] at hr
            simpa only [loopResult, run, hb, hcard, ite_false, hp, hp', n, Answer.project,
              Memory.graphState, Outcome.add, Outcome.combine] using hr

def initial (root : V) (c : Cache Q) : Memory V Q :=
  ⟨[root], [], 1, c⟩

noncomputable def program (key : V → Q) (a : ℝ) (B : ℕ) (l : List V)
    (root : V) (c : Cache Q) : Code (Sym2 V) Q (Answer V Q) :=
  .tick 3 (loopProgram key a B l (B + 1) (initial root c))

noncomputable def result (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) : Outcome (Answer V Q) :=
  (loopResult w b key a B l (B + 1) (initial root c)).add 4 0 0 0

theorem program_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) :
    Code.Evaluates w b (program key a B l root c) (result w b key a B l root c) := by
  intro F
  exact loop_evaluates w b key a B l (B + 1) (initial root c) (fun o => F (o.add 4 0 0 0))

theorem initial_valid (b : Q → Bool) (root : V) (c : Cache Q) (hc : Cache.Correct b c) :
    Memory.Valid b (initial root c) :=
  ⟨by simp [initial], by simp [initial], rfl, hc⟩

theorem result_correct (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q)
    (hc : Cache.Correct b c) (hroot : root ∈ retained b key l.toFinset) :
    CorrectResult B (retainedGraph w b key l.toFinset a) root
      (result w b key a B l root c).value.project := by
  have hr : root ∈ l := List.mem_toFinset.mp (Finset.mem_filter.mp hroot).1
  have hi : Invariant B (retainedGraph w b key l.toFinset a) l root (initial root c).graphState := by
    refine ⟨by simp [initial, Memory.graphState], by simp [initial, Memory.graphState],
      ?_, ?_, by simp [initial, Memory.graphState], ?_⟩
    · simpa only [initial, Memory.graphState, List.toFinset_cons, List.toFinset_nil,
        Finset.insert_empty] using Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hr)
    · intro y hy
      have he : y = root := by simpa [initial, Memory.graphState] using hy
      subst y
      exact SimpleGraph.Reachable.refl _
    · simp [initial, Memory.graphState]
  have hp := loop_projects w b key a B l root hroot (B + 1) (initial root c)
    (initial_valid b root c hc) hi
  have hcorrect := initial_correct B (retainedGraph w b key l.toFinset a) l root hr
    (retainedGraph_support w b key l.toFinset a)
  simpa only [result, Outcome.add, initial, Memory.graphState, List.toFinset_cons,
    List.toFinset_nil, Finset.insert_empty] using hp ▸ hcorrect

theorem result_valid (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) (hc : Cache.Correct b c) :
    Memory.Valid b (result w b key a B l root c).value.memory :=
  loop_valid w b key a B l (B + 1) (initial root c) (initial_valid b root c hc)

theorem result_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) :
    (result w b key a B l root c).metricQueries ≤ (B + 1) * l.length := by
  simpa only [result, Outcome.add, Nat.zero_add] using
    loop_metric_queries w b key a B l (B + 1) (initial root c)

theorem result_positive (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) :
    (result w b key a B l root c).positiveReplies ≤ B := by
  have hp := loop_positive_potential w b key a B l (B + 1) (initial root c)
  have hz := loop_count w b key a B l (B + 1) (initial root c) (by simp [initial])
  change (loopResult w b key a B l (B + 1) (initial root c)).positiveReplies + 1 ≤ _ at hp
  simp only [result, Outcome.add, Nat.zero_add]
  omega

theorem result_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (l : List V) (root : V) (c : Cache Q) (hc : Cache.Correct b c) :
    (result w b key a B l root c).work ≤ 64 * (l.length + 1) * (B + 2) ^ 2 := by
  have hw := loop_work w b key a B l (B + 1) (initial root c)
    (initial_valid b root c hc) (by simp [initial]) (by simp [initial])
  simp only [result, Outcome.add, iterationBudget] at hw ⊢
  nlinarith [Nat.zero_le (B ^ 2 * l.length), Nat.zero_le (B * l.length)]

end SteinerUpperBound.ComponentExplore

module

public import SteinerLowerBound.Simulation.PublicModel

@[expose] public section

namespace SteinerLowerBound.Simulation

open scoped Classical
open HardDistribution

structure Report (Q Z T X : Type*) where
  result : Z
  transcript : List (Q × Screening.Reply)
  state : State T X

namespace Public

open MetricComparison.Public

variable {S G I C Z : Type*}
  [Fintype S] [Fintype G] [Fintype I] [Fintype C]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

noncomputable def cachedBit (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (cache : Cache (Candidate S C d))
    (h : List (Query (Terminal S G I) C)) (c : C) (u : Terminal S G I) : Bool :=
  decide (u ∈ fillers π F c ∨
    (TwoAnchor.active (fillers π F) (Screening.centerHistory h) c ∧
      ∃ x ∈ cache.kept, x.1 = c ∧
        Disjoint (support π d x)
          (TwoAnchor.blocked (fillers π F) (Screening.centerHistory h) c) ∧
        u ∈ support π d x))

noncomputable def answer (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (cache : Cache (Candidate S C d))
    (h : List (Query (Terminal S G I) C)) : Query (Terminal S G I) C → Reply
  | .tt u v => if u = v then .diagonal else if Screening.SameCluster π u v then .cluster else .far
  | .ct c u => if cachedBit π d F cache h c u then .unit else .far
  | .cc c c' => if c = c' then .diagonal else .far

noncomputable def notices (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S)
    (D t : ℕ) (h : List (Query (Terminal S G I) C))
    (q : Query (Terminal S G I) C) (a : Reply) (Q : Finset (Terminal S G I)) :
    Finset (Terminal S G I) :=
  Finset.univ.filter fun u => Screening.specialPosition (π u) ∧ u ∉ Q ∧
    ((∃ c, q = .ct c u ∧ a = .unit) ∨ D ≤ Screening.degree (h ++ [q]) u ∨
      t ≤ (Screening.counterLabels π (internalSupport (fun c => fillerNeighbors (F c)))
        (h ++ [q]) u).card)

theorem notices_actual (π : Equiv.Perm (Terminal S G I)) (F : C → Filler S)
    (H : C → Finset (Terminal S G I)) (D t : ℕ)
    (h : List (Query (Terminal S G I) C)) (q : Query (Terminal S G I) C)
    (Q : Finset (Terminal S G I)) :
    notices π F D t h q
      (Screening.queryAnswer π (internalSupport (fun c => fillerNeighbors (F c))) H h q) Q =
      Screening.noticeCandidates π (internalSupport (fun c => fillerNeighbors (F c)))
        H D t h q Q := by
  classical
  ext u
  constructor
  · intro hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
  · intro hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩

abbrev SimState (S G I C : Type*) (d : ℕ) :=
  State (Terminal S G I) (Candidate S C d)

abbrev SimReport (S G I C Z : Type*) (d : ℕ) :=
  Report (Query (Terminal S G I) C) Z (Terminal S G I) (Candidate S C d)

noncomputable def run (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) :
    DecisionTree (Query (Terminal S G I) C) Reply Z →
      List (Query (Terminal S G I) C) → SimState S G I C d →
        DecisionTree (Candidate S C d) Bool (SimReport S G I C Z d)
  | .leaf z, _, s => .leaf ⟨z, [], s⟩
  | .query q next, h, s =>
      if s.stop ≠ none then
        let r := onlineRun (fun _ _ => Screening.Reply.far) (.query q next) h
        .leaf ⟨r.1, r.2, s⟩
      else
        let a := answer π d F s.cache h q
        bind (noticeList (access π d F) (support π d) R
          (Screening.noticeOrder (notices π F D t h q a s.exposed)) s) fun s' =>
          bind (run π d F D t R (next a) (h ++ [q]) s') fun r =>
            .leaf {r with transcript := (q, a) :: r.transcript}

theorem run_spec (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) (tree : DecisionTree (Query (Terminal S G I) C) Reply Z)
    (h : List (Query (Terminal S G I) C)) (s : SimState S G I C d)
    (hs : Stable (access π d F) (support π d) R s) :
    Spec (fun r => r.state.cache) (fun r => Stable (access π d F) (support π d) R r.state)
      s.cache (run π d F D t R tree h s) := by
  induction tree generalizing h s with
  | leaf z => exact ⟨rfl, hs⟩
  | query q next ih =>
      rw [run]
      split_ifs with hstop
      · exact ⟨rfl, hs⟩
      · apply (noticeList_spec (access π d F) (support π d) (access_mono π d F)
          R _ s hs).bind
        intro s' hs'
        apply (ih (answer π d F s.cache h q) (h ++ [q]) s' hs').bind
        intro r hr
        exact ⟨rfl, hr⟩

noncomputable def tree (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    DecisionTree (Candidate S C d) Bool (SimReport S G I C Z d) :=
  run π d F D t R (mapQuestions orient algorithm) [] .initial

theorem tree_spec (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    Spec (fun r => r.state.cache) (fun r => Stable (access π d F) (support π d) R r.state)
      .empty (tree π d F D t R algorithm) :=
  run_spec π d F D t R _ [] .initial
    (initial_stable _ _ R (access_empty π d F))

theorem tree_valid (π : Equiv.Perm (Terminal S G I)) (d : ℕ) (F : C → Filler S)
    (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z) :
    Protocol.Valid (VisibleMass.region d F) (fun Q => Q.card ≤ 2 * R) ∅
      (tree π d F D t R algorithm) := by
  apply (tree_spec π d F D t R algorithm).valid
  intro r hr
  exact ⟨pull π r.state.requested,
    (pull_card_le π _).trans hr.1.requested_cap, hr.1.read_subset⟩

theorem tree_cache_consistent (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (o : Candidate S C d → Bool) :
    ((tree π d F D t R algorithm).output o).state.cache.Consistent o := by
  exact Spec.consistent (fun r : SimReport S G I C Z d => r.state.cache)
    (fun r => Stable (access π d F) (support π d) R r.state) .empty
    (tree π d F D t R algorithm) (tree_spec π d F D t R algorithm) o
    (Cache.empty_consistent o)

theorem tree_overflow_retained (π : Equiv.Perm (Terminal S G I)) (d : ℕ)
    (F : C → Filler S) (D t R : ℕ) (algorithm : DecisionTree (Queries S G I C) Reply Z)
    (o : Candidate S C d → Bool)
    (hstop : ((tree π d F D t R algorithm).output o).state.stop = some .closure) :
    R < d * retainedRead (tree π d F D t R algorithm) o := by
  have hs := Spec.output (fun r : SimReport S G I C Z d => r.state.cache)
    (fun r => Stable (access π d F) (support π d) R r.state) .empty
    (tree π d F D t R algorithm) (tree_spec π d F D t R algorithm) o
  have hov := closure_overflow _ (support π d) R d
    (fun x => (support_card π d x).le) _ hs hstop
  have hcount := Spec.kept_card (fun r : SimReport S G I C Z d => r.state.cache)
    (fun r => Stable (access π d F) (support π d) R r.state) .empty
    (tree π d F D t R algorithm) (tree_spec π d F D t R algorithm) o
  have hle : ((tree π d F D t R algorithm).output o).state.cache.kept.card ≤
      retainedRead (tree π d F D t R algorithm) o := by
    simpa [Cache.empty] using hcount
  exact hov.trans_le (Nat.mul_le_mul_left d hle)

end Public

end SteinerLowerBound.Simulation

module

public import SteinerLowerBound.MetricComparison.PublicQueries

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Padding

open scoped BigOperators Classical

structure Reduction (Qp Q A : Type*) where
  shape : Qp → A ⊕ Q
  embed : Q → Qp
  recover : ∀ qp q, shape qp = .inr q → qp = embed q

namespace Reduction

variable {Qp Q A R R' : Type*}

def oracle (D : Reduction Qp Q A) (o : Q → A) (q : Qp) : A :=
  (D.shape q).elim id o

def prepend (q : Qp) (a : A) (r : R × List (Qp × A)) : R × List (Qp × A) :=
  (r.1, (q, a) :: r.2)

noncomputable def simulate (D : Reduction Qp Q A) :
    DecisionTree Qp A R → DecisionTree Q A (R × List (Qp × A))
  | .leaf r => .leaf (r, [])
  | .query q next =>
    match D.shape q with
    | .inl a => (D.simulate (next a)).map (prepend q a)
    | .inr q' => .query q' (fun a => (D.simulate (next a)).map (prepend q a))

theorem simulate_result (D : Reduction Qp Q A) (t : DecisionTree Qp A R) (o : Q → A) :
    (D.simulate t).output o = (t.output (D.oracle o), t.transcript (D.oracle o)) := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    cases hq : D.shape q with
    | inl a =>
      simp only [simulate, hq, DecisionTree.output_map, DecisionTree.output,
        DecisionTree.transcript, oracle, Sum.elim_inl, id_eq, ih, prepend]
    | inr q' =>
      simp only [simulate, hq, DecisionTree.output_map, DecisionTree.output,
        DecisionTree.transcript, oracle, Sum.elim_inr, ih, prepend]

theorem transcript_map (f : R → R') (t : DecisionTree Q A R) (o : Q → A) :
    (t.map f).transcript o = t.transcript o := by
  induction t with
  | leaf => rfl
  | query q next ih => simp only [DecisionTree.map, DecisionTree.transcript, ih]

theorem simulate_queries (D : Reduction Qp Q A) (t : DecisionTree Qp A R) (o : Q → A) :
    (D.simulate t).queries o ≤ t.queries (D.oracle o) := by
  induction t with
  | leaf => rfl
  | query q next ih =>
    cases hq : D.shape q with
    | inl a =>
      simp only [simulate, hq, DecisionTree.queries_map]
      have hh := ih a
      simpa only [DecisionTree.queries, DecisionTree.transcript, oracle, hq,
        Sum.elim_inl, id_eq, List.length_cons] using hh.trans (Nat.le_succ _)
    | inr q' =>
      simpa only [simulate, hq, DecisionTree.queries_map, DecisionTree.queries,
        DecisionTree.transcript, oracle, Sum.elim_inr, List.length_cons, transcript_map] using
        Nat.add_le_add_right (ih (o q')) 1

theorem bounded_mono (t : DecisionTree Q A R) (n m : ℕ) (hnm : n ≤ m)
    (hn : Screening.DecisionTree.Bounded t n) : Screening.DecisionTree.Bounded t m := by
  induction t generalizing n m with
  | leaf => trivial
  | query q next ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      cases m with
      | zero => omega
      | succ m => exact fun a => ih a n m (by omega) (hn a)

theorem bounded_map (f : R → R') (t : DecisionTree Q A R) (n : ℕ)
    (hn : Screening.DecisionTree.Bounded t n) :
    Screening.DecisionTree.Bounded (t.map f) n := by
  induction t generalizing n with
  | leaf => trivial
  | query q next ih =>
    cases n with
    | zero => contradiction
    | succ n => exact fun a => ih a n (hn a)

theorem simulate_bounded (D : Reduction Qp Q A) (t : DecisionTree Qp A R) (n : ℕ)
    (hn : Screening.DecisionTree.Bounded t n) :
    Screening.DecisionTree.Bounded (D.simulate t) n := by
  induction t generalizing n with
  | leaf => trivial
  | query q next ih =>
    cases n with
    | zero => contradiction
    | succ n =>
      cases hq : D.shape q with
      | inl a =>
        simp only [simulate, hq]
        exact bounded_mono _ n (n + 1) (Nat.le_succ _)
          (bounded_map _ _ n (ih a n (hn a)))
      | inr q' =>
        simp only [simulate, hq]
        exact fun a => bounded_map _ _ n (ih a n (hn a))

variable [Fintype A]

@[simp]
theorem used_map (f : R → R') (t : DecisionTree Q A R) :
    (t.map f).used = t.used := by
  induction t with
  | leaf => rfl
  | query q next ih => simp only [DecisionTree.map, DecisionTree.used, ih]

theorem noRepeats_map (f : R → R') (t : DecisionTree Q A R) (ht : t.NoRepeats) :
    (t.map f).NoRepeats := by
  induction t with
  | leaf => trivial
  | query q next ih =>
    exact ⟨fun a => ih a (ht.1 a), fun a => by simpa only [used_map] using ht.2 a⟩

theorem simulate_used (D : Reduction Qp Q A) (t : DecisionTree Qp A R)
    (q : Q) (hq : q ∈ (D.simulate t).used) : D.embed q ∈ t.used := by
  classical
  induction t with
  | leaf => simpa only [simulate, DecisionTree.used, Finset.notMem_empty] using hq
  | query qp next ih =>
    cases hp : D.shape qp with
    | inl a =>
      simp only [simulate, hp, used_map] at hq
      exact Compiler.Decoder.branch_used_subset qp next a (ih a hq)
    | inr q' =>
      simp only [simulate, hp, DecisionTree.used, used_map, Finset.mem_insert,
        Finset.mem_biUnion, Finset.mem_univ, true_and] at hq
      rcases hq with hq | ⟨a, ha⟩
      · subst q
        rw [← D.recover qp q' hp]
        exact Finset.mem_insert_self _ _
      · exact Compiler.Decoder.branch_used_subset qp next a (ih a ha)

theorem simulate_noRepeats (D : Reduction Qp Q A) (t : DecisionTree Qp A R)
    (ht : t.NoRepeats) : (D.simulate t).NoRepeats := by
  induction t with
  | leaf => trivial
  | query qp next ih =>
    cases hp : D.shape qp with
    | inl a =>
      simp only [simulate, hp]
      exact noRepeats_map _ _ (ih a (ht.1 a))
    | inr q =>
      simp only [simulate, hp]
      refine ⟨fun a => noRepeats_map _ _ (ih a (ht.1 a)), ?_⟩
      intro a ha
      rw [used_map] at ha
      have hh := D.simulate_used (next a) q ha
      rw [← D.recover qp q hp] at hh
      exact ht.2 a hh

noncomputable def simulateOutput (D : Reduction Qp Q A) (t : DecisionTree Qp A R) :
    DecisionTree Q A R :=
  (D.simulate t).map Prod.fst

@[simp]
theorem simulateOutput_result (D : Reduction Qp Q A) (t : DecisionTree Qp A R) (o : Q → A) :
    (D.simulateOutput t).output o = t.output (D.oracle o) := by
  rw [simulateOutput, DecisionTree.output_map, D.simulate_result]

theorem simulateOutput_queries (D : Reduction Qp Q A) (t : DecisionTree Qp A R) (o : Q → A) :
    (D.simulateOutput t).queries o ≤ t.queries (D.oracle o) := by
  rw [simulateOutput, DecisionTree.queries_map]
  exact D.simulate_queries t o

theorem simulateOutput_bounded (D : Reduction Qp Q A) (t : DecisionTree Qp A R)
    (n : ℕ) (hn : Screening.DecisionTree.Bounded t n) :
    Screening.DecisionTree.Bounded (D.simulateOutput t) n :=
  bounded_map _ _ n (D.simulate_bounded t n hn)

theorem simulateOutput_noRepeats (D : Reduction Qp Q A) (t : DecisionTree Qp A R)
    (ht : t.NoRepeats) : (D.simulateOutput t).NoRepeats :=
  noRepeats_map _ _ (D.simulate_noRepeats t ht)

end Reduction

end SteinerLowerBound.MetricComparison.Padding

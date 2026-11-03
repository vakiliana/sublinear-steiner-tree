module

public import SteinerUpperBound.Matching.Padded.Kernel

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

theorem expect_match_bool {C A : Type*} (p q : Program C A) (b : Bool) (f : A → ℝ) :
    (match b with | true => p | false => q).expect f =
      match b with | true => p.expect f | false => q.expect f := by
  cases b <;> rfl

end Program

namespace Sparse

variable {C S : Type*}

def loopC (label : ℕ → C) (r : ℚ) (step : ℕ → S → Program C S) :
    ℕ → ℕ → S → Program C S
  | 0, _, s => .ret s
  | n + 1, start, s =>
    ((IntegerCoin.sample (1 - r)).relabel label).bind fun b =>
      match b with
      | true => (step start s).bind fun s' => loopC label r step n (start + 1) s'
      | false => loopC label r step n (start + 1) s

theorem dense_fusionC (label : ℕ → C) (r : ℚ) (step : ℕ → S → Program C S)
    (n start : ℕ) (s : S) (f : S → ℝ) :
    (dense r n start).expect (fun xs => (Program.forEach step xs s).expect f) =
      (loopC label r step n start s).expect f := by
  induction n generalizing start s f with
  | zero => simp [dense, loopC, Program.forEach]
  | succ n ih =>
    rw [dense, loopC]
    simp only [Program.expect_bind, Program.expect_relabel, Program.expect_ret]
    congr 1
    funext b
    cases b
    · exact ih (start + 1) s f
    · simp only [Program.forEach, Program.expect_bind]
      rw [Program.expect_commute]
      congr 1
      funext s'
      exact ih (start + 1) s' f

end Sparse

namespace Plan

variable {V E : Type*} {G : Graph V E} (S : Slots G) (Q : ℕ) (hQ : 0 < Q)

theorem selected_expect (s : Cache S Q) (v : V) (b i : ℕ)
    (f : Option (Entry S Q) → ℝ) :
    (Cache.selectedStep S Q hQ (Cache.boundary S Q s v) b v i s).expect f =
      match atIndex S Q s v i with
      | none => f none
      | some x => (Range.sample Q hQ (Cache.boundary S Q s v) b).expect
          (fun r => f (some (x.entry r))) := by
  unfold Cache.selectedStep atIndex
  split_ifs with hi
  · simp only [Command.testSlot, Program.bind, Program.expect_tick]
    cases ht : S.test ⟨v, ⟨i, hi⟩⟩ with
    | none => simp [ht]
    | some hit =>
      obtain ⟨e, reverse⟩ := hit
      simp only [ht]
      split_ifs
      · simp only [Program.expect_tick, Program.expect_bind, Command.expect_arithmetic,
          Program.expect_ret, Item.entry]
      · simp
  · simp

theorem collectStep_expect (s : Cache S Q) (v : V) (b i : ℕ)
    (entries : List (Entry S Q)) (f : List (Entry S Q) → ℝ) :
    (Cache.collectStep S Q hQ (Cache.boundary S Q s v) b v s i entries).expect f =
      (Cache.selectedStep S Q hQ (Cache.boundary S Q s v) b v i s).expect
        (fun out => f (Cache.addEntry entries out)) := by
  rw [Cache.collectStep, Program.expect_bind]
  simp only [Program.expect_tick, Program.expect_ret]

theorem factory_expect (s : Cache S Q) (v : V) (b i : ℕ)
    (entries : List (Entry S Q)) (F : List (Entry S Q) → ℝ) :
    (IntegerCoin.sample (Range.probability Q (Cache.boundary S Q s v) b)).expect
      (fun hit => match hit with
        | false => F entries
        | true => (Cache.selectedStep S Q hQ (Cache.boundary S Q s v) b v i s).expect
            (fun out => F (Cache.addEntry entries out))) =
      match atIndex S Q s v i with
      | none => F entries
      | some x => (Observation.sample Q hQ (Cache.boundary S Q s v) b).expect
          (fun obs => F (Cache.addEntry entries (obs.map x.entry))) := by
  simp_rw [selected_expect]
  cases hx : atIndex S Q s v i with
  | none =>
    dsimp only [Cache.addEntry]
    have hc : (fun hit : Bool => match hit with | false => F entries | true => F entries) =
        (fun _ => F entries) := by
      funext hit
      cases hit <;> rfl
    rw [hc]
    exact Program.expect_const _ _
  | some x =>
    dsimp only
    rw [Observation.sample, Program.expect_bind]
    congr 1
    funext hit
    cases hit <;> simp only [Program.expect_bind, Program.expect_ret, Option.map_none,
      Option.map_some, Cache.addEntry]

theorem loopC_tree (s : Cache S Q) (v : V) (b n start : ℕ)
    (entries : List (Entry S Q)) (f : List (Entry S Q) → ℝ) :
    (Sparse.loopC Command.arithmetic
      (1 - Range.probability Q (Cache.boundary S Q s v) b)
      (Cache.collectStep S Q hQ (Cache.boundary S Q s v) b v s) n start entries).expect f =
      (DecisionTree.program
        (fun _ : E => Command.liftArithmetic (S := S)
          (Observation.sample Q hQ (Cache.boundary S Q s v) b))
        (tree ((List.range' start n).filterMap (atIndex S Q s v)) entries)).expect f := by
  induction n generalizing start entries f with
  | zero => simp [Sparse.loopC, tree, DecisionTree.program]
  | succ n ih =>
    have hrr : 1 - (1 - Range.probability Q (Cache.boundary S Q s v) b) =
        Range.probability Q (Cache.boundary S Q s v) b := by ring
    rw [Sparse.loopC, Program.expect_bind, Program.expect_relabel, hrr]
    simp_rw [Program.expect_match_bool, Program.expect_bind, collectStep_expect]
    have hcont (xs : List (Entry S Q)) :=
      ih (start + 1) xs f
    simp_rw [hcont]
    let F : List (Entry S Q) → ℝ := fun xs =>
      (DecisionTree.program
        (fun _ : E => Command.liftArithmetic (S := S)
          (Observation.sample Q hQ (Cache.boundary S Q s v) b))
        (tree ((List.range' (start + 1) n).filterMap (atIndex S Q s v)) xs)).expect f
    trans (match atIndex S Q s v start with
      | none => F entries
      | some x => (Observation.sample Q hQ (Cache.boundary S Q s v) b).expect
          (fun obs => F (Cache.addEntry entries (obs.map x.entry))))
    · calc
        _ = (IntegerCoin.sample (Range.probability Q (Cache.boundary S Q s v) b)).expect
            (fun hit => match hit with
              | false => F entries
              | true => (Cache.selectedStep S Q hQ (Cache.boundary S Q s v) b v start s).expect
                  (fun out => F (Cache.addEntry entries out))) := by
          congr 1
          funext hit
          cases hit <;> rfl
        _ = _ := factory_expect S Q hQ s v b start entries F
    · rw [List.range'_succ]
      simp only [List.filterMap_cons]
      cases hx : atIndex S Q s v start with
      | none => simp only [hx]; rfl
      | some x =>
        simp only [hx, tree, DecisionTree.program, Program.expect_bind, Command.expect_arithmetic]
        congr 1
        funext obs
        cases obs <;> rfl

theorem collect_tree (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) (f : List (Entry S Q) → ℝ) :
    (Cache.collect S Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1)) v s).expect f =
      (DecisionTree.program
        (fun _ : E => Command.liftArithmetic (S := S)
          (Observation.sample Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1))))
        (tree (items S Q s v) [])).expect f := by
  have ha := Buckets.bound_strictMono (show s.level v < s.level v + 1 by omega)
  have hp := Range.probability_bounds Q (Cache.boundary S Q s v)
    (Buckets.bound (s.level v + 1)) ha hb
  have hr0 : 0 ≤ 1 - Range.probability Q (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1)) :=
    sub_nonneg.mpr hp.2
  have hr1 : 1 - Range.probability Q (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1)) ≤ 1 := by
    linarith [hp.1]
  unfold Cache.collect
  simp only [Program.expect_bind, Command.expect_arithmetic]
  rw [Sparse.expect_sample _ hr0 hr1]
  rw [Sparse.dense_fusionC (Command.arithmetic (S := S))]
  have hl := loopC_tree S Q hQ s v (Buckets.bound (s.level v + 1)) (S.length v) 0 [] f
  simpa only [items, List.range_eq_range'] using hl

theorem collect_law [Fintype E] (s : Cache S Q) (v : V)
    (hb : Buckets.bound (s.level v + 1) ≤ Q) (f : List (Entry S Q) → ℝ) :
    (Cache.collect S Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1)) v s).expect f =
      (Law.pi (Kernel.observationLaw S Q hQ s v)).expect
        (fun obs => f (observations (items S Q s v) obs).reverse) := by
  rw [collect_tree S Q hQ s v hb]
  have hd := DecisionTree.deferred_on (Kernel.observationLaw S Q hQ s v)
    (fun _ : E => Command.liftArithmetic (S := S)
      (Observation.sample Q hQ (Cache.boundary S Q s v) (Buckets.bound (s.level v + 1))))
    (tree (items S Q s v) []) (tree_noRepeats _ (keys_nodup S Q s v) [])
    (fun e he f => by
      have he' : e ∈ keys S Q s v :=
        List.mem_toFinset.mpr (tree_used_subset _ _ e he)
      simp only [Kernel.observationLaw, he', ↓reduceIte, Command.expect_arithmetic]
      exact (Observation.expect_law Q hQ _ _ f).symm) f
  simpa only [tree_output, List.append_nil] using hd

end Plan

end SteinerUpperBound.Matching.Padded

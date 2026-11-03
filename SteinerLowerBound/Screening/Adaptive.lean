module

public import SteinerLowerBound.Screening.Probability
public import SteinerLowerBound.QueryModel

@[expose] public section

namespace SteinerLowerBound

open scoped BigOperators Classical

namespace Screening

variable {Ω Q A Z : Type*}

abbrev Record (Q A : Type*) := List (Q × A)

def questions (r : Record Q A) : List Q := r.map Prod.fst

def Compatible (answer : List Q → Q → A) (r : Record Q A) : Prop :=
  ∀ (i : ℕ) (hi : i < r.length), answer (questions (r.take i)) (r[i].1) = r[i].2

@[simp]
theorem compatible_nil (answer : List Q → Q → A) : Compatible answer [] := by
  intro i hi
  simp at hi

theorem compatible_append (answer : List Q → Q → A) (r : Record Q A) (q : Q) (b : A) :
    Compatible answer (r ++ [(q, b)]) ↔
      Compatible answer r ∧ answer (questions r) q = b := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i (by simp; omega)
      simpa only [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using hh
    · have hh := h r.length (by simp)
      simpa [List.take_left, questions] using hh
  · rintro ⟨hr, hq⟩ i hi
    by_cases hir : i < r.length
    · simpa only [List.take_append_of_le_length hir.le, List.getElem_append_left hir] using hr i hir
    · have he : i = r.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simpa [List.take_left, questions] using hq

namespace DecisionTree

noncomputable def accumulate (answer : Ω → List Q → Q → A)
    (cost : Ω → Record Q A → Q → ℝ) (ω : Ω) (r : Record Q A) :
    SteinerLowerBound.DecisionTree Q A Z → ℝ
  | .leaf _ => 0
  | .query q next =>
      cost ω r q +
        accumulate answer cost ω (r ++ [(q, answer ω (questions r) q)])
          (next (answer ω (questions r) q))

noncomputable def run (answer : Ω → List Q → Q → A) (ω : Ω) (r : Record Q A) :
    SteinerLowerBound.DecisionTree Q A Z → Record Q A
  | .leaf _ => r
  | .query q next =>
      run answer ω (r ++ [(q, answer ω (questions r) q)])
        (next (answer ω (questions r) q))

def Bounded : SteinerLowerBound.DecisionTree Q A Z → ℕ → Prop
  | .leaf _, _ => True
  | .query _ _, 0 => False
  | .query _ next, n + 1 => ∀ b, Bounded (next b) n

theorem run_compatible (answer : Ω → List Q → Q → A) (ω : Ω)
    (t : SteinerLowerBound.DecisionTree Q A Z) (r : Record Q A)
    (hr : Compatible (answer ω) r) :
    Compatible (answer ω) (run answer ω r t) := by
  induction t generalizing r with
  | leaf => exact hr
  | query q next ih =>
      exact ih _ _ ((compatible_append _ _ _ _).mpr ⟨hr, rfl⟩)

theorem run_length_le (answer : Ω → List Q → Q → A) (ω : Ω)
    (t : SteinerLowerBound.DecisionTree Q A Z) (n : ℕ) (hn : Bounded t n)
    (r : Record Q A) : (run answer ω r t).length ≤ r.length + n := by
  induction t generalizing n r with
  | leaf => simp [run]
  | query q next ih =>
      cases n with
      | zero => contradiction
      | succ n =>
          have hh := ih (answer ω (questions r) q) n (hn _) (r ++ [(q, answer ω (questions r) q)])
          simpa only [run, List.length_append, List.length_singleton, Nat.add_assoc,
            Nat.add_comm 1] using hh

theorem accumulate_one_le (answer : Ω → List Q → Q → A) (ω : Ω)
    (t : SteinerLowerBound.DecisionTree Q A Z) (n : ℕ) (hn : Bounded t n)
    (r : Record Q A) :
    accumulate answer (fun _ _ _ => 1) ω r t ≤ n := by
  induction t generalizing n r with
  | leaf => simp [accumulate]
  | query q next ih =>
      cases n with
      | zero => contradiction
      | succ n =>
          have hh := ih (answer ω (questions r) q) n (hn _)
            (r ++ [(q, answer ω (questions r) q)])
          simp only [accumulate, Nat.cast_add, Nat.cast_one]
          linarith

variable [Fintype Ω] [Fintype A]

theorem expect_branch (μ : Law Ω) (P : Set Ω) (a : Ω → A) (f : A → Ω → ℝ) :
    μ.expect (fun ω => if ω ∈ P then f (a ω) ω else 0) =
      ∑ b, μ.expect (fun ω => if ω ∈ P ∧ a ω = b then f b ω else 0) := by
  classical
  rw [← Law.expect_sum]
  apply congrArg (Law.expect μ)
  funext ω
  by_cases hp : ω ∈ P <;> simp [hp]

theorem expect_indicator (μ : Law Ω) (P : Set Ω) (a : ℝ) :
    μ.expect (fun ω => if ω ∈ P then a else 0) = a * μ.prob P := by
  classical
  simp only [Law.expect, Law.prob, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : ω ∈ P <;> simp [hp, mul_comm]

theorem charging (μ : Law Ω) (answer : Ω → List Q → Q → A)
    (cost : Ω → Record Q A → Q → ℝ) (quota : Record Q A → Q → ℝ) (B : ℝ)
    (hlocal : ∀ r q,
      μ.expect (fun ω => if Compatible (answer ω) r then cost ω r q else 0) ≤
        B * quota r q * μ.prob {ω | Compatible (answer ω) r})
    (t : SteinerLowerBound.DecisionTree Q A Z) (r : Record Q A) :
    μ.expect (fun ω => if Compatible (answer ω) r then accumulate answer cost ω r t else 0) ≤
      B * μ.expect (fun ω => if Compatible (answer ω) r then
        accumulate answer (fun _ s q => quota s q) ω r t else 0) := by
  classical
  induction t generalizing r with
  | leaf => simp [accumulate, Law.expect_const]
  | query q next ih =>
      have split (f : Ω → Record Q A → Q → ℝ) :
          μ.expect (fun ω => if Compatible (answer ω) r then
            accumulate answer f ω r (.query q next) else 0) =
          μ.expect (fun ω => if Compatible (answer ω) r then f ω r q else 0) +
            ∑ b, μ.expect (fun ω => if Compatible (answer ω) (r ++ [(q, b)]) then
              accumulate answer f ω (r ++ [(q, b)]) (next b) else 0) := by
        have he (ω : Ω) :
            (if Compatible (answer ω) r then
              accumulate answer f ω r (.query q next) else 0) =
            (if Compatible (answer ω) r then f ω r q else 0) +
            (if Compatible (answer ω) r then
              accumulate answer f ω (r ++ [(q, answer ω (questions r) q)])
                (next (answer ω (questions r) q)) else 0) := by
          by_cases hr : Compatible (answer ω) r <;> simp [accumulate, hr]
        simp_rw [he]
        rw [Law.expect_add]
        congr 1
        calc
          _ = ∑ b, μ.expect (fun ω => if Compatible (answer ω) r ∧
              answer ω (questions r) q = b then
                accumulate answer f ω (r ++ [(q, b)]) (next b) else 0) := by
            simpa only [Set.mem_ofPred_eq] using
              expect_branch μ {ω | Compatible (answer ω) r}
                (fun ω => answer ω (questions r) q)
                (fun b ω => accumulate answer f ω (r ++ [(q, b)]) (next b))
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b _
            apply congrArg (Law.expect μ)
            funext ω
            simp only [compatible_append]
      rw [split cost, split (fun _ s q => quota s q), mul_add]
      have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun b _ => ih b (r ++ [(q, b)]))
      rw [← Finset.mul_sum] at hsum
      have hq := hlocal r q
      have he : μ.expect (fun ω => if Compatible (answer ω) r then quota r q else 0) =
          quota r q * μ.prob {ω | Compatible (answer ω) r} := by
        simpa only [Set.mem_ofPred_eq] using
          expect_indicator μ {ω | Compatible (answer ω) r} (quota r q)
      rw [he]
      simpa only [mul_assoc] using add_le_add hq hsum

end DecisionTree

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable local instance : DecidableEq (Terminal S G I) := Classical.decEq _
noncomputable local instance : BEq (Terminal S G I) := instBEqOfDecidableEq

theorem compatible_iff_observations (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset (Terminal S G I)) (r : Record (Query (Terminal S G I) C) Reply) :
    Compatible (queryAnswer π F H) r ↔
      observations π F H (questions r) =
        fun i => (r[i.val]'(by simpa [questions] using i.isLt)).2 := by
  constructor
  · intro hr
    funext i
    have hh := hr i.val (by simpa [questions] using i.isLt)
    change queryAnswer π F H ((questions r).take i.val) ((questions r).get i) = _
    rw [List.get_eq_getElem]
    simpa [questions, List.map_take] using hh
  · intro hr i hi
    have hh := congrFun hr ⟨i, by simpa [questions] using hi⟩
    simpa [observations, questions, List.map_take, List.get_eq_getElem] using hh

end Screening

end SteinerLowerBound

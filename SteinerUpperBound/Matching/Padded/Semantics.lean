module

public import SteinerUpperBound.Matching.Padded.Sparse
public import SteinerLowerBound.LawOperations

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C D A B : Type*}

theorem expect_commute (p : Program C A) (q : Program D B) (f : A → B → ℝ) :
    p.expect (fun a => q.expect (f a)) = q.expect (fun b => p.expect (fun a => f a b)) := by
  unfold expect Law.expect law
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem expect_law_commute {Ω : Type*} [Fintype Ω] (p : Program C A) (μ : Law Ω)
    (f : A → Ω → ℝ) :
    p.expect (fun a => μ.expect (f a)) = μ.expect (fun ω => p.expect (fun a => f a ω)) := by
  unfold expect Law.expect law
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem expect_sum {J : Type*} (p : Program C A) (s : Finset J) (f : J → A → ℝ) :
    p.expect (fun a => ∑ j ∈ s, f j a) = ∑ j ∈ s, p.expect (f j) :=
  FiniteAveraging.expect_sum _ _ _

theorem probability_eq_expect (p : Program C A) (P : A → Prop) :
    p.probability P = p.expect (fun a => if P a then 1 else 0) := by
  simpa only [probability, expect, Set.mem_ofPred_eq] using
    Law.prob_eq_expect p.law {x | P (p.output x)}

theorem mass_pos (p : Program C A) (x : p.Outcomes) : 0 < p.mass x := by
  induction p with
  | ret => exact zero_lt_one
  | tick c p ih => exact ih x
  | draw n hn next ih =>
    exact mul_pos (inv_pos.mpr (by exact_mod_cast hn)) (ih x.1 x.2)

def forEach {S : Type*} (step : A → S → Program C S) :
    List A → S → Program C S
  | [], s => .ret s
  | a :: xs, s => (step a s).bind fun s' => forEach step xs s'

end Program

namespace Sparse

variable {S : Type*}

def loop (r : ℚ) (step : ℕ → S → Program ℕ S) : ℕ → ℕ → S → Program ℕ S
  | 0, _, s => .ret s
  | n + 1, start, s =>
    (IntegerCoin.sample (1 - r)).bind fun b =>
      match b with
      | true => (step start s).bind fun s' => loop r step n (start + 1) s'
      | false => loop r step n (start + 1) s

theorem dense_fusion (r : ℚ) (step : ℕ → S → Program ℕ S) (n start : ℕ)
    (s : S) (f : S → ℝ) :
    ((dense r n start).bind (fun xs => Program.forEach step xs s)).expect f =
      (loop r step n start s).expect f := by
  induction n generalizing start s f with
  | zero => simp [dense, loop, Program.forEach, Program.bind]
  | succ n ih =>
    rw [dense, loop]
    simp only [Program.expect_bind, Program.expect_ret]
    apply congrArg
    funext b
    cases b
    · simpa only [Program.expect_bind] using ih (start + 1) s f
    · simp only [Program.forEach, Program.expect_bind]
      rw [Program.expect_commute]
      apply congrArg
      funext s'
      simpa only [Program.expect_bind] using ih (start + 1) s' f

/-- Sparse selected-index testing has the law of the independent-coin loop. -/
theorem sample_fusion (r : ℚ) (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (step : ℕ → S → Program ℕ S) (n start : ℕ) (s : S) (f : S → ℝ) :
    ((sample r n start).bind (fun xs => Program.forEach step xs s)).expect f =
      (loop r step n start s).expect f := by
  rw [Program.expect_bind, expect_sample r h0 h1]
  simpa only [Program.expect_bind] using dense_fusion r step n start s f

end Sparse

end SteinerUpperBound.Matching.Padded

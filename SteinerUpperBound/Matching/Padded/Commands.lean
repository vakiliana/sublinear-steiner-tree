module

public import SteinerUpperBound.Matching.Padded.Bayes

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open SteinerLowerBound
open scoped Classical BigOperators

namespace Program

variable {C D A : Type*}

def relabel (f : C → D) : Program C A → Program D A
  | .ret a => .ret a
  | .tick c p => .tick (f c) (relabel f p)
  | .draw n hn next => .draw n hn (fun i => relabel f (next i))

theorem expect_relabel (f : C → D) (p : Program C A) (g : A → ℝ) :
    (p.relabel f).expect g = p.expect g := by
  induction p with
  | ret => simp [relabel]
  | tick c p ih => simpa [relabel] using ih
  | draw n hn next ih =>
    simp only [relabel, expect_draw]
    exact Finset.sum_congr rfl fun i _ => by rw [ih i]

theorem expectedCost_relabel (f : C → D) (p : Program C A) (charge : D → ℝ) (r : ℝ) :
    (p.relabel f).expectedCost charge r = p.expectedCost (fun c => charge (f c)) r := by
  induction p with
  | ret => simp [relabel]
  | tick c p ih => simp only [relabel, expectedCost_tick, ih]
  | draw n hn next ih =>
    simp only [relabel, expectedCost_draw]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [ih i]

theorem expectedCost_scale (p : Program C A) (charge : C → ℝ) (r t : ℝ) :
    p.expectedCost (fun c => t * charge c) (t * r) = t * p.expectedCost charge r := by
  induction p with
  | ret => simp
  | tick c p ih => simp only [expectedCost_tick, ih]; ring
  | draw n hn next ih =>
    simp only [expectedCost_draw, ih]
    rw [mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem expectedCost_mono (p : Program C A) (c d : C → ℝ) (r s : ℝ)
    (hcd : ∀ a, c a ≤ d a) (hrs : r ≤ s) :
    p.expectedCost c r ≤ p.expectedCost d s := by
  apply Law.expect_mono
  intro x
  induction p with
  | ret => exact le_refl _
  | tick a p ih => exact add_le_add (hcd a) (ih x)
  | draw n hn next ih => exact add_le_add hrs (ih x.1 x.2)

theorem cost_add (p : Program C A) (c d : C → ℝ) (r s : ℝ) (x : p.Outcomes) :
    p.cost (fun a => c a + d a) (r + s) x = p.cost c r x + p.cost d s x := by
  induction p with
  | ret => simp [cost]
  | tick a p ih => simp only [cost, ih x]; ring
  | draw n hn next ih =>
    obtain ⟨i, x⟩ := x
    simp only [cost, ih i x]
    ring

end Program

variable {V E : Type*} {G : Graph V E}

inductive Command (S : Slots G) where
  | arithmetic : ℕ → Command S
  | oracle : ℕ → Command S
  | test : Slot S.length → Command S
  | prepare : V → Command S

namespace Command

variable {S : Slots G}

def charge (A : Account S) : Command S → ℝ
  | .arithmetic n => A.rate * n
  | .oracle n => A.rate * n
  | .test s => A.slot s
  | .prepare v => A.preparation v

theorem charge_nonneg (A : Account S) (c : Command S) : 0 ≤ charge A c := by
  cases c with
  | arithmetic n => exact mul_nonneg A.rate_nonneg (Nat.cast_nonneg _)
  | oracle n => exact mul_nonneg A.rate_nonneg (Nat.cast_nonneg _)
  | test s => exact A.slot_nonneg s
  | prepare v => exact A.preparation_nonneg v

/-- The two arithmetic tags have identical runtime charges. -/
def bucketCharge (A : Account S) : Command S → ℝ
  | .oracle _ => 0
  | c => charge A c

def oracleCharge (A : Account S) : Command S → ℝ
  | .oracle n => A.rate * n
  | _ => 0

theorem bucketCharge_nonneg (A : Account S) (c : Command S) : 0 ≤ bucketCharge A c := by
  cases c <;> simp only [bucketCharge]
  · exact charge_nonneg A _
  · exact le_refl _
  · exact charge_nonneg A _
  · exact charge_nonneg A _

theorem oracleCharge_nonneg (A : Account S) (c : Command S) : 0 ≤ oracleCharge A c := by
  cases c <;> simp only [oracleCharge, le_refl]
  exact mul_nonneg A.rate_nonneg (Nat.cast_nonneg _)

theorem split_cost {A : Type*} (p : Program (Command S) A) (account : Account S) (x : p.Outcomes) :
    p.cost (charge account) account.rate x =
      p.cost (bucketCharge account) account.rate x + p.cost (oracleCharge account) 0 x := by
  have hc : charge account = fun c => bucketCharge account c + oracleCharge account c := by
    funext c
    cases c <;> simp [charge, bucketCharge, oracleCharge]
  rw [hc]
  simpa only [add_zero] using Program.cost_add p (bucketCharge account) (oracleCharge account) account.rate 0 x

def liftArithmetic {A : Type*} (p : Program ℕ A) : Program (Command S) A :=
  p.relabel Command.arithmetic

theorem expect_arithmetic {A : Type*} (p : Program ℕ A) (f : A → ℝ) :
    (liftArithmetic (S := S) p).expect f = p.expect f := Program.expect_relabel _ _ _

theorem cost_arithmetic {A : Type*} (p : Program ℕ A) (Acount : Account S) :
    (liftArithmetic p).expectedCost (charge Acount) Acount.rate =
      Acount.rate * p.expectedCost (fun n => (n : ℝ)) 1 := by
  rw [liftArithmetic, Program.expectedCost_relabel]
  simpa only [charge, mul_one] using
    Program.expectedCost_scale p (fun n => (n : ℝ)) 1 Acount.rate

def testSlot (S : Slots G) (s : Slot S.length) :
    Program (Command S) (Option (E × Slot S.length)) :=
  .tick (.test s) (.ret (S.test s))

end Command

end SteinerUpperBound.Matching.Padded

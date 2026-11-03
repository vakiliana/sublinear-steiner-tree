module

public import SteinerUpperBound.BandEstimator.Tuning
public import SteinerUpperBound.BandEvaluation
public import SteinerUpperBound.QueryProgram

@[expose] public section

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical BigOperators

abbrev Index (g : Grid) := Fin (g.intervals + 1)

variable {M Q : Type*} {n k : ℕ}

noncomputable def scaleProgram (g : Grid) : ℕ → Code M Q ℝ
  | 0 => .tick 2 (.pure g.first)
  | i + 1 => (scaleProgram g i).bind (fun a => .tick 1 (.pure (a * g.q)))

noncomputable def scaleResult (g : Grid) (i : ℕ) : Outcome ℝ :=
  ⟨g.scale i, 2 * i + 3, 0, 0, 0⟩

theorem scale_evaluates (m : M → ℝ) (b : Q → Bool) (g : Grid) (i : ℕ) :
    Code.Evaluates m b (scaleProgram g i) (scaleResult g i) := by
  induction i with
  | zero =>
    intro F
    simp [scaleProgram, scaleResult, Code.evaluate, Outcome.add, Outcome.pure]
  | succ i ih =>
    intro F
    rw [scaleProgram, Code.evaluate_bind, ih]
    simp only [Code.evaluate, scaleResult, Outcome.add, Outcome.combine,
      Outcome.pure, Grid.scale_succ, Nat.add_zero, mul_comm (g.scale i) g.q]
    congr 2

theorem scale_noRandom (g : Grid) (i : ℕ) :
    BandEvaluation.NoRandom (scaleProgram (M := M) (Q := Q) g i) := by
  induction i with
  | zero => trivial
  | succ i ih => exact BandEvaluation.noRandom_bind _ _ ih (fun _ => trivial)

theorem scale_runs (m : M → ℝ) (b : Q → Bool) (g : Grid) (i : ℕ) (o : Outcome ℝ)
    (ho : Runs m b (scaleProgram g i) o) : o = scaleResult g i :=
  BandEvaluation.runs_eq_of_evaluates m b _ (scale_noRandom g i) _
    (scale_evaluates m b g i) o ho

noncomputable def meanProgram (label : Fin (k + 1) → Fin n) (key : Fin n → Q)
    (root : Fin (k + 1)) (terminals : List (Fin n)) (d : Data) (a : ℝ) (c : Cache Q) :
    Code (Sym2 (Fin n)) Q (Covers.OracleProgram.Mean.Result Q k d.samples) :=
  BandEvaluation.samplingProgram label key root d.rowCap d.samples d.totalCap c
    (accuracy d) a d.cutoff terminals (EstimatorParameters.deltaCoarse * a) EstimatorParameters.tau

noncomputable def finish (d : Data) (a : ℝ)
    (r : Covers.OracleProgram.Mean.Result Q k d.samples) : Option ℝ × Cache Q :=
  (r.value.map (fun empirical => BandEvaluation.estimate a r.lower empirical (accuracy d)), r.cache)

noncomputable def stage (g : Grid) (label : Fin (k + 1) → Fin n)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (d : Data) (i : Index g) (c : Cache Q) : Code (Sym2 (Fin n)) Q (Option ℝ × Cache Q) :=
  .tick 15 ((scaleProgram g i.val).bind (fun a =>
    (meanProgram label (key i) root terminals d a c).bind (fun r =>
      .tick 11 (.pure (finish d a r)))))

noncomputable def add (x y : Option ℝ) : Option ℝ :=
  x.bind (fun a => y.map (fun b => a + b))

noncomputable def rounds (g : Grid) (label : Fin (k + 1) → Fin n)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n)) (d : Data) :
    List (Index g) → Option ℝ → Cache Q → Code (Sym2 (Fin n)) Q (Option ℝ × Cache Q)
  | [], total, c => .tick 0 (.pure (total, c))
  | i :: l, total, c =>
      (stage g label key root terminals d i c).bind (fun r =>
        .tick 3 (rounds g label key root terminals d l (add total r.1) r.2))

/-- All coarse levels, including the last endpoint, are processed. -/
noncomputable def program (g : Grid) (label : Fin (k + 1) → Fin n)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (d : Data) (c : Cache Q) : Code (Sym2 (Fin n)) Q (Option ℝ × Cache Q) :=
  .tick (4 * (g.intervals + 1) + 3)
    (rounds g label key root terminals d (List.finRange (g.intervals + 1)) (some 0) c)

noncomputable def fromParameters (g : Grid) (label : Fin (k + 1) → Fin n)
    (key : Index g → Fin n → Q) (root : Fin (k + 1)) (terminals : List (Fin n))
    (p : EstimatorParameters.PublicParameters) (c : Cache Q) :
    Code (Sym2 (Fin n)) Q (Option ℝ × Cache Q) :=
  .tick 15 (program g label key root terminals (ofParameters p (k + 1)) c)

theorem band_parameters (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ EstimatorParameters.deltaCoarse * a ∧ 0 ≤ EstimatorParameters.tau ∧
      EstimatorParameters.tau * a ≤ a - 2 * (EstimatorParameters.deltaCoarse * a) := by
  have hd : 0 ≤ EstimatorParameters.deltaCoarse := (EstimatorParameters.metric_scale_constants).1.le
  have ht : 0 ≤ EstimatorParameters.tau := (EstimatorParameters.metric_scale_constants).2.2.2.2.1.le
  have h : EstimatorParameters.tau + 2 * EstimatorParameters.deltaCoarse ≤ 1 := by
    norm_num [EstimatorParameters.tau, EstimatorParameters.tauQ,
      EstimatorParameters.deltaCoarse, EstimatorParameters.deltaCoarseQ]
  exact ⟨mul_nonneg hd ha, ht, by nlinarith [mul_le_mul_of_nonneg_right h ha]⟩

noncomputable def retained (b : Q → Bool) (g : Grid) (key : Index g → Fin n → Q)
    (terminals : List (Fin n)) (i : Index g) : Finset (Fin n) :=
  BandEvaluation.retainedSet b (key i) terminals

noncomputable def target (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data) (i : Index g) : ℝ :=
  BandEvaluation.smallBandSum I (retained b g key terminals i) (g.scale i.val)
    (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau d.cutoff

noncomputable def totalSmallScore (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data) : ℝ :=
  ∑ i, target I b g key terminals d i

noncomputable def mass (b : Q → Bool) (g : Grid) (key : Index g → Fin n → Q)
    (terminals : List (Fin n)) : ℝ :=
  ∑ i, g.scale i.val * (retained b g key terminals i).card

def GoodStage (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (key : Index g → Fin n → Q) (terminals : List (Fin n)) (d : Data) (i : Index g)
    (r : Option ℝ × Cache Q) : Prop :=
  Cache.Correct b r.2 ∧ ∃ t, r.1 = some t ∧ 0 ≤ t ∧
    t ≤ target I b g key terminals d i ∧
    target I b g key terminals d i - t ≤
      9 * accuracy d * g.scale i.val * (retained b g key terminals i).card

end SteinerUpperBound.BandEstimator

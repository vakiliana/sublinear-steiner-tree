module

public import SteinerUpperBound.BandEstimator.Stage

@[expose] public section

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

namespace SteinerUpperBound.BandEstimator

open SteinerLowerBound QueryProgram MSTApproximation Covers.OracleProgram
open scoped Classical

variable {Q : Type*} {n k : ℕ}

def meanWork (n length : ℕ) (d : Data) : ℕ :=
  64 * (d.totalCap + d.samples + 1) +
    40000000000 * (n + length + 1) * (d.cutoff + 2) ^ 12 * d.samples

def stageWork (g : Grid) (n length : ℕ) (d : Data) : ℕ :=
  meanWork n length d + 2 * (g.intervals + 1) + 31

def stagePositive (d : Data) : ℕ := (d.cutoff + 2) * d.samples

def programWork (g : Grid) (n length : ℕ) (d : Data) : ℕ :=
  (stageWork g n length d + 8) * (g.intervals + 1) + 5

def programPositive (g : Grid) (d : Data) : ℕ :=
  stagePositive d * (g.intervals + 1)

theorem stage_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (i : Index g) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b (stage g label key root terminals d i c) o →
      Cache.Correct b o.value.2 ∧ o.work ≤ stageWork g n terminals.length d ∧
        o.positiveReplies ≤ stagePositive d := by
  intro o ho
  have hcache := stage_cache_correct I b g label key root terminals hlabels d i c hc o ho
  obtain ⟨r, hr, rfl⟩ := stage_runs I.weight b g label key root terminals d i c o ho
  obtain ⟨seed, he⟩ := Mean.runs_compiled_seed I.weight b
    (meanProgram label (key i) root terminals d (g.scale i.val) c) r hr
  have hb := BandEvaluation.sampling_compiled_resources I b label (key i) root terminals hlabels
    (g.scale i.val) (EstimatorParameters.deltaCoarse * g.scale i.val) EstimatorParameters.tau d.cutoff
    (band_parameters _ (g.scale_pos _).le).2.2 d.rowCap d.samples d.totalCap c hc (accuracy d) seed
  change (((meanProgram label (key i) root terminals d (g.scale i.val) c).compile
    I.weight).tree seed).output b = r at he
  change (let o := (((meanProgram label (key i) root terminals d (g.scale i.val) c).compile
    I.weight).tree seed).output b
    o.work ≤ meanWork n terminals.length d ∧ o.positiveReplies ≤ stagePositive d) at hb
  dsimp only at hb
  rw [he] at hb
  refine ⟨hcache, ?_, hb.2⟩
  have hi : i.val ≤ g.intervals + 1 := Nat.le_of_lt i.isLt
  dsimp only [stageOutcome, stageWork]
  omega

theorem rounds_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals) (d : Data)
    (indices : List (Index g)) (total : Option ℝ) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b (rounds g label key root terminals d indices total c) o →
      Cache.Correct b o.value.2 ∧
        o.work ≤ (stageWork g n terminals.length d + 4) * indices.length + 1 ∧
        o.positiveReplies ≤ stagePositive d * indices.length := by
  induction indices generalizing total c with
  | nil =>
    intro o ho
    rw [rounds] at ho
    cases ho with
    | tick ho =>
      cases ho
      exact ⟨hc, by simp [Outcome.add, Outcome.pure], by simp [Outcome.add, Outcome.pure]⟩
  | cons i l ih =>
    intro o ho
    rw [rounds] at ho
    obtain ⟨r, z, hr, hz, rfl⟩ := Mean.runs_bind_inv I.weight b
      (stage g label key root terminals d i c) _ _ ho
    have hs := stage_resources I b g label key root terminals hlabels d i c hc r hr
    cases hz with
    | tick hz =>
      have ht := ih (add total r.value.1) r.value.2 hs.1 _ hz
      refine ⟨ht.1, ?_, ?_⟩ <;>
        simp only [Outcome.combine, Outcome.add, List.length_cons, Nat.mul_succ] <;> omega

theorem program_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (c : Cache Q) (hc : Cache.Correct b c) :
    ∀ o, Runs I.weight b (program g label key root terminals d c) o →
      Cache.Correct b o.value.2 ∧ o.work ≤ programWork g n terminals.length d ∧
        o.positiveReplies ≤ programPositive g d := by
  intro o ho
  rw [program] at ho
  cases ho with
  | tick ho =>
    have ht := rounds_resources I b g label key root terminals hlabels d
      (List.finRange (g.intervals + 1)) (some 0) c hc _ ho
    simp only [List.length_finRange] at ht
    refine ⟨ht.1, ?_, ?_⟩
    · dsimp only [programWork, Outcome.add]
      nlinarith [ht.2.1]
    · simpa only [Outcome.add, Nat.zero_add, programPositive] using ht.2.2

theorem program_compiled_resources (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (c : Cache Q) (hc : Cache.Correct b c)
    (seed : ((program g label key root terminals d c).compile I.weight).Seed) :
    let o := (((program g label key root terminals d c).compile I.weight).tree seed).output b
    Cache.Correct b o.value.2 ∧ o.work ≤ programWork g n terminals.length d ∧
      o.positiveReplies ≤ programPositive g d :=
  program_resources I b g label key root terminals hlabels d c hc _
    (runs_compile I.weight b _ seed)

theorem stage_expected (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (i : Index g) (c : Cache Q) (hc : Cache.Correct b c) :
    (stage g label key root terminals d i c).evaluate I.weight b (fun o => (o.work : ℝ)) ≤
        stageWork g n terminals.length d ∧
      (stage g label key root terminals d i c).evaluate I.weight b (fun o => (o.positiveReplies : ℝ)) ≤
        stagePositive d := by
  constructor
  · apply le_trans _ (Code.evaluate_const I.weight b (stage g label key root terminals d i c)
      ((stageWork g n terminals.length d : ℕ) : ℝ)).le
    apply Mean.evaluate_mono_runs
    intro o ho
    exact_mod_cast (stage_resources I b g label key root terminals hlabels d i c hc o ho).2.1
  · apply le_trans _ (Code.evaluate_const I.weight b (stage g label key root terminals d i c)
      ((stagePositive d : ℕ) : ℝ)).le
    apply Mean.evaluate_mono_runs
    intro o ho
    exact_mod_cast (stage_resources I b g label key root terminals hlabels d i c hc o ho).2.2

theorem program_expected (I : Instance (Fin n)) (b : Q → Bool) (g : Grid)
    (label : Fin (k + 1) → Fin n) (key : Index g → Fin n → Q) (root : Fin (k + 1))
    (terminals : List (Fin n)) (hlabels : ∀ u, label u ∈ terminals)
    (d : Data) (c : Cache Q) (hc : Cache.Correct b c) :
    (program g label key root terminals d c).evaluate I.weight b (fun o => (o.work : ℝ)) ≤
        programWork g n terminals.length d ∧
      (program g label key root terminals d c).evaluate I.weight b (fun o => (o.positiveReplies : ℝ)) ≤
        programPositive g d := by
  constructor
  · apply le_trans _ (Code.evaluate_const I.weight b (program g label key root terminals d c)
      ((programWork g n terminals.length d : ℕ) : ℝ)).le
    apply Mean.evaluate_mono_runs
    intro o ho
    exact_mod_cast (program_resources I b g label key root terminals hlabels d c hc o ho).2.1
  · apply le_trans _ (Code.evaluate_const I.weight b (program g label key root terminals d c)
      ((programPositive g d : ℕ) : ℝ)).le
    apply Mean.evaluate_mono_runs
    intro o ho
    exact_mod_cast (program_resources I b g label key root terminals hlabels d c hc o ho).2.2

end SteinerUpperBound.BandEstimator

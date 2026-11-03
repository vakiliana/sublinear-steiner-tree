module

public import SteinerUpperBound.SavingEstimator.Resources.Geometry
public import SteinerUpperBound.LargeCoverProgram.SmallResources

@[expose] public section

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram EstimatorParameters
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical

def workUnit : CounterKind → ℕ
  | .ordinary => 1
  | .positive => 0

theorem workUnit_eq (kind : CounterKind) : (workUnit kind : ℝ) = kind.counter.work := by
  cases kind <;> norm_num [workUnit, CounterKind.counter, workCounter, positiveCounter]

def largestSize (n : ℕ) : ℕ := publicSize n n (4 * n + 2) (B n)
def largestLog (n : ℕ) : ℕ := Nat.log 2 (largestSize n) + 1
def lazyFactor (n : ℕ) : ℕ := 2 ^ 128 * largestLog n ^ 9

def geometricPublic (kind : CounterKind) (n : ℕ) : ℕ :=
  match kind with
  | .ordinary => 2400000 * (n + 1) * t n * (B n + 2) ^ 4
  | .positive => 400 * t n * (B n + 2) ^ 3

def pointPublic (kind : CounterKind) (n : ℕ) : ℕ :=
  match kind with
  | .ordinary => 4200 * (n + 1) * (B n + 2) ^ 2
  | .positive => B n + 1

def meanBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  let p := closed n (k + 1)
  match kind with
  | .ordinary => 64 * (p.meanProposals + p.meanSamples + 1)
  | .positive => p.meanSamples

def coveredBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  32 * workUnit kind + meanBase kind n k +
    (closed n (k + 1)).meanSamples *
      (pointPublic kind n + lazyFactor n * geometricPublic kind n + 12 * workUnit kind)

def deletionBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  match kind with
  | .ordinary => LargeCoverProgram.deletionWork n (closed n (k + 1))
  | .positive => (closed n (k + 1)).poolSamples

def largeBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  deletionBase kind n k + 4 * workUnit kind + coveredBase kind n k

def smallBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  match kind with
  | .ordinary => LargeCoverProgram.smallWork n k (closed n (k + 1))
  | .positive => LargeCoverProgram.smallLimit (closed n (k + 1))

def frontendBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  let p := closed n (k + 1)
  samplerBudget kind p.calibrationProposals p.calibrationSamples +
    32 * workUnit kind + smallBase kind n k + largeBase kind n k

def rawBase (kind : CounterKind) (n k : ℕ) : ℕ :=
  (configurationWork n (k + 1) (parameters n (k + 1)) + 12) * workUnit kind +
    frontendBase kind n k

theorem rowCapacity_le_max (n count : ℕ) (gm : ℚ) :
    LargeCoverProgram.rowCapacity n (closed n count) gm ≤ 4 * n + 2 := by
  unfold LargeCoverProgram.rowCapacity
  have hm := min_le_left (4 * n / max 1 (closed n count).t + 2)
    (max 1 ⌈100 * (n : ℚ) / ((closed n count).eps * gm)⌉₊)
  have hd := Nat.div_le_self (4 * n) (max 1 (closed n count).t)
  omega

theorem rankSize_le (n count : ℕ) (b : ℕ) (hk : count ≤ n) (hb : b ≤ 4 * n + 2) :
    publicSize n count b (B n) ≤ largestSize n := by
  dsimp only [largestSize, publicSize]
  gcongr

theorem truncatedFactor_le (n count b : ℕ) (hk : count ≤ n) (hb : b ≤ 4 * n + 2) :
    truncatedFactor n count b (B n) ≤ (lazyFactor n : ℝ) := by
  have hl := Nat.add_le_add_right
    (Nat.log_mono_right (b := 2) (rankSize_le n count b hk hb)) 1
  have hh := Nat.mul_le_mul_left (2 ^ 128) (Nat.pow_le_pow_left hl 9)
  simpa only [truncatedFactor, lazyFactor, largestLog, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one] using (show
      ((2 ^ 128 * (Nat.log 2 (publicSize n count b (B n)) + 1) ^ 9 : ℕ) : ℝ) ≤
        (lazyFactor n : ℝ) by exact_mod_cast hh)

theorem geometricBudget_le (kind : CounterKind) (n : ℕ) :
    geometricBudget kind n (B n) (t n) ≤ (geometricPublic kind n : ℝ) := by
  have ht : (0 : ℝ) < t n := by exact_mod_cast t_pos n
  have ht1 : (1 : ℝ) ≤ t n := by exact_mod_cast t_pos n
  have hn : (n : ℝ) ≤ (t n : ℝ) * t n := by
    have hh : (n : ℝ) ≤ (t n : ℝ) ^ 2 := by exact_mod_cast (n_lt_t_sq n).le
    simpa only [pow_two] using hh
  have hd : (n : ℝ) / t n ≤ t n := (div_le_iff₀ ht).mpr hn
  have hh : (1 : ℝ) + n / t n ≤ 2 * t n := by linarith
  cases kind
  · calc
      geometricBudget .ordinary n (B n) (t n) ≤
          1200000 * (n + 1 : ℝ) * (2 * t n) * (B n + 2 : ℝ) ^ 4 := by
        dsimp only [geometricBudget]
        gcongr
      _ = _ := by dsimp only [geometricPublic]; push_cast; ring
  · calc
      geometricBudget .positive n (B n) (t n) ≤ 200 * (2 * t n : ℝ) * (B n + 2 : ℝ) ^ 3 := by
        dsimp only [geometricBudget]
        gcongr
      _ = _ := by dsimp only [geometricPublic]; push_cast; ring

theorem pointBase_le (kind : CounterKind) (n count b : ℕ)
    (hk : count ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) :
    pointBase kind n count b (B n) ≤ pointPublic kind n := by
  cases kind
  · have hp : LargeCoverProgram.pointBudget n count b (B n) ≤ 2 * workCap n count b (B n) := by
      unfold LargeCoverProgram.pointBudget workCap preparationBudget
      omega
    have hw := Nat.mul_le_mul_left 2 (workCap_le n count b (B n) hk hb)
    dsimp only [pointBase, pointPublic]
    nlinarith
  · exact le_refl _

theorem smallLimit_eq (n count : ℕ) :
    LargeCoverProgram.smallLimit (closed n count) = 10 * B n * t n := by
  change ⌈100 * (t n : ℚ) / epsQ n⌉₊ = _
  have he : 100 * (t n : ℚ) / epsQ n = ((10 * B n * t n : ℕ) : ℚ) := by
    unfold epsQ B
    push_cast
    simp only [div_eq_mul_inv, one_mul, inv_inv]
    ring
  rw [he, Nat.ceil_natCast]

theorem meanBase_le (kind : CounterKind) (n k : ℕ) :
    (samplerBudget kind (closed n (k + 1)).meanProposals (closed n (k + 1)).meanSamples : ℝ) +
      (6 * (closed n (k + 1)).meanSamples + 42 : ℕ) * kind.counter.work ≤
        (meanBase kind n k : ℝ) := by
  cases kind <;> dsimp only [samplerBudget, meanBase, CounterKind.counter, workCounter, positiveCounter]
  all_goals push_cast; nlinarith

theorem accessBudget_le (kind : CounterKind) (n count b : ℕ)
    (hk : count ≤ n) (hb : b ≤ 4 * n + 2) (hb1 : 1 ≤ b) (T : ℝ) (hT : 0 ≤ T) :
    accessBudget kind n count b (B n) (t n) T ≤
      (lazyFactor n : ℝ) * geometricPublic kind n + 12 * kind.counter.work +
        2 * T / (publicSize n count 1 (B n) : ℝ) ^ 3 := by
  have hsize : publicSize n count 1 (B n) ≤ publicSize n count b (B n) := by
    unfold publicSize
    gcongr
  have hlow : (0 : ℝ) < publicSize n count 1 (B n) := by unfold publicSize; positivity
  have hpow : (publicSize n count 1 (B n) : ℝ) ^ 3 ≤ (publicSize n count b (B n) : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsize) 3
  have he := div_le_div_of_nonneg_left (show 0 ≤ 2 * T by positivity) (pow_pos hlow 3) hpow
  have hg := mul_le_mul (truncatedFactor_le n count b hk hb) (geometricBudget_le kind n)
    (geometricBudget_nonneg kind n (B n) (t n) (by exact_mod_cast t_pos n)) (by positivity)
  exact add_le_add (add_le_add hg (le_refl _)) he

end SteinerUpperBound.SavingEstimator.Resources

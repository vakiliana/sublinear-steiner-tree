module

public import SteinerUpperBound.SavingEstimator.Resources.Program
public import SteinerUpperBound.SavingEstimator.Resources.Polynomial.Assembly

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram EstimatorParameters
open PortGraph.RuntimeAdapter.Averaged
open scoped Classical

variable {n k : ℕ} {Q : Type}

theorem raw_counter_bad (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup)
    (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty) :
    (SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache).evaluate I.weight bits
      (fun o => if ¬ kind.counter.value o ≤ (executionBudget kind n : ℝ) then 1 else 0) ≤ 5 * beta n := by
  let raw := SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache
  let T : ℝ := executionBudget kind n
  have hpos : 0 < T := by dsimp only [T]; exact_mod_cast executionBudget_pos kind n
  have hD : (0 : ℝ) < betaDenom n := by exact_mod_cast betaDenom_pos n
  have hbase : (rawBase kind n k : ℝ) / T ≤ beta n := by
    rw [beta_eq]
    apply (div_le_div_iff₀ hpos hD).mpr
    simp only [one_mul]
    dsimp only [T]
    exact_mod_cast (show rawBase kind n k * betaDenom n ≤ executionBudget kind n by
      simpa only [Nat.mul_comm] using budgeted_rawBase kind n k (terminal_count_le terminals hnd))
  have hm := raw_clipped kind I bits terminals root key a hT hnd cache hc hb T hpos.le
  have ht := counter_bad_le_clipped I.weight bits raw kind.counter T hpos
  calc
    _ ≤ raw.evaluate I.weight bits (clipped kind.counter T) / T := ht
    _ ≤ ((rawBase kind n k : ℝ) + 4 * beta n * T) / T :=
      div_le_div_of_nonneg_right hm hpos.le
    _ = (rawBase kind n k : ℝ) / T + 4 * beta n := by field_simp <;> ring
    _ ≤ beta n + 4 * beta n := add_le_add hbase (le_refl _)
    _ = _ := by ring

theorem performance : Performance resourceConstant 64 := by
  refine ⟨resourceConstant_pos, ?_⟩
  intro Q n k I bits terminals root key a hT hnd cache hc hroot
  let raw := SavingEstimator.fromParameters terminals root key a (parameters n (k + 1)) cache
  have hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty := by
    refine ⟨root, ?_⟩
    simp only [Covers.Rejection.retained, CategoricalCoupling.selected, Finset.mem_filter,
      Finset.mem_univ, true_and, hroot]
  refine ⟨originalGood I.weight bits raw (workBudget resourceConstant 64 n) (positiveBudget resourceConstant 64 n),
    ?_, ?_, ?_⟩
  · have hh := originalGood_failure I.weight bits raw
      (workBudget resourceConstant 64 n) (positiveBudget resourceConstant 64 n)
      (5 * beta n) (5 * beta n)
      (raw_counter_bad .ordinary I bits terminals root key a hT hnd cache hc hb)
      (raw_counter_bad .positive I bits terminals root key a hT hnd cache hc hb)
    convert hh using 1 <;> ring
  · have hh := (originalGood_costs I.weight bits raw
      (workBudget resourceConstant 64 n) (positiveBudget resourceConstant 64 n)).1
    convert hh using 1
    apply congrArg (raw.compile I.weight).law.expect
    funext seed
    by_cases h : originalGood I.weight bits raw (workBudget resourceConstant 64 n)
        (positiveBudget resourceConstant 64 n) seed
    all_goals simp only [h, ↓reduceIte, Causal.counterSeed, ordinary_value, raw]
  · have hh := (originalGood_costs I.weight bits raw
      (workBudget resourceConstant 64 n) (positiveBudget resourceConstant 64 n)).2
    convert hh using 1
    apply congrArg (raw.compile I.weight).law.expect
    funext seed
    by_cases h : originalGood I.weight bits raw (workBudget resourceConstant 64 n)
        (positiveBudget resourceConstant 64 n) seed
    all_goals simp only [h, ↓reduceIte, Causal.counterSeed, positive_value, raw]

theorem exists_performance : ∃ K d : ℕ, Performance K d :=
  ⟨resourceConstant, 64, performance⟩

end SteinerUpperBound.SavingEstimator.Resources

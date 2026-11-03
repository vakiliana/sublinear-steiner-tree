module

public import SteinerUpperBound.SavingEstimator.Resources.Envelope
public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

@[expose] public section

set_option maxHeartbeats 1800000

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical BigOperators

variable {n k b B : ℕ} {Q : Type}

theorem ordinary_value {R : Type*} :
    (CounterKind.ordinary.counter.value : Outcome R → ℝ) = fun o => (o.work : ℝ) := by
  funext o
  exact workCounter_value o

theorem positive_value {R : Type*} :
    (CounterKind.positive.counter.value : Outcome R → ℝ) = fun o => (o.positiveReplies : ℝ) := by
  funext o
  exact positiveCounter_value o

theorem clipped_ordinary {R : Type*} (T : ℝ) :
    (clipped CounterKind.ordinary.counter T : Outcome R → ℝ) = fun o => min (o.work : ℝ) T := by
  funext o
  dsimp only [clipped]
  rw [ordinary_value]

theorem clipped_positive {R : Type*} (T : ℝ) :
    (clipped CounterKind.positive.counter T : Outcome R → ℝ) = fun o => min (o.positiveReplies : ℝ) T := by
  funext o
  dsimp only [clipped]
  rw [positive_value]

/-- Only genuine calibration, incidence and residual-neighborhood facts.
There is deliberately no oracle value, call, or cost premise. -/
structure AccessFacts (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (t epsilon xi gm : ℝ) : Prop where
  terminals : cfg.terminals.toList.toFinset = I.terminals
  nodup : cfg.terminals.toList.Nodup
  t_pos : 0 < t
  epsilon_pos : 0 < epsilon
  epsilon_le : epsilon ≤ 1
  xi_le : xi ≤ 1 / 2
  retained_pos : 0 < (PortGraph.retained I bits cfg).card
  calibrated : (1 - xi) * (PortGraph.retained I bits cfg).card ≤ gm
  incidence : (b : ℝ) ≤ 100 * n / (epsilon * gm) + 1
  cutoff : 10 / epsilon ≤ (B : ℝ)
  count : k ≤ n
  square : b ^ 2 ≤ 50 * (n + 1)
  clamp : (b : ℝ) ≤ 4 * n / t + 1
  residual : ∀ v, ((PortGraph.residualNeighbors I bits cfg v).card : ℝ) ≤
    4 * (PortGraph.retained I bits cfg).card / t

noncomputable def oracleClip (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (T : ℝ)
    (C : PortGraph.Vertex I bits cfg B) (cache : Cache Q) : ℝ :=
  (oracle cfg (publicSize n k b B) (PortGraph.canonicalFrame I cfg b B C.val) cache).evaluate
    I.weight bits (clipped kind.counter T)

noncomputable def oracleEnvelope (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (T : ℝ) (C : PortGraph.Vertex I bits cfg B) : ℝ :=
  envelope (Cache.Correct bits) (oracleClip (b := b) kind I bits cfg T) C

noncomputable def accessBudget (kind : CounterKind) (n k b B : ℕ) (t T : ℝ) : ℝ :=
  truncatedFactor n k b B * geometricBudget kind n B t + 12 * kind.counter.work +
    2 * T / (publicSize n k b B : ℝ) ^ 3

theorem oracleClip_mask (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (T : ℝ) (C : PortGraph.Vertex I bits cfg B) (cache : Cache Q) :
    oracleClip (b := b) kind I bits cfg T C cache ≤
      jointGoodCost (b := b) kind I bits cfg C cache + T * jointGoodFailure (b := b) I bits cfg C cache := by
  have hh := clipped_mask I.weight bits
    (oracle cfg (publicSize n k b B) (PortGraph.canonicalFrame I cfg b B C.val) cache)
    kind.counter T (jointOutcomeGood n k b B)
  have he :
      (oracle cfg (publicSize n k b B) (PortGraph.canonicalFrame I cfg b B C.val) cache).evaluate
        I.weight bits (fun o => if jointOutcomeGood n k b B o then 0 else 1) =
      jointGoodFailure (b := b) I bits cfg C cache := by
    rw [jointGoodFailure_eq]
    apply congrArg ((oracle cfg (publicSize n k b B) (PortGraph.canonicalFrame I cfg b B C.val)
      cache).evaluate I.weight bits)
    funext o
    by_cases h : jointOutcomeGood n k b B o <;> simp [h]
  rw [← jointGoodCost_eq, he] at hh
  exact hh

theorem calibrated_oracleClip_average (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (t epsilon xi gm : ℝ) (facts : AccessFacts (b := b) (B := B) I bits cfg t epsilon xi gm)
    (caches : PortGraph.Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (T : ℝ) (hT : 0 ≤ T) :
    initiationAverage (fun C => oracleClip (b := b) kind I bits cfg T C (caches C))
      (PortGraph.retained I bits cfg).card ≤ accessBudget kind n k b B t T := by
  have ha := calibrated_joint_good_accounts kind I bits cfg facts.terminals facts.nodup caches hc
    t epsilon xi gm facts.t_pos facts.epsilon_pos facts.epsilon_le facts.xi_le facts.retained_pos
    facts.calibrated facts.incidence facts.cutoff facts.count facts.square facts.clamp facts.residual
  have hm := initiation_mono _ _ ((PortGraph.retained I bits cfg).card : ℝ) (Nat.cast_nonneg _)
    (fun C => oracleClip_mask (b := b) kind I bits cfg T C (caches C))
  have he :
      initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C) +
        T * jointGoodFailure (b := b) I bits cfg C (caches C)) (PortGraph.retained I bits cfg).card =
      initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C))
        (PortGraph.retained I bits cfg).card +
      T * initiationAverage (fun C => jointGoodFailure (b := b) I bits cfg C (caches C))
        (PortGraph.retained I bits cfg).card := by
    simp only [initiationAverage, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [he] at hm
  have hc' := hm.trans (add_le_add ha.1 (mul_le_mul_of_nonneg_left ha.2 hT))
  have hr := vertex_ratio I bits cfg B facts.retained_pos
  have hw0 := kind.counter.work_nonneg
  have hwork := mul_le_mul_of_nonneg_left hr.2
    (show 0 ≤ 12 * kind.counter.work by positivity)
  have herr := mul_le_mul_of_nonneg_left hr.2
    (show 0 ≤ 2 * T * (1 / (publicSize n k b B : ℝ) ^ 3) by positivity)
  dsimp only [accessBudget]
  apply hc'.trans
  convert add_le_add
    (add_le_add (le_refl (truncatedFactor n k b B * geometricBudget kind n B t)) hwork) herr using 1 <;> ring

theorem oracleEnvelope_nonneg (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (T : ℝ) (hT : 0 ≤ T)
    (C : PortGraph.Vertex I bits cfg B) :
    0 ≤ oracleEnvelope (b := b) kind I bits cfg T C :=
  envelope_nonneg (Cache.Correct bits) (oracleClip (b := b) kind I bits cfg T) cache hc T
    (fun C c _ => clipped_expect_le_ceiling I.weight bits _ kind.counter T)
    (fun C c _ => clipped_expect_nonneg I.weight bits _ kind.counter T hT) C

theorem oracleClip_le_envelope (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (T : ℝ)
    (C : PortGraph.Vertex I bits cfg B) (c : Cache Q) (hcc : Cache.Correct bits c) :
    oracleClip (b := b) kind I bits cfg T C c ≤ oracleEnvelope (b := b) kind I bits cfg T C :=
  le_envelope (Cache.Correct bits) (oracleClip (b := b) kind I bits cfg T) cache hc T
    (fun C c _ => clipped_expect_le_ceiling I.weight bits _ kind.counter T) C c hcc

theorem calibrated_oracleEnvelope_average (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (t epsilon xi gm : ℝ) (facts : AccessFacts (b := b) (B := B) I bits cfg t epsilon xi gm)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (T : ℝ) (hT : 0 ≤ T) :
    initiationAverage (oracleEnvelope (b := b) (B := B) kind I bits cfg T) (PortGraph.retained I bits cfg).card ≤
      accessBudget kind n k b B t T := by
  have hg : (0 : ℝ) < (PortGraph.retained I bits cfg).card := by exact_mod_cast facts.retained_pos
  have hfamily (caches : PortGraph.Vertex I bits cfg B → Cache Q)
      (hcs : ∀ C, Cache.Correct bits (caches C)) :
      (∑ C, oracleClip (b := b) kind I bits cfg T C (caches C)) ≤
        accessBudget kind n k b B t T * (PortGraph.retained I bits cfg).card :=
    (div_le_iff₀ hg).mp (calibrated_oracleClip_average kind I bits cfg t epsilon xi gm facts caches hcs T hT)
  have hs := envelope_sum_le (Cache.Correct bits) (oracleClip (b := b) kind I bits cfg T)
    cache hc T (accessBudget kind n k b B t T * (PortGraph.retained I bits cfg).card)
    (fun C c _ => clipped_expect_le_ceiling I.weight bits _ kind.counter T) hfamily
  exact (div_le_iff₀ hg).mpr hs

end SteinerUpperBound.SavingEstimator.Resources

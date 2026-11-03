module

public import SteinerUpperBound.SavingEstimator.Resources.VO
public import SteinerUpperBound.SavingEstimator.Resources.Mean
public import SteinerUpperBound.LargeCoverProgram.PointNormalization
public import SteinerUpperBound.LargeCoverProgram.CausalCache

@[expose] public section

set_option maxHeartbeats 1800000

namespace SteinerUpperBound.SavingEstimator.Resources

open SteinerLowerBound QueryProgram Matching.Padded Covers.OracleProgram
open PortGraph.RuntimeAdapter PortGraph.RuntimeAdapter.Averaged
open scoped Classical BigOperators

variable {n k b B : ℕ} {Q : Type}

def pointBase (kind : CounterKind) (n k b B : ℕ) : ℕ :=
  match kind with
  | .ordinary => LargeCoverProgram.pointBudget n k b B
  | .positive => B + 1

noncomputable def pointCallback (cfg : LocalAccess.SlotConfig Q n (k + 1)) (b B : ℕ) :
    Mean.Callback (Sym2 (Fin n)) Q (Fin (k + 1)) :=
  fun u cache => LargeCoverProgram.point cfg.key cfg.scale (List.finRange n) cfg.terminals.toList
    cfg.covered (builder cfg.key cfg.scale cfg.terminals B cfg.covered b) (cfg.terminals.get u) cache

theorem concrete_point_family_clipped (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (t epsilon xi gm : ℝ) (facts : AccessFacts (b := b) (B := B) I bits cfg t epsilon xi gm)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (caches : Fin (k + 1) → Cache Q) (hc : ∀ u, Cache.Correct bits (caches u))
    (T : ℝ) (hT : 0 ≤ T) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (fun u => (pointCallback cfg b B u (caches u)).evaluate I.weight bits (clipped kind.counter T)) ≤
      pointBase kind n (k + 1) b B + accessBudget kind n (k + 1) b B t T := by
  have heta : (⟨cfg.key, cfg.scale, cfg.terminals, cfg.covered⟩ :
      LocalAccess.SlotConfig Q n (k + 1)) = cfg := by cases cfg; rfl
  let vo := builder cfg.key cfg.scale cfg.terminals B cfg.covered b
  have hw (stores : PortGraph.Vertex I bits cfg B → Cache Q)
      (hs : ∀ C, Cache.Correct bits (stores C)) :
      (∑ C, (vo (PortGraph.canonicalFrame I cfg b B C.val) (stores C)).evaluate I.weight bits
        (fun o => min (o.work : ℝ) T)) / (Nat.card (LargeCoverProgram.RetainedIndex bits cfg) : ℝ) ≤
        accessBudget .ordinary n (k + 1) b B t T := by
    have hh := calibrated_oracleClip_average .ordinary I bits cfg t epsilon xi gm facts stores hs T hT
    simpa only [vo, builder, heta, initiationAverage, oracleClip, clipped_ordinary,
      LargeCoverProgram.retainedIndex_card I bits cfg facts.terminals facts.nodup] using hh
  have hp (stores : PortGraph.Vertex I bits cfg B → Cache Q)
      (hs : ∀ C, Cache.Correct bits (stores C)) :
      (∑ C, (vo (PortGraph.canonicalFrame I cfg b B C.val) (stores C)).evaluate I.weight bits
        (fun o => min (o.positiveReplies : ℝ) T)) / (Nat.card (LargeCoverProgram.RetainedIndex bits cfg) : ℝ) ≤
        accessBudget .positive n (k + 1) b B t T := by
    have hh := calibrated_oracleClip_average .positive I bits cfg t epsilon xi gm facts stores hs T hT
    simpa only [vo, builder, heta, initiationAverage, oracleClip, clipped_positive,
      LargeCoverProgram.retainedIndex_card I bits cfg facts.terminals facts.nodup] using hh
  have hh := LargeCoverProgram.point_clipped_average I bits cfg facts.terminals facts.nodup hb vo caches hc
    T hT (accessBudget .ordinary n (k + 1) b B t T) (accessBudget .positive n (k + 1) b B t T) hw hp
  cases kind
  · simpa only [pointCallback, pointBase, vo, clipped_ordinary] using hh.1
  · simpa only [pointCallback, pointBase, vo, clipped_positive, Nat.cast_add, Nat.cast_one] using hh.2

theorem concrete_point_cache (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    ∀ u cache, Cache.Correct bits cache →
      Causal.Ensures I.weight bits (pointCallback cfg b B u cache)
        (fun reply => Cache.Correct bits reply.2) := by
  intro u cache hc
  exact LargeCoverProgram.point_cache_ensures I bits cfg hT hnd _
    (LargeCoverProgram.concrete_builder_cache_ensures I bits cfg hT hnd) u cache hc

def samplerBudget (kind : CounterKind) (proposals samples : ℕ) : ℕ :=
  match kind with
  | .ordinary => 16 * (proposals + samples + 1)
  | .positive => samples

theorem sampler_counter_le {M : Type*} (m : M → ℝ) (bits : Q → Bool)
    (query : Fin (k + 1) → Q) (root : Fin (k + 1)) (C s B : ℕ) (cache : Cache Q)
    (kind : CounterKind) :
    (Sampler.program query root C s B cache : Code M Q _).evaluate m bits kind.counter.value ≤
      samplerBudget kind B s := by
  cases kind
  · rw [ordinary_value]
    change (Sampler.program query root C s B cache : Code M Q _).evaluate m bits
      (fun o => (o.work : ℝ)) ≤ _
    apply (Mean.evaluate_mono_runs m bits _ _ (fun _ => (16 * (B + s + 1) : ℕ)) ?_).trans_eq
      (Code.evaluate_const m bits _ _)
    intro o ho
    have hr := Sampler.pool_resources m bits query root C s (Sampler.Store.initial cache B) o ho
    have hB : o.value.store.proposals ≤ B := by dsimp only [Sampler.Store.initial] at hr; omega
    have hw := hr.2.2.2.2.1
    dsimp only [Sampler.Store.initial] at hw
    exact_mod_cast hw.trans (by omega)
  · simpa only [positive_value, samplerBudget] using (Mean.sampler_expected m bits query root C s B cache).2

theorem concrete_mean_clipped (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (t epsilon xi gm : ℝ) (facts : AccessFacts (b := b) (B := B) I bits cfg t epsilon xi gm)
    (root : Fin (k + 1)) (C s proposals : ℕ) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (accuracy T : ℝ) (hT : 0 ≤ T) :
    (Mean.program (fun u => cfg.key (cfg.terminals.get u)) root C s proposals cache accuracy
      (pointCallback cfg b B)).evaluate I.weight bits (clipped kind.counter T) ≤
      samplerBudget kind proposals s + (6 * s + 42 : ℕ) * kind.counter.work +
        s * (pointBase kind n (k + 1) b B + accessBudget kind n (k + 1) b B t T) := by
  have hm := mean_family_clipped I.weight bits (pointCallback cfg b B)
    (concrete_point_cache I bits cfg facts.terminals facts.nodup) kind.counter T hT
    (fun u => cfg.key (cfg.terminals.get u)) root C s proposals cache hc hb accuracy
    (pointBase kind n (k + 1) b B + accessBudget kind n (k + 1) b B t T)
    (fun stores hs => concrete_point_family_clipped kind I bits cfg t epsilon xi gm facts hb stores hs T hT)
  exact hm.trans (add_le_add
    (add_le_add (sampler_counter_le I.weight bits _ root C s proposals cache kind) (le_refl _)) (le_refl _))

end SteinerUpperBound.SavingEstimator.Resources

module

public import SteinerUpperBound.EstimatorFrontend.Analysis.Records
public import SteinerUpperBound.EstimatorFrontend.Analysis.Probability

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Analysis

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Covers.Geometry
open scoped Classical BigOperators
open BandCompleteness

variable {n k : ℕ} {I : Instance (Fin n)} {label : Vector (Fin n) (k + 1)}
  {root : Fin (k + 1)} {t : Tables} {inverse : Vector (Fin (k + 1)) n}
  {bits : RuntimeWorld.Coordinate t k → Bool} {R : ℝ}

noncomputable local instance loopVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance loopLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

noncomputable abbrev recordBounds (I : Instance (Fin n)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (bits : RuntimeWorld.Coordinate t k → Bool) :
    Index t → ℝ → ℝ → Prop :=
  fun i z _ => SavingBounds I t inverse bits i z

noncomputable abbrev Completed (I : Instance (Fin n)) (t : Tables)
    (inverse : Vector (Fin (k + 1)) n) (bits : RuntimeWorld.Coordinate t k → Bool) :=
  EstimatorLoop.Completed bits (recordBounds I t inverse bits)
    (List.finRange (t.coarse.intervals + 1)) []

theorem savingRound_success (saving : Saving n k t) (epsilon : ℝ)
    (hs : SavingContract I t inverse bits saving epsilon)
    (i : Index t) (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    1 - epsilon ≤ Code.valueProbability I.weight bits (EstimatorFrontend.savingRound t saving i cache)
      (EstimatorLoop.GoodStep bits (recordBounds I t inverse bits) i) := by
  rw [EstimatorFrontend.savingRound, Code.valueProbability_map]
  apply (hs i cache hc).trans
  apply BandEstimator.valueProbability_mono
  rintro r ⟨⟨z, c⟩, rfl, hcache, hbounds⟩
  exact ⟨z, 0, c, rfl, hcache, hbounds⟩

theorem saving_rounds_success (saving : Saving n k t) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hs : SavingContract I t inverse bits saving epsilon)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    1 - ((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon ≤
      Code.valueProbability I.weight bits
        (EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving)
          (List.finRange (t.coarse.intervals + 1)) ⟨cache, []⟩)
        (Completed I t inverse bits) := by
  have hinit : EstimatorLoop.GoodState bits (recordBounds I t inverse bits)
      (⟨cache, []⟩ : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k)) := by
    refine ⟨hc, ?_⟩
    intro r hr
    exact (List.not_mem_nil hr).elim
  have h := EstimatorLoop.rounds_success I.weight bits (EstimatorFrontend.savingRound t saving)
    (recordBounds I t inverse bits) (fun _ => epsilon) (List.finRange (t.coarse.intervals + 1))
    ⟨cache, []⟩ hinit (fun _ _ => he)
    (fun i _ c hc => savingRound_success saving epsilon hs i c hc)
  simpa only [Completed, List.map_nil, List.map_const', List.length_finRange,
    List.sum_replicate, nsmul_eq_mul] using h

theorem afterSaving_success (G : Geometry I label root t inverse bits R)
    (upper : ℝ) (hu : I.mst ≤ upper ∧ upper ≤ (1 + nu) * I.mst)
    (r : Option (EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k)))
    (hr : Completed I t inverse bits r) :
    1 - 3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ) ≤
      Code.valueProbability I.weight bits
        (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse upper r)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
  obtain ⟨saved, rfl, hstate, hlog⟩ := hr
  have hlog' : saved.records.map EstimatorLoop.ScaleRecord.index =
      (List.finRange (t.coarse.intervals + 1)).reverse := by
    simpa only [List.append_nil] using hlog
  let bandCode := BandEstimator.fromParameters t.coarse label.get
    (fun i => RuntimeWorld.coarseKey t inverse i.val) root label.toList
      (parameters n (k + 1)) saved.cache
  let bandGood := BandEstimator.GoodOutput I bits t.coarse
    (fun i => RuntimeWorld.coarseKey t inverse i.val) label.toList
      (BandEstimator.publicData n (k + 1)) I.mst
  let next : (Option ℝ × Cache (RuntimeWorld.Coordinate t k)) →
      Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ) :=
    fun band => .tick 1 (match band.1 with
      | none => .pure none
      | some That => EstimatorFrontend.finish t upper That saved)
  have hb : 1 - 3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ) ≤
      Code.valueProbability I.weight bits bandCode bandGood := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      BandEstimator.fromParameters_success I bits t.coarse label.get G.injective
        (fun i => RuntimeWorld.coarseKey t inverse i.val) root label.toList (labels_list_native label)
        I.mst I.mst_nonneg (band_world G) saved.cache hstate.1
  have hn (band : Option ℝ × Cache (RuntimeWorld.Coordinate t k)) (hband : bandGood band) :
      1 - (0 : ℝ) ≤ Code.valueProbability I.weight bits (next band)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
    obtain ⟨_hc, That, hv, h0, h1, hloss⟩ := hband
    rw [band_score_eq G.terminals G.coarse_ratio] at h1 hloss
    have hf := finish_success G saved hlog' hstate.2 upper That hu ⟨h0, h1, hloss⟩
    dsimp only [next]
    rw [BandEstimator.valueProbability_tick, hv]
    simpa only [sub_zero] using hf.ge
  have h := Code.bind_success I.weight bits bandCode next bandGood
    (Code.SomeGood (GoodEstimate (2 - c) I.optimum))
    (3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ)) 0
    (by have hb := (beta_bounds n).1; positivity) (by norm_num) hb hn
  change _ ≤ Code.valueProbability I.weight bits (bandCode.bind next) _
  simpa only [sub_zero] using h

theorem afterMST_success (G : Geometry I label root t inverse bits R)
    (saving : Saving n k t) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (hs : SavingContract I t inverse bits saving epsilon)
    (mst : MSTApproximation.IntervalAnswer (RuntimeWorld.Coordinate t k))
    (hmst : MSTApproximation.CorrectInterval I nu mst ∧ Cache.Correct bits mst.cache) :
    1 - ((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon -
        3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ) ≤
      Code.valueProbability I.weight bits
        (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving mst)
        (Code.SomeGood (GoodEstimate (2 - c) I.optimum)) := by
  have hl := saving_rounds_success saving epsilon he hs mst.cache hmst.2
  have hn := afterSaving_success G mst.upper hmst.1.2.2
  have h := Code.bind_success I.weight bits
    (EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving)
      (List.finRange (t.coarse.intervals + 1)) ⟨mst.cache, []⟩)
    (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse mst.upper)
    (Completed I t inverse bits) (Code.SomeGood (GoodEstimate (2 - c) I.optimum))
    (((t.coarse.intervals + 1 : ℕ) : ℝ) * epsilon)
    (3 * beta n * ((t.coarse.intervals + 1 : ℕ) : ℝ))
    (by positivity) (by have hb := (beta_bounds n).1; positivity) hl hn
  rw [EstimatorFrontend.afterMST, BandEstimator.valueProbability_tick]
  exact h

end SteinerUpperBound.EstimatorFrontend.Analysis

module

public import SteinerUpperBound.LargeCoverProgram.Confidence
public import SteinerUpperBound.PortGraph.RuntimeAdapter

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical

attribute [local instance] copyDecidableEq

variable {Q : Type} {n k b B : ℕ}

noncomputable def residualVertexOf (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Finset (Fin n)) (hC : C ∈ PortGraph.parts I bits cfg) (hs : C.card ≤ B)
    (hh : coveredComponent cfg C = false) : PortGraph.Vertex I bits cfg B :=
  ⟨C, Finset.mem_filter.mpr ⟨hC, hs, (coveredComponent_false I bits cfg hT ⟨C, hC⟩).mp hh⟩⟩

theorem matchedPart_lifted (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (C : PortGraph.Vertex I bits cfg B)
    (rank : Matching.Rank (PortGraph.Copy I bits cfg b B)) :
    matchedPart I bits cfg (PortGraph.liftedGraph I bits cfg b B) C.val rank =
      ((PortGraph.graph I bits cfg b B).vertexOracle rank C).value.isSome := by
  rw [matchedPart, dif_pos (PortGraph.vertex_part I bits cfg B C)]
  apply Bool.eq_iff_iff.mpr
  simp only [Option.isSome_iff_exists, Matching.Graph.vertexOracle_eq_some_iff]
  exact PortGraph.lifted_matched I bits cfg b B rank C

noncomputable def concreteVOError (n k B : ℕ) : ℝ :=
  1 / (PortGraph.RuntimeAdapter.publicSize n k 1 B : ℝ) ^ 30

theorem concreteVOError_nonneg (n k B : ℕ) : 0 ≤ concreteVOError n k B := by
  unfold concreteVOError
  positivity

theorem concreteVOError_bound (n k b B : ℕ) (hb : 1 ≤ b) :
    1 / (PortGraph.RuntimeAdapter.publicSize n k b B : ℝ) ^ 30 ≤ concreteVOError n k B := by
  have hs : PortGraph.RuntimeAdapter.publicSize n k 1 B ≤
      PortGraph.RuntimeAdapter.publicSize n k b B := by
    unfold PortGraph.RuntimeAdapter.publicSize
    gcongr
  have hp : (0 : ℝ) < PortGraph.RuntimeAdapter.publicSize n k 1 B := by
    have hh : 2 ≤ PortGraph.RuntimeAdapter.publicSize n k 1 B := by
      unfold PortGraph.RuntimeAdapter.publicSize
      omega
    exact_mod_cast (show 0 < PortGraph.RuntimeAdapter.publicSize n k 1 B by omega)
  unfold concreteVOError
  apply one_div_le_one_div_of_le (pow_pos hp _)
  gcongr

theorem concrete_builder_cache_ensures (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    CanonicalVOEnsures I bits cfg b B
      (PortGraph.RuntimeAdapter.builder cfg.key cfg.scale cfg.terminals B cfg.covered b) := by
  have heta : (⟨cfg.key, cfg.scale, cfg.terminals, cfg.covered⟩ :
      LocalAccess.SlotConfig Q n (k + 1)) = cfg := by cases cfg; rfl
  intro C hC hs hh cache hc
  let C0 := residualVertexOf I bits cfg hT C hC hs hh
  simpa only [PortGraph.RuntimeAdapter.builder, heta, C0, residualVertexOf] using
    (PortGraph.RuntimeAdapter.oracle_preserves (b := b) I bits cfg hT hnd C0 cache hc)

/-- The supplied callback is now the ACTUAL concrete ambient-root/name runtime.
All value/cache refinement is discharged from its proved primitive adapter and
the generic actual-code matching theorem; no final VO certificate is assumed. -/
theorem concrete_builder_refinement (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : 1 ≤ b) :
    VOApproxRefinement I bits cfg b B
      (PortGraph.RuntimeAdapter.builder cfg.key cfg.scale cfg.terminals B cfg.covered b)
      (Matching.Rank.uniform (E := PortGraph.Copy I bits cfg b B))
      (matchedPart I bits cfg (PortGraph.liftedGraph I bits cfg b B))
      (concreteVOError n (k + 1) B) := by
  have heta : (⟨cfg.key, cfg.scale, cfg.terminals, cfg.covered⟩ :
      LocalAccess.SlotConfig Q n (k + 1)) = cfg := by cases cfg; rfl
  refine ⟨?_, ?_⟩
  · exact concrete_builder_cache_ensures I bits cfg hT hnd
  · intro C hC hs hh cache hc F hF₀ hF₁
    let C0 := residualVertexOf I bits cfg hT C hC hs hh
    have he := PortGraph.RuntimeAdapter.oracle_mean_error (b := b) I bits cfg hT hnd C0 cache hc F hF₀ hF₁
    have hm : PortGraph.RuntimeAdapter.strictMean (PortGraph.graph I bits cfg b B) C0 F =
        (Matching.Rank.uniform (E := PortGraph.Copy I bits cfg b B)).expect
          (fun rank => F (matchedPart I bits cfg (PortGraph.liftedGraph I bits cfg b B) C rank)) := by
      unfold PortGraph.RuntimeAdapter.strictMean
      apply congrArg (Matching.Rank.uniform (E := PortGraph.Copy I bits cfg b B)).expect
      funext rank
      exact congrArg F (matchedPart_lifted I bits cfg C0 rank).symm
    rw [hm] at he
    refine le_trans ?_ (concreteVOError_bound n (k + 1) b B hb)
    simpa only [PortGraph.RuntimeAdapter.builder, heta, C0, residualVertexOf] using he

theorem concrete_largeVORefinement (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (terminals : Vector (Fin n) (k + 1)) (key : Fin n → Q) (a : ℝ)
    (hT : terminals.toList.toFinset = I.terminals) (hnd : terminals.toList.Nodup) :
    LargeVORefinement I bits p terminals key a
      (PortGraph.RuntimeAdapter.builder key a terminals p.cutoff)
      (concreteVOError n (k + 1) p.cutoff) := by
  intro gm selected D cfg _ _ _ _ _ _ _
  exact ⟨Matching.Rank.uniform, concrete_builder_refinement I bits cfg hT hnd (rowCapacity_pos n p gm)⟩

/-- Closed scalar confidence theorem for the actual executable D-aware VO
builder. Only explicit public numerical tests and the metric/retention model
remain; neither a VO, score, saving, stability, nor matching certificate is an
assumption. Ordinary/disclosure clocks may be applied to this genuine code. -/
theorem program_concrete_saving_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (hT : terminals.toList.toFinset = I.terminals)
    (hnd : terminals.toList.Nodup) (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (key (terminals.get u))).Nonempty)
    (heps : 0 < (p.eps : ℝ)) (heps1 : (p.eps : ℝ) ≤ 1) (hxi : 0 < (p.xi : ℝ))
    (hxi' : (p.xi : ℝ) ≤ (p.eps : ℝ) / 100)
    (hB : SavingScores.smallThreshold (p.eps : ℝ) ≤ p.cutoff)
    (betaPool betaMean : ℝ) (ht : 0 < p.t) (hbeta : 0 < betaPool) (hbeta' : betaPool < 1 / 4)
    (hL : ReusableSample.logBudget p.t betaPool ≤ p.Lbar)
    (hM : ReusableSample.rowBudget n p.t betaPool ≤ p.Mbar)
    (hs : 0 < p.meanSamples) (hbudget : 1 ≤ betaMean * ((p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2))
    (hcalSamples : 0 < p.calibrationSamples)
    (hcalCap : p.calibrationSamples * p.calibrationRowCap ≤ p.calibrationProposals)
    (hcalExp : Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) ≤ (p.xi : ℝ) / 8) :
    Code.valueProbability I.weight bits
      (program p terminals root key a (PortGraph.RuntimeAdapter.builder key a terminals p.cutoff) c)
      (fun r => ¬ GoodSaving
        (Covers.Geometry.savingOn I (I.terminals.filter (fun v => bits (key v) = true)) a (5 * a / 8))
        (Covers.Rejection.retained (fun u => bits (key (terminals.get u)))).card (p.eps : ℝ) r.value) ≤
      ((p.calibrationSamples : ℝ) * Real.exp (-(p.calibrationRowCap : ℝ) / (k + 1)) +
        8 / (((p.xi : ℝ) / 4) ^ 2 * p.calibrationSamples)) +
      (Mean.capError (fun u => bits (key (terminals.get u))) p.poolRowCap p.poolSamples p.poolProposals +
        betaPool +
        (Mean.capError (fun u => bits (key (terminals.get u))) p.meanRowCap p.meanSamples p.meanProposals +
          p.meanSamples * concreteVOError n (k + 1) p.cutoff + betaMean)) :=
  program_saving_confidence I bits p terminals root key a hT hnd _ c hc hb heps heps1 hxi hxi' hB
    betaPool betaMean _ (concreteVOError_nonneg _ _ _)
    (concrete_largeVORefinement I bits p terminals key a hT hnd)
    ht hbeta hbeta' hL hM hs hbudget hcalSamples hcalCap hcalExp

end SteinerUpperBound.LargeCoverProgram

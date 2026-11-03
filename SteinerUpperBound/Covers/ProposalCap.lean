module

public import SteinerUpperBound.Covers.DisclosureBudget

@[expose] public section

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound
open scoped Classical BigOperators
open FiniteSampling RetentionTree

variable {U : Type*} [Fintype U] [Nonempty U]

theorem waiting_exp_le_two (b : U → Bool) (hb : (retained b).Nonempty)
    (C : ℕ) (a : ℝ) (ha : a ≤ hitRate b / 2) :
    (tape (Law.uniform U) C).expect (fun w => Real.exp (a * waiting b C w)) ≤ 2 := by
  induction C with
  | zero => simp [tape, waiting]
  | succ C ih =>
    rw [expect_tape_succ]
    have hf (x : U) :
        (tape (Law.uniform U) C).expect
          (fun w => Real.exp (a * waiting b (C + 1) (Fin.cons x w))) =
        if b x = true then Real.exp a
        else Real.exp a *
          (tape (Law.uniform U) C).expect (fun w => Real.exp (a * waiting b C w)) := by
      cases hx : b x
      · simp only [waiting, Fin.cons_zero, Fin.tail_cons, hx, Bool.false_eq_true,
          ↓reduceIte, Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add]
        rw [Law.expect_const_mul]
      · simp [waiting, hx]
    simp_rw [hf]
    rw [uniform_split b hb, Law.expect_const]
    have hstep := mul_le_mul_of_nonneg_left ih
      (mul_nonneg (sub_nonneg.mpr (hitRate_le_one b)) (Real.exp_pos a).le)
    have hbase : Real.exp a * (1 - hitRate b / 2) ≤ 1 := by
      have he := mul_le_mul_of_nonneg_left
        (Real.add_one_le_exp (-(hitRate b / 2))) (Real.exp_pos a).le
      have hsum : a + -(hitRate b / 2) ≤ 0 := by linarith
      have hexp : Real.exp (a + -(hitRate b / 2)) ≤ 1 := by
        simpa using Real.exp_le_exp.mpr hsum
      rw [Real.exp_add] at hexp
      nlinarith
    nlinarith

theorem proposals_exp (b : U → Bool) (hb : (retained b).Nonempty) (C s : ℕ) :
    (poolLaw C s).expect (fun rows =>
      Real.exp ((proposals b C s rows : ℝ) / (4 * Fintype.card U))) ≤ Real.exp s := by
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  let a : ℝ := 1 / (4 * Fintype.card U)
  have ha : a ≤ hitRate b / 2 := by
    have h := hitRate_ge_inverse b hb
    have hinv : (0 : ℝ) ≤ 1 / Fintype.card U := by positivity
    have he : a = (1 / (Fintype.card U : ℝ)) / 4 := by dsimp [a]; ring
    rw [he]
    linarith
  have he (rows : Fin s → Fin C → U) :
      Real.exp ((proposals b C s rows : ℝ) / (4 * Fintype.card U)) =
        ∏ j, Real.exp (a * waiting b C (rows j)) := by
    rw [← Real.exp_sum, ← Finset.mul_sum]
    congr 1
    simp only [proposals, Nat.cast_sum]
    dsimp [a]
    ring
  simp_rw [he]
  rw [poolLaw, expect_product (tape (Law.uniform U) C)
    (fun w => Real.exp (a * waiting b C w)) s]
  have h := waiting_exp_le_two b hb C a ha
  calc
    _ ≤ (2 : ℝ) ^ s := pow_le_pow_left₀ (Law.expect_nonneg _ (fun _ => (Real.exp_pos _).le)) h s
    _ ≤ (Real.exp 1) ^ s := pow_le_pow_left₀ (by norm_num)
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) s
    _ = _ := by rw [← Real.exp_nat_mul]; simp

theorem proposals_tail (b : U → Bool) (hb : (retained b).Nonempty)
    (C s B : ℕ) :
    (poolLaw C s).prob {rows | B < proposals b C s rows} ≤
      Real.exp ((s : ℝ) - (B : ℝ) / (4 * Fintype.card U)) := by
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hsub : {rows | B < proposals b C s rows} ⊆
      {rows | Real.exp ((B : ℝ) / (4 * Fintype.card U)) ≤
        Real.exp ((proposals b C s rows : ℝ) / (4 * Fintype.card U))} := by
    intro rows hrows
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hrows.le
  calc
    _ ≤ (poolLaw C s).prob
        {rows | Real.exp ((B : ℝ) / (4 * Fintype.card U)) ≤
          Real.exp ((proposals b C s rows : ℝ) / (4 * Fintype.card U))} :=
      Law.prob_mono _ hsub
    _ ≤ (poolLaw C s).expect
        (fun rows => Real.exp ((proposals b C s rows : ℝ) / (4 * Fintype.card U))) /
          Real.exp ((B : ℝ) / (4 * Fintype.card U)) :=
      Law.markov _ (fun _ => (Real.exp_pos _).le) (Real.exp_pos _)
    _ ≤ Real.exp s / Real.exp ((B : ℝ) / (4 * Fintype.card U)) :=
      div_le_div_of_nonneg_right (proposals_exp b hb C s) (Real.exp_pos _).le
    _ = _ := (Real.exp_sub _ _).symm

noncomputable def proposalBudget (k s : ℕ) (β : ℝ) : ℕ :=
  ⌈4 * (k : ℝ) * ((s : ℝ) + Real.log (2 / β))⌉₊

theorem proposals_budget (b : U → Bool) (hb : (retained b).Nonempty)
    (C s : ℕ) (β : ℝ) (hβ : 0 < β) :
    (poolLaw C s).prob
      {rows | proposalBudget (Fintype.card U) s β < proposals b C s rows} ≤ β / 2 := by
  apply (proposals_tail b hb C s _).trans
  have hk : (0 : ℝ) < Fintype.card U := by exact_mod_cast Fintype.card_pos
  have hB := Nat.le_ceil
    (4 * (Fintype.card U : ℝ) * ((s : ℝ) + Real.log (2 / β)))
  calc
    _ ≤ Real.exp (-Real.log (2 / β)) := by
      apply Real.exp_le_exp.mpr
      have hd : (s : ℝ) + Real.log (2 / β) ≤
          (proposalBudget (Fintype.card U) s β : ℝ) / (4 * Fintype.card U) :=
        (le_div_iff₀ (by positivity)).mpr (by dsimp [proposalBudget]; nlinarith)
      linarith
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / β)]; field_simp

def cappedPoolTree (root : U) (C s B : ℕ) (rows : Fin s → Fin C → U) :
    DecisionTree U Bool (Option (Fin s → U)) :=
  ((sampleTree C s rows).truncate B).map
    (fun out => out.map (fun v j => (v j).getD root))

theorem cappedPoolTree_queries (b : U → Bool) (root : U)
    (C s B : ℕ) (rows : Fin s → Fin C → U) :
    (cappedPoolTree root C s B rows).queries b ≤ B := by
  rw [cappedPoolTree, DecisionTree.queries_map]
  exact DecisionTree.truncate_queries _ _ _

theorem cappedPoolTree_output (b : U → Bool) (root : U)
    (C s B : ℕ) (rows : Fin s → Fin C → U) (h : proposals b C s rows ≤ B) :
    (cappedPoolTree root C s B rows).output b = some (labels b root C s rows) := by
  rw [cappedPoolTree, DecisionTree.output_map, DecisionTree.truncate_output]
  · rw [sampleTree_output]
    rfl
  · rwa [sampleTree_queries]

theorem cappedPoolTree_uniform_close (b : U → Bool) (hb : (retained b).Nonempty)
    (root : U) (C s B : ℕ) :
    Law.Close
      ((poolLaw C s).map (fun rows => (cappedPoolTree root C s B rows).output b))
      ((tape (uniformRetained b hb) s).map some)
      ((poolLaw C s).prob {rows | B < proposals b C s rows} +
        (poolLaw C s).prob {rows | ¬ Successful b C s rows}) := by
  have hc := Law.close_maps (poolLaw C s)
    (fun rows => (cappedPoolTree root C s B rows).output b)
    (fun rows => some (labels b root C s rows))
  have hsub : {rows | (cappedPoolTree root C s B rows).output b ≠
        some (labels b root C s rows)} ⊆ {rows | B < proposals b C s rows} := by
    intro rows hrows
    by_contra hn
    exact hrows (cappedPoolTree_output b root C s B rows (le_of_not_gt hn))
  have hc' := hc.mono (Law.prob_mono _ hsub)
  have hu := (pool_uniform_close b hb root C s).map (some : (Fin s → U) → Option (Fin s → U))
  rw [LawOperations.map_comp] at hu
  exact hc'.trans hu

/-- The final sampler uses a fixed `O(k(s + log(1/β)))` proposal cap. The
calibration still uses the proved Chebyshev sample count. -/
theorem capped_sampler_and_calibration (b : U → Bool) (hb : (retained b).Nonempty)
    (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := calibrationSamples (β / 2) ξ
    let C := proposalRowCap (Fintype.card U) s (β / 2) ξ
    let B := proposalBudget (Fintype.card U) s β
    (poolLaw C s).prob
      {rows | B < proposals b C s rows ∨
        ¬ Successful b C s rows ∨ ¬ Calibrated b C s ξ rows} ≤ β := by
  dsimp only
  have hsample := sampler_and_calibration b hb (β / 2) ξ (by positivity)
    (by linarith) hξ hξ1
  have hcap := proposals_budget b hb
    (proposalRowCap (Fintype.card U) (calibrationSamples (β / 2) ξ) (β / 2) ξ)
    (calibrationSamples (β / 2) ξ) β hβ
  exact (Law.prob_union_le _ _ _).trans ((add_le_add hcap hsample).trans (by ring_nf; rfl))

theorem capped_sampler_uniform_budget (b : U → Bool) (hb : (retained b).Nonempty)
    (root : U) (β ξ : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    let s := calibrationSamples (β / 2) ξ
    let C := proposalRowCap (Fintype.card U) s (β / 2) ξ
    let B := proposalBudget (Fintype.card U) s β
    Law.Close
      ((poolLaw C s).map (fun rows => (cappedPoolTree root C s B rows).output b))
      ((tape (uniformRetained b hb) s).map some) β := by
  dsimp only
  let s := calibrationSamples (β / 2) ξ
  let C := proposalRowCap (Fintype.card U) s (β / 2) ξ
  let B := proposalBudget (Fintype.card U) s β
  apply (cappedPoolTree_uniform_close b hb root C s B).mono
  have hcap := proposals_budget b hb C s β hβ
  have hsample := sampler_and_calibration b hb (β / 2) ξ (by positivity)
    (by linarith) hξ hξ1
  have hfail : (poolLaw C s).prob {rows | ¬ Successful b C s rows} ≤ β / 2 :=
    (Law.prob_mono _ (fun _ h => Or.inl h)).trans hsample
  exact (add_le_add hcap hfail).trans (by ring_nf; rfl)

theorem first_some_retained (b : U → Bool) (C : ℕ) (w : Fin C → U)
    (x : U) (h : first b C w = some x) : b x = true := by
  induction C with
  | zero => simp [first] at h
  | succ C ih =>
    cases hx : b (w 0)
    · exact ih (Fin.tail w) (by simpa only [first, hx, Bool.false_eq_true, ↓reduceIte] using h)
    · have he : w 0 = x := by simpa only [first, hx, ↓reduceIte, Option.some.injEq] using h
      simpa only [he] using hx

theorem successful_labels_retained (b : U → Bool) (root : U)
    (C s : ℕ) (rows : Fin s → Fin C → U) (h : Successful b C s rows) :
    ∀ j, b (labels b root C s rows j) = true := by
  intro j
  cases he : first b C (rows j) with
  | none => exact (h j he).elim
  | some x =>
    simpa only [labels, he, Option.getD_some] using first_some_retained b C (rows j) x he

end SteinerUpperBound.Covers.Rejection

namespace SteinerUpperBound.Covers.RetentionTree

open SteinerLowerBound

variable {Q A : Type*}

theorem queries_truncate_min (t : DecisionTree Q Bool A) (b : Q → Bool) (B : ℕ) :
    (t.truncate B).queries b = min B (t.queries b) := by
  induction B generalizing t with
  | zero => cases t <;> simp [DecisionTree.truncate, DecisionTree.queries, DecisionTree.transcript]
  | succ B ih =>
    cases t with
    | leaf r => simp [DecisionTree.truncate, DecisionTree.queries, DecisionTree.transcript]
    | query q next =>
      rw [DecisionTree.truncate, queries_query, ih, queries_query]
      omega

theorem positiveHeight_truncate (t : DecisionTree Q Bool A) (B : ℕ) :
    positiveHeight (t.truncate B) ≤ positiveHeight t := by
  induction B generalizing t with
  | zero => cases t <;> simp [DecisionTree.truncate, positiveHeight]
  | succ B ih =>
    cases t with
    | leaf => simp [DecisionTree.truncate, positiveHeight]
    | query q next =>
      exact max_le_max (ih (next false)) (Nat.add_le_add_left (ih (next true)) 1)

end SteinerUpperBound.Covers.RetentionTree

namespace SteinerUpperBound.Covers.Rejection

open SteinerLowerBound RetentionTree

variable {U : Type*} [Fintype U]

theorem cappedPoolTree_proposals (b : U → Bool) (root : U)
    (C s B : ℕ) (rows : Fin s → Fin C → U) :
    (cappedPoolTree root C s B rows).queries b = min B (proposals b C s rows) := by
  rw [cappedPoolTree, DecisionTree.queries_map, queries_truncate_min, sampleTree_queries]

theorem cappedPoolTree_positiveHeight (root : U) (C s B : ℕ)
    (rows : Fin s → Fin C → U) : positiveHeight (cappedPoolTree root C s B rows) ≤ s := by
  rw [cappedPoolTree, positiveHeight_map]
  exact (positiveHeight_truncate _ _).trans (sampleTree_positiveHeight C s rows)

end SteinerUpperBound.Covers.Rejection

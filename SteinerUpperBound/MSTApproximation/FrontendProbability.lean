module

public import SteinerUpperBound.MSTApproximation.Correctness

@[expose] public section

namespace SteinerUpperBound.MSTApproximation

open SteinerLowerBound Covers.Geometry QueryProgram
open scoped Classical BigOperators
open Covers.Rejection Covers.FiniteSampling

variable {V Q : Type*} [Fintype V] {k : ℕ}

theorem scaleTrace_probability (w : Sym2 V → ℝ) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : V → Q)
    (a xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) (cache : Cache Q)
    (hc : Cache.Correct b cache) (E : Set (ScaleAnswer Q)) :
    Code.probability w b (scaleProgram e key a xi B C samples l root cache) {o | o.value ∈ E} =
      (poolLaw C samples).prob {rows | scaleTrace w b e key a xi B C samples l root cache rows ∈ E} := by
  classical
  let F : ScaleAnswer Q → ℝ := fun r => if r ∈ E then 1 else 0
  have hlaw := scaleProgram_law w b e key a xi B C samples l root cache hc F
  unfold Code.probability
  calc
    _ = (scaleProgram e key a xi B C samples l root cache).evaluate w b (fun o => F o.value) := by
      apply congrArg ((scaleProgram e key a xi B C samples l root cache).evaluate w b)
      funext o
      by_cases h : o.value ∈ E <;> simp [F, h]
    _ = _ := hlaw
    _ = _ := by
      rw [Law.prob_eq_expect]
      apply congrArg (poolLaw C samples).expect
      funext rows
      by_cases h : scaleTrace w b e key a xi B C samples l root cache rows ∈ E <;> simp [F, h]

theorem probability_tape_succ {U : Type*} [Fintype U] (mu : Law U) (n : ℕ)
    (E : Set (Fin (n + 1) → U)) :
    (tape mu (n + 1)).prob E =
      mu.expect (fun x => (tape mu n).prob {rows | Fin.cons x rows ∈ E}) := by
  classical
  rw [Law.prob_eq_expect, expect_tape_succ]
  apply congrArg mu.expect
  funext x
  rw [Law.prob_eq_expect]
  apply congrArg (tape mu n).expect
  funext rows
  by_cases h : Fin.cons x rows ∈ E <;> simp [h]

noncomputable def GoodSteps (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1)) :
    (is : List ℕ) → FrontendState Q →
      (Fin is.length → Fin samples → Fin C → Fin (k + 1)) → Prop
  | [], _, _ => True
  | i :: is, s, rows =>
      let r := scaleTrace I.weight b e (key i) (g.scale i) xi B C samples l root s.cache (rows 0)
      ScaleGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi r ∧
        GoodSteps I b e key g xi B C samples l root is (recordScale g xi s i r) (Fin.tail rows)

theorem goodSteps_failure (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (hinj : Function.Injective e) (key : ℕ → V → Q)
    (g : Grid) (xi beta : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hc : Cache.Correct b s.cache)
    (he : Finset.univ.image e = l.toFinset) (hr : ∀ i ∈ is, b (key i (e root)) = true)
    (hs : 0 < samples) (hx : 0 < xi) (hx1 : xi ≤ 1) (hb : 0 < beta) (hb1 : beta ≤ 1)
    (hbudget : 256 ≤ beta * ((samples : ℝ) * xi ^ 2))
    (hrow : Real.exp (-(C : ℝ) / (k + 1)) ≤ beta * xi / (16 * samples)) :
    (tape (poolLaw C samples) is.length).prob
      {rows | ¬ GoodSteps I b e key g xi B C samples l root is s rows} ≤ (is.length : ℝ) * beta := by
  classical
  induction is generalizing s with
  | nil => simp [GoodSteps, List.length_nil]
  | cons i is ih =>
    let step := fun row => scaleTrace I.weight b e (key i) (g.scale i) xi B C samples l root s.cache row
    let Bad : Set (Fin samples → Fin C → Fin (k + 1)) :=
      {row | ¬ ScaleGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi (step row)}
    have hhead : (poolLaw C samples).prob Bad ≤ beta := by
      have h := scaleProgram_failure I b e hinj (key i) (g.scale i) xi beta B C samples l root s.cache
        hc (hr i List.mem_cons_self) he hs hx hx1 hb hb1 hbudget hrow
      calc
        (poolLaw C samples).prob Bad =
            Code.probability I.weight b (scaleProgram e (key i) (g.scale i) xi B C samples l root s.cache)
              {o | ¬ ScaleGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi o.value} := by
          simpa only [Set.mem_ofPred_eq] using
            (scaleTrace_probability I.weight b e (key i) (g.scale i) xi B C samples l root s.cache hc
              {r | ¬ ScaleGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi r}).symm
        _ ≤ beta := h
    change (tape (poolLaw C samples) (is.length + 1)).prob
      {rows | ¬ GoodSteps I b e key g xi B C samples l root (i :: is) s rows} ≤ _
    rw [probability_tape_succ]
    have hpoint row : (tape (poolLaw C samples) is.length).prob
        {rows | ¬ GoodSteps I b e key g xi B C samples l root (i :: is) s (Fin.cons row rows)} ≤
        (if row ∈ Bad then (1 : ℝ) else 0) + (is.length : ℝ) * beta := by
      have hcache := (scaleTrace_fields I b e (key i) (g.scale i) xi B C samples l root s.cache
        hc (hr i List.mem_cons_self) he row).2.2.2
      have ht := ih (recordScale g xi s i (step row)) hcache
        (fun j hj => hr j (List.mem_cons_of_mem _ hj))
      by_cases hbad : row ∈ Bad
      · rw [if_pos hbad]
        exact ((tape (poolLaw C samples) is.length).prob_le_one _).trans
          (by
            have h : 0 ≤ (is.length : ℝ) * beta := by positivity
            simpa only [add_zero] using add_le_add (show (1 : ℝ) ≤ 1 from le_rfl) h)
      · rw [if_neg hbad, zero_add]
        have hgood : ScaleGood I (ComponentExplore.retained b (key i) l.toFinset)
            (g.scale i) B xi (step row) := by simpa only [Bad, Set.mem_ofPred_eq, not_not] using hbad
        have hevents : {rows | ¬ GoodSteps I b e key g xi B C samples l root (i :: is) s (Fin.cons row rows)} =
            {rows | ¬ GoodSteps I b e key g xi B C samples l root is
              (recordScale g xi s i (step row)) rows} := by
          ext rows
          simp only [GoodSteps, Fin.cons_zero, Fin.tail_cons, step, hgood, true_and, Set.mem_ofPred_eq]
        rw [hevents]
        exact ht
    have hmean := (poolLaw C samples).expect_mono hpoint
    rw [Law.expect_add, Law.expect_const] at hmean
    have hprob : (poolLaw C samples).expect (fun row => if row ∈ Bad then (1 : ℝ) else 0) =
        (poolLaw C samples).prob Bad := by
      rw [Law.prob_eq_expect]
      apply congrArg (poolLaw C samples).expect
      funext row
      by_cases h : row ∈ Bad <;> simp [h]
    rw [hprob] at hmean
    calc
      _ ≤ (poolLaw C samples).prob Bad + (is.length : ℝ) * beta := hmean
      _ ≤ beta + (is.length : ℝ) * beta := add_le_add hhead le_rfl
      _ = _ := by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

def ReadingGood (I : Instance V) (N : Finset V) (a : ℝ) (B : ℕ) (xi : ℝ) (r : Measurement) : Prop :=
  r.successful = true ∧ (1 - xi) * (N.card : ℝ) ≤ r.gminus ∧ r.gminus ≤ N.card ∧
    |r.empirical - scoreMean I N a B| ≤ xi

theorem goodSteps_readings (I : Instance V) (b : Q → Bool)
    (e : Fin (k + 1) → V) (key : ℕ → V → Q)
    (g : Grid) (xi : ℝ) (B C samples : ℕ) (l : List V) (root : Fin (k + 1))
    (is : List ℕ) (s : FrontendState Q) (hn : is.Nodup) (hs : s.successful = true)
    (rows : Fin is.length → Fin samples → Fin C → Fin (k + 1))
    (hgood : GoodSteps I b e key g xi B C samples l root is s rows) :
    let r := frontendTrace I.weight b e key g xi B C samples l root is s rows
    r.successful = true ∧ ∀ i ∈ is,
      ReadingGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi (r.readings i) := by
  induction is generalizing s with
  | nil => exact ⟨hs, by simp⟩
  | cons i is ih =>
    let step := scaleTrace I.weight b e (key i) (g.scale i) xi B C samples l root s.cache (rows 0)
    have hg : ScaleGood I (ComponentExplore.retained b (key i) l.toFinset) (g.scale i) B xi step ∧
        GoodSteps I b e key g xi B C samples l root is (recordScale g xi s i step) (Fin.tail rows) := hgood
    have hni := (List.nodup_cons.mp hn).1
    have hnt := (List.nodup_cons.mp hn).2
    have hstart : (recordScale g xi s i step).successful = true := by simp [hs, hg.1.1]
    obtain ⟨hts, htr⟩ := ih _ hnt hstart (Fin.tail rows) hg.2
    refine ⟨hts, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with hji | hj
    · subst j
      have hread := frontendTrace_reading_unchanged I.weight b e key g xi B C samples l root is
        (recordScale g xi s i step) i hni (Fin.tail rows)
      change ReadingGood I _ _ _ _
        ((frontendTrace I.weight b e key g xi B C samples l root is
          (recordScale g xi s i step) (Fin.tail rows)).readings i)
      rw [hread]
      simpa only [recordScale, Function.update_self, ReadingGood, ScaleGood] using hg.1
    · exact htr j hj

end SteinerUpperBound.MSTApproximation

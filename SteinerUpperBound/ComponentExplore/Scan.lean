module

public import SteinerUpperBound.ComponentExplore.Step

@[expose] public section

namespace SteinerUpperBound.ComponentExplore

open QueryProgram
open scoped Classical

variable {V Q : Type*} [Fintype V]

noncomputable def retained (b : Q → Bool) (key : V → Q) (T : Finset V) : Finset V :=
  T.filter (fun x => b (key x) = true)

noncomputable def retainedGraph (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (T : Finset V) (a : ℝ) : SimpleGraph V :=
  TerminalMST.below w (retained b key T) a

theorem retainedGraph_support (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (T : Finset V) (a : ℝ) :
    Network.TerminalOnly T (retainedGraph w b key T a) := by
  intro x y hxy
  obtain ⟨_, hx, hy, _⟩ := (TerminalMST.below_adj _ _ _ _ _).mp hxy
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1⟩

theorem reachable_retained (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (T : Finset V) (a : ℝ) {x y : V} (hx : x ∈ retained b key T)
    (hxy : (retainedGraph w b key T a).Reachable x y) : y ∈ retained b key T := by
  obtain ⟨p⟩ := hxy
  revert hx
  induction p with
  | nil => exact id
  | @cons x y z hxy p ih =>
      intro _
      exact ih ((TerminalMST.below_adj _ _ _ _ _).mp hxy).2.2.1

theorem step_points_mono (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    s.points.toFinset ⊆ (stepResult w b key a B x s y).value.points.toFinset := by
  by_cases hb : B < s.count <;>
    by_cases hs : (memberResult y s.points).value = true <;>
    by_cases hd : w (Sym2.mk x y) < a <;>
    cases hr : (Cache.resolved b (key y) s.cache).value.1 <;>
    simp [stepResult, hb, hs, hd, hr, Memory.remember, Outcome.add, Outcome.combine,
      Outcome.pure]

theorem step_processed (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V) :
    (stepResult w b key a B x s y).value.processed = s.processed := by
  by_cases hb : B < s.count <;>
    by_cases hs : (memberResult y s.points).value = true <;>
    by_cases hd : w (Sym2.mk x y) < a <;>
    cases hr : (Cache.resolved b (key y) s.cache).value.1 <;>
    simp [stepResult, hb, hs, hd, hr, Memory.remember, Outcome.add, Outcome.combine,
      Outcome.pure]

theorem step_found (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (T : Finset V) (a : ℝ) (B : ℕ) (x : V) (s : Memory V Q) (y : V)
    (hs : Memory.Valid b s) (hx : x ∈ retained b key T) (hy : y ∈ T)
    (hxf : x ∈ s.points.toFinset) :
    (stepResult w b key a B x s y).value.points.toFinset =
      if B < s.points.toFinset.card then s.points.toFinset else
        if (retainedGraph w b key T a).Adj x y then insert y s.points.toFinset
        else s.points.toFinset := by
  have hcard : s.points.toFinset.card = s.count := Memory.card_eq b s hs
  by_cases hb : B < s.count
  · simp [stepResult, hb, hcard, Outcome.add, Outcome.pure]
  · by_cases hm : y ∈ s.points
    · have hseen := (member_value y s.points).mpr hm
      have hmem : y ∈ s.points.toFinset := List.mem_toFinset.mpr hm
      simp [stepResult, hb, hcard, hseen, Outcome.add, Outcome.combine, Outcome.pure,
        Finset.insert_eq_of_mem hmem]
    · have hseen : (memberResult y s.points).value = false := by
        simp [member_value_eq, hm]
      have hxy : x ≠ y := by
        intro he
        subst y
        exact hm (List.mem_toFinset.mp hxf)
      have hxt := Finset.mem_filter.mp hx
      have hadj : (retainedGraph w b key T a).Adj x y ↔
          w (Sym2.mk x y) < a ∧ b (key y) = true := by
        simp [retainedGraph, TerminalMST.below_adj, retained, hxy, hxt.1, hxt.2,
          hy, and_comm]
      have hr := (Cache.resolved_correct b (key y) s.cache hs.cache_correct).1
      by_cases hd : w (Sym2.mk x y) < a <;> cases hv : b (key y) <;>
        simp [stepResult, hb, hcard, hseen, hadj, hd, hr, hv, Memory.remember,
          Outcome.add, Outcome.combine, Outcome.pure]

noncomputable def scanProgram (key : V → Q) (a : ℝ) (B : ℕ) (x : V)
    (l : List V) (s : Memory V Q) : Code (Sym2 V) Q (Memory V Q) :=
  Code.foldList (stepProgram key a B x) l s

noncomputable def scanResult (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) : Outcome (Memory V Q) :=
  Code.folded (stepResult w b key a B x) l s

theorem scan_evaluates (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) :
    Code.Evaluates w b (scanProgram key a B x l s) (scanResult w b key a B x l s) :=
  Code.foldList_evaluates w b _ _ (step_evaluates w b key a B x) l s

theorem scan_valid (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) (hs : Memory.Valid b s) :
    Memory.Valid b (scanResult w b key a B x l s).value := by
  induction l generalizing s with
  | nil => exact hs
  | cons y l ih => exact ih _ (step_valid w b key a B x s y hs)

theorem scan_count (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) (hs : s.count ≤ B + 1) :
    (scanResult w b key a B x l s).value.count ≤ B + 1 := by
  induction l generalizing s with
  | nil => exact hs
  | cons y l ih => exact ih _ (step_size w b key a B x s y hs)

theorem scan_processed (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) :
    (scanResult w b key a B x l s).value.processed = s.processed := by
  induction l generalizing s with
  | nil => rfl
  | cons y l ih =>
      exact (ih (stepResult w b key a B x s y).value).trans
        (step_processed w b key a B x s y)

theorem scan_work (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q)
    (hs : Memory.Valid b s) (hsize : s.count ≤ B + 1) :
    (scanResult w b key a B x l s).work ≤ (2 * (B + 1) + 13) * l.length := by
  induction l generalizing s with
  | nil => simp [scanResult, Code.folded, Outcome.pure]
  | cons y l ih =>
      have ht := step_work w b key a B x s y
      have hlen : s.points.length ≤ B + 1 := hs.count_eq ▸ hsize
      have hv := step_valid w b key a B x s y hs
      have hz := step_size w b key a B x s y hsize
      have hr := ih _ hv hz
      dsimp only [scanResult] at hr
      simp only [scanResult, Code.folded, Outcome.add, Outcome.combine, List.length_cons]
      nlinarith

theorem scan_metric_queries (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) :
    (scanResult w b key a B x l s).metricQueries ≤ l.length := by
  simpa only [Nat.one_mul, scanResult] using
    Code.folded_metric_queries (stepResult w b key a B x) 1
      (step_metric_queries w b key a B x) l s

theorem scan_positive_potential (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q) :
    (scanResult w b key a B x l s).positiveReplies + s.count ≤
      (scanResult w b key a B x l s).value.count :=
  Code.folded_positive_potential (stepResult w b key a B x) Memory.count
    (step_positive_potential w b key a B x) l s

theorem scan_of_overflow (B : ℕ) (G : SimpleGraph V) (x : V) (l : List V)
    (found : Finset V) (h : B < found.card) : scan B G x l found = found := by
  cases l <;> simp only [scan, h, ite_true]

theorem scan_projects (w : Sym2 V → ℝ) (b : Q → Bool) (key : V → Q)
    (T : Finset V) (a : ℝ) (B : ℕ) (x : V) (l : List V) (s : Memory V Q)
    (hs : Memory.Valid b s) (hx : x ∈ retained b key T)
    (hxf : x ∈ s.points.toFinset) (hl : ∀ y ∈ l, y ∈ T) :
    (scanResult w b key a B x l s).value.graphState =
      ⟨scan B (retainedGraph w b key T a) x l s.points.toFinset,
        s.processed.toFinset⟩ := by
  induction l generalizing s with
  | nil => rfl
  | cons y l ih =>
      let n := (stepResult w b key a B x s y).value
      have hn := step_valid w b key a B x s y hs
      have hnx : x ∈ n.points.toFinset := step_points_mono w b key a B x s y hxf
      have hih := ih n hn hnx (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      change (scanResult w b key a B x l n).value.graphState = _
      rw [hih, step_found w b key T a B x s y hs hx (hl y List.mem_cons_self) hxf,
        step_processed]
      by_cases hb : B < s.points.toFinset.card
      · simp only [hb, ite_true, scan, scan_of_overflow B _ x l _ hb]
      · simp only [hb, ite_false, scan]

end SteinerUpperBound.ComponentExplore

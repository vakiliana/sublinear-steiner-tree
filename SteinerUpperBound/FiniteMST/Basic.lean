module

public import SteinerUpperBound.SmallCoverProgram.Closure
public import SteinerUpperBound.SortedForest

@[expose] public section

namespace SteinerUpperBound.FiniteMST

open QueryProgram SmallCoverProgram
open scoped Classical

variable {m : ℕ}

abbrev Matrix (m : ℕ) := Closure.Dense ℝ m
abbrev Edge (m : ℕ) := Fin (m * m)

def ends (e : Edge m) : Fin m × Fin m := finProdFinEquiv.symm e

abbrev valid (e : Edge m) : Prop := (ends e).1 < (ends e).2

def sym (e : Edge m) : Sym2 (Fin m) := Sym2.mk (ends e).1 (ends e).2

def edgeWeight (d : Matrix m) (e : Edge m) : ℝ := Closure.entry d (ends e).1 (ends e).2

def pairWeight (d : Matrix m) (x y : Fin m) : ℝ :=
  if x ≤ y then Closure.entry d x y else Closure.entry d y x

theorem pairWeight_symm (d : Matrix m) (x y : Fin m) : pairWeight d x y = pairWeight d y x := by
  by_cases hxy : x ≤ y <;> by_cases hyx : y ≤ x
  · have he := le_antisymm hxy hyx
    subst y
    rfl
  · simp only [pairWeight, hxy, hyx, ↓reduceIte]
  · simp only [pairWeight, hxy, hyx, ↓reduceIte]
  · exact (hxy (le_of_not_ge hyx)).elim

def weight (d : Matrix m) : Sym2 (Fin m) → ℝ :=
  Sym2.lift ⟨pairWeight d, pairWeight_symm d⟩

@[simp] theorem weight_mk (d : Matrix m) (x y : Fin m) :
    weight d (Sym2.mk x y) = pairWeight d x y := by
  rw [weight, Sym2.lift_mk]

theorem weight_sym_valid (d : Matrix m) (e : Edge m) (he : valid e) :
    weight d (sym e) = edgeWeight d e := by
  simp only [sym, weight_mk, pairWeight, le_of_lt he, ↓reduceIte, edgeWeight]

theorem weight_nonneg (d : Matrix m) (hd : ∀ i j, 0 ≤ Closure.entry d i j) :
    ∀ e, 0 ≤ weight d e := by
  intro e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [weight_mk]
      unfold pairWeight
      split_ifs <;> exact hd _ _

theorem weight_eq (d : Matrix m) (w : Sym2 (Fin m) → ℝ)
    (hd : ∀ i j, Closure.entry d i j = w (Sym2.mk i j)) : weight d = w := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [weight_mk]
      unfold pairWeight
      split_ifs
      · exact hd _ _
      · simpa only [Sym2.eq_swap] using hd y x

def baseCandidates (m : ℕ) : List (Edge m) :=
  ((List.finRange (m * m)).filter (fun e => decide (valid e))).reverse

theorem mem_baseCandidates (e : Edge m) : e ∈ baseCandidates m ↔ valid e := by
  simp [baseCandidates]

theorem baseCandidates_nodup (m : ℕ) : (baseCandidates m).Nodup := by
  have hh : ((List.finRange (m * m)).filter (fun e => decide (valid e))).Nodup :=
    (List.nodup_finRange _).filter _
  simpa only [baseCandidates, List.nodup_reverse] using hh

theorem baseCandidates_length (m : ℕ) : (baseCandidates m).length ≤ m * m := by
  simpa only [baseCandidates, List.length_reverse, List.length_finRange] using
    List.length_filter_le (fun e : Edge m => decide (valid e)) (List.finRange (m * m))

theorem sym_injOn_valid {e f : Edge m} (he : valid e) (hf : valid f) (h : sym e = sym f) : e = f := by
  rcases Sym2.eq_iff.mp h with h | h
  · exact finProdFinEquiv.symm.injective (Prod.ext h.1 h.2)
  · have ha : (ends e).1 < (ends e).2 := he
    have hb : (ends f).1 < (ends f).2 := hf
    rw [h.1, h.2] at ha
    exact (lt_asymm ha hb).elim

theorem sym_list_nodup (l : List (Edge m)) (hn : l.Nodup) (hv : ∀ e ∈ l, valid e) :
    (l.map sym).Nodup := by
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp_of_mem
    (fun he hf hne h => hne (sym_injOn_valid (hv _ he) (hv _ hf) h)) hn

noncomputable def spanningGraph {V : Type*} (l : List (Sym2 V)) : SimpleGraph V :=
  GraphRank.ofEdges l.toFinset

theorem candidates_span (l : List (Edge m)) (hp : l.Perm (baseCandidates m)) :
    spanningGraph (l.map sym) = Network.completeOn (Finset.univ : Finset (Fin m)) := by
  ext x y
  simp only [spanningGraph, GraphRank.ofEdges, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    List.mem_toFinset, Network.completeOn_adj, Finset.mem_univ, and_true]
  constructor
  · exact And.right
  · intro hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · let e : Edge m := finProdFinEquiv (x, y)
      have he : valid e := by simpa only [valid, ends, e, Equiv.symm_apply_apply] using hlt
      have hel : e ∈ l := hp.mem_iff.mpr ((mem_baseCandidates e).mpr he)
      exact ⟨List.mem_map.mpr ⟨e, hel, by simp only [sym, ends, e, Equiv.symm_apply_apply]⟩, hxy⟩
    · let e : Edge m := finProdFinEquiv (y, x)
      have he : valid e := by simpa only [valid, ends, e, Equiv.symm_apply_apply] using hgt
      have hel : e ∈ l := hp.mem_iff.mpr ((mem_baseCandidates e).mpr he)
      exact ⟨List.mem_map.mpr ⟨e, hel, by simp only [sym, ends, e, Equiv.symm_apply_apply, Sym2.eq_swap]⟩,
        hxy⟩

def generateStep (l : List (Edge m)) (e : Edge m) : List (Edge m) :=
  if valid e then e :: l else l

def candidates {M Q : Type*} (m : ℕ) : Code M Q (List (Edge m)) :=
  Code.foldList (fun l e => .tick 7 (.pure (generateStep l e))) (List.finRange (m * m)) []

def candidatesRun (m : ℕ) : Outcome (List (Edge m)) :=
  Code.folded (fun l e => ⟨generateStep l e, 8, 0, 0, 0⟩) (List.finRange (m * m)) []

theorem generateFold (l : List (Edge m)) (init : List (Edge m)) :
    l.foldl generateStep init = (l.filter (fun e => decide (valid e))).reverse ++ init := by
  induction l generalizing init with
  | nil => rfl
  | cons e l ih =>
      by_cases he : valid e <;>
        simp [List.foldl_cons, generateStep, he, ih, List.reverse_cons, List.append_assoc]

theorem candidatesRun_value (m : ℕ) : (candidatesRun m).value = baseCandidates m := by
  rw [candidatesRun, folded_value]
  change (List.finRange (m * m)).foldl generateStep [] = _
  rw [generateFold]
  simp only [List.append_nil, baseCandidates]

theorem candidates_evaluates {M Q : Type*} (oracle : M → ℝ) (bits : Q → Bool) (m : ℕ) :
    Code.Evaluates oracle bits (candidates m) (candidatesRun m) := by
  apply Code.foldList_evaluates
  intro l e
  exact Code.Evaluates.tick _ _ _ _ (Code.evaluates_pure _ _ _) 7

theorem candidatesRun_work (m : ℕ) : (candidatesRun m).work ≤ 9 * (m * m) := by
  simpa [candidatesRun] using Code.folded_work
    (fun l e => (⟨generateStep l e, 8, 0, 0, 0⟩ : Outcome (List (Edge m))))
    8 (fun _ _ => le_rfl) (List.finRange (m * m)) []

theorem candidatesRun_resources (m : ℕ) :
    (candidatesRun m).metricQueries = 0 ∧ (candidatesRun m).retentionQueries = 0 ∧
      (candidatesRun m).positiveReplies = 0 := by
  let step := fun l e => (⟨generateStep l e, 8, 0, 0, 0⟩ : Outcome (List (Edge m)))
  have hm := Code.folded_metric_queries step 0 (fun _ _ => le_rfl) (List.finRange (m * m)) []
  have hr := folded_retention_zero step (fun _ _ => rfl) (List.finRange (m * m)) []
  have hp := folded_positive_zero step (fun _ _ => rfl) (List.finRange (m * m)) []
  simpa only [candidatesRun] using
    (And.intro (by simpa only [Nat.zero_mul, Nat.le_zero] using hm) (And.intro hr hp))

end SteinerUpperBound.FiniteMST

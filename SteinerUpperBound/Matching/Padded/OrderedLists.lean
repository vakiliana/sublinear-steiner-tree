module

public import SteinerUpperBound.Matching.Padded.IteratorCorrect

@[expose] public section

namespace SteinerUpperBound.Matching.Padded

open scoped Classical

theorem threshold_takeWhile {A : Type*} (xs : List A) (rank : A → ℕ) (a : ℕ)
    (hs : xs.Pairwise (fun x y => rank x ≤ rank y)) :
    xs.takeWhile (fun x => rank x < a) = xs.filter (fun x => rank x < a) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : rank x < a
    · simpa [hx] using congrArg (List.cons x) (ih hs.of_cons)
    · have hnone : ∀ y ∈ xs, ¬ rank y < a := by
        intro y hy
        have hh := List.rel_of_pairwise_cons hs hy
        omega
      have hf : xs.filter (fun y => rank y < a) = [] :=
        List.filter_eq_nil_iff.mpr (by simpa only [decide_eq_true_eq] using hnone)
      simp [hx, hf]

theorem drop_after_lookup {A : Type*} (xs : List A) (cursor : ℕ) (a : A)
    (h : xs[cursor]? = some a) : xs.drop cursor = a :: xs.drop (cursor + 1) := by
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp h
  simpa only [he] using List.drop_eq_getElem_cons hl

theorem drop_after_exhaustion {A : Type*} (xs : List A) (cursor : ℕ)
    (h : xs[cursor]? = none) : xs.drop cursor = [] :=
  List.drop_eq_nil_of_le (List.getElem?_eq_none_iff.mp h)

variable {V E : Type*} {G : Graph V E} (Q : ℕ) [Fintype E]

theorem candidates_length_le (ρ : Rank E) (v : V) :
    (G.candidates ρ (Fintype.card E) v).length ≤ Fintype.card E :=
  (G.candidates_nodup ρ (Fintype.card E) v).length_le_card

theorem candidates_numeric_prefix (ranks : E → Fin Q) (hn : Function.Injective ranks)
    (v : V) (d : E) :
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).takeWhile
        (fun e => (ranks e).val < (ranks d).val) =
      G.candidates (UniformOrder.order ranks) ((UniformOrder.order ranks).index d) v := by
  classical
  let ρ := UniformOrder.order ranks
  rw [threshold_takeWhile _ _ _ (Cache.incident_rank_ordered Q ranks hn v)]
  let : Std.Antisymm (fun e f : E => ρ.index e < ρ.index f) :=
    ⟨fun _ _ h h' => (lt_asymm h h').elim⟩
  let : Std.Irrefl (fun e f : E => ρ.index e < ρ.index f) := ⟨fun _ => lt_irrefl _⟩
  apply List.Pairwise.eq_of_mem_iff
    ((G.candidates_pairwise ρ (Fintype.card E) v).filter _) (G.candidates_pairwise ρ _ v)
  intro e
  simp only [List.mem_filter, G.mem_candidates, decide_eq_true_eq]
  have hr : (ranks e).val < (ranks d).val ↔ ρ.index e < ρ.index d :=
    (UniformOrder.order_lt ranks hn e d).symm
  constructor
  · rintro ⟨⟨_, hi⟩, h⟩
    exact ⟨hr.mp h, hi⟩
  · rintro ⟨h, hi⟩
    exact ⟨⟨ρ.index_lt e, hi⟩, hr.mpr h⟩

theorem candidates_full_numeric (ranks : E → Fin Q) (v : V) :
    (G.candidates (UniformOrder.order ranks) (Fintype.card E) v).takeWhile
      (fun e => (ranks e).val < Q) =
        G.candidates (UniformOrder.order ranks) (Fintype.card E) v := by
  generalize G.candidates (UniformOrder.order ranks) (Fintype.card E) v = xs
  induction xs with
  | nil => rfl
  | cons e xs ih => simpa [(ranks e).isLt] using congrArg (List.cons e) ih

end SteinerUpperBound.Matching.Padded

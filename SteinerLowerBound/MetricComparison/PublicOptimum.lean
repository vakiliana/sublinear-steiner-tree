module

public import SteinerLowerBound.MetricComparison.Padding

@[expose] public section

/-!
# The actual shuffled public Steiner optimum

Feasible public trees contain every public terminal label and an arbitrary
selected subset of the publicly named centers. Their weights are obtained by
querying the actual shuffled public metric, not by defining their costs to be
canonical costs. A bijective relabeling of vertices transports feasible trees
and preserves these costs. Consequently their finite minimum is exactly
`Steiner.optimum`.
-/

namespace SteinerLowerBound.MetricComparison

open scoped BigOperators Classical

section Relabel

variable {V W : Type*}

noncomputable def treeRelabelEquiv (e : V ≃ W) :
    {T : SimpleGraph V // T.IsTree} ≃ {T : SimpleGraph W // T.IsTree} where
  toFun T := ⟨T.val.map e, (SimpleGraph.Iso.map e T.val).isTree_iff.mp T.property⟩
  invFun T := ⟨T.val.map e.symm, (SimpleGraph.Iso.map e.symm T.val).isTree_iff.mp T.property⟩
  left_inv T := by
    apply Subtype.ext
    change (T.val.map e).map e.symm = T.val
    rw [SimpleGraph.map_map]
    have he : e.symm ∘ e = id := funext e.symm_apply_apply
    rw [he, SimpleGraph.map_id]
  right_inv T := by
    apply Subtype.ext
    change (T.val.map e.symm).map e = T.val
    rw [SimpleGraph.map_map]
    have he : e ∘ e.symm = id := funext e.apply_symm_apply
    rw [he, SimpleGraph.map_id]

theorem cost_relabel [Fintype V] [Fintype W] (e : V ≃ W)
    (w : Sym2 W → ℝ) (T : SimpleGraph V) :
    GraphCost.cost w (T.map e) =
      GraphCost.cost (fun z => w (Sym2.map e z)) T := by
  classical
  letI : DecidableRel T.Adj := fun _ _ => Classical.propDecidable _
  letI : DecidableRel (T.map e).Adj := fun _ _ => Classical.propDecidable _
  have he : (T.map e).edgeFinset = T.edgeFinset.image (Sym2.map e) := by
    apply Finset.Subset.antisymm (Padding.edgeFinset_map_subset T e)
    intro z hz
    obtain ⟨q, hsource, rfl⟩ := Finset.mem_image.mp hz
    induction q using Sym2.inductionOn with
    | _ x y =>
      have ha := (SimpleGraph.mem_edgeSet T).mp (SimpleGraph.mem_edgeFinset.mp hsource)
      exact SimpleGraph.mem_edgeFinset.mpr ((SimpleGraph.mem_edgeSet (T.map e)).mpr
        (SimpleGraph.map_adj_apply' ha (e.injective.ne ha.ne)))
  unfold GraphCost.cost
  rw [he, Finset.sum_image]
  intro z _ z' _ hz
  exact e.toEmbedding.sym2Map.injective hz

end Relabel

namespace Public

open Screening (Terminal Reply)

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable def placeEquiv (π : Equiv.Perm (Terminal S G I)) :
    Points S G I C ≃ Point S G I C where
  toFun := place π
  invFun
    | .special s => .inl (π.symm (.inl s))
    | .ordinary g i => .inl (π.symm (.inr (g, i)))
    | .center c => .inr c
  left_inv x := by
    cases x with
    | inl t =>
      cases ht : π t with
      | inl s => simp only [place, ht]; rw [← ht, π.symm_apply_apply]
      | inr gi => simp only [place, ht]; rw [← ht, π.symm_apply_apply]
    | inr c => rfl
  right_inv x := by cases x <;> simp [place]

noncomputable def distance (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (x y : Points S G I C) : ℝ :=
  Point.distance ell (fun c => (nb c : Set S)) (place π x) (place π y)

theorem distance_eq_query (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (x y : Points S G I C) :
    distance π ell nb x y = replyValue ell (staticAnswer π nb (Sym2.mk x y)) :=
  (staticAnswer_metric π nb ell x y).symm

@[instance_reducible]
noncomputable def metricSpace (π : Equiv.Perm (Terminal S G I))
    {ell : ℝ} (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S) :
    MetricSpace (Points S G I C) :=
  MetricSpace.induced (placeEquiv π) (placeEquiv π).injective
    (Point.metricSpace hEll₀ hEll₂ (fun c => (nb c : Set S)))

theorem metricSpace_dist (π : Equiv.Perm (Terminal S G I))
    {ell : ℝ} (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S)
    (x y : Points S G I C) :
    @dist _ (metricSpace π hEll₀ hEll₂ nb).toDist x y = distance π ell nb x y := rfl

noncomputable def edgeWeight (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (q : Queries S G I C) : ℝ :=
  replyValue ell (staticAnswer π nb q)

theorem edgeWeight_canonical (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (q : Queries S G I C) :
    edgeWeight π ell nb q =
      HardCost.edgeWeight ell (fun c => (nb c : Set S)) (Sym2.map (placeEquiv π) q) := by
  induction q using Sym2.inductionOn with
  | _ x y => exact staticAnswer_metric π nb ell x y

def selectedInclusion (X : Finset C) :
    Points S G I {c // c ∈ X} → Points S G I C
  | .inl t => .inl t
  | .inr c => .inr c.val

noncomputable def selectedWeight (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (X : Finset C) (q : Queries S G I {c // c ∈ X}) : ℝ :=
  edgeWeight π ell nb (Sym2.map (selectedInclusion X) q)

theorem selected_place (π : Equiv.Perm (Terminal S G I)) (X : Finset C)
    (x : Points S G I {c // c ∈ X}) :
    place π (selectedInclusion X x) = Padding.pointMap Subtype.val (place π x) := by
  cases x with
  | inl t => cases ht : π t <;> simp only [selectedInclusion, place, ht, Padding.pointMap]
  | inr c => rfl

theorem selectedWeight_canonical (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (X : Finset C) (q : Queries S G I {c // c ∈ X}) :
    selectedWeight π ell nb X q =
      HardCost.edgeWeight ell (fun c : {c // c ∈ X} => (nb c.val : Set S))
        (Sym2.map (placeEquiv π) q) := by
  induction q using Sym2.inductionOn with
  | _ x y =>
    rw [selectedWeight, edgeWeight_canonical]
    simp only [Sym2.map_mk, HardCost.edgeWeight_mk]
    change Point.distance ell (fun c => (nb c : Set S))
      (place π (selectedInclusion X x)) (place π (selectedInclusion X y)) = _
    rw [selected_place, selected_place]
    exact Padding.distance_pointMap ell (fun c : {c // c ∈ X} => nb c.val) nb
      Subtype.val Subtype.val_injective (fun _ => rfl) _ _

abbrev Solution (S G I C : Type*) :=
  Σ X : Finset C, {T : SimpleGraph (Points S G I {c // c ∈ X}) // T.IsTree}

variable [Fintype C]

noncomputable instance : Fintype (Solution S G I C) := by
  classical
  infer_instance

noncomputable def solutionEquiv (π : Equiv.Perm (Terminal S G I)) :
    Solution S G I C ≃ Steiner.Solution S G I C :=
  Equiv.sigmaCongrRight (fun _ => treeRelabelEquiv (placeEquiv π))

noncomputable def solutionCost (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (t : Solution S G I C) : ℝ :=
  GraphCost.cost (selectedWeight π ell nb t.1) t.2.val

theorem solutionCost_relabel (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (t : Solution S G I C) :
    solutionCost π ell nb t = Steiner.solutionCost ell nb (solutionEquiv π t) := by
  change GraphCost.cost (selectedWeight π ell nb t.1) t.2.val =
    GraphCost.cost
      (HardCost.edgeWeight ell (fun c : {c // c ∈ t.1} => (nb c.val : Set S)))
      (t.2.val.map (placeEquiv π))
  rw [cost_relabel]
  congr 1
  funext q
  exact selectedWeight_canonical π ell nb t.1 q

variable [Nonempty G] [Nonempty I]

theorem solution_nonempty : Nonempty (Solution S G I C) :=
  (Steiner.solution_nonempty (S := S) (G := G) (I := I) (C := C)).map
    (solutionEquiv (Equiv.refl (Terminal S G I))).symm

noncomputable def optimum (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) : ℝ :=
  (Finset.univ.image (solutionCost (G := G) (I := I) π ell nb)).min' (by
    obtain ⟨t⟩ := solution_nonempty (S := S) (G := G) (I := I) (C := C)
    exact ⟨solutionCost π ell nb t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩)

theorem optimum_le (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) (t : Solution S G I C) :
    optimum π ell nb ≤ solutionCost π ell nb t :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)

theorem optimum_attained (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) :
    ∃ t : Solution S G I C, solutionCost π ell nb t = optimum π ell nb := by
  have hh := Finset.min'_mem (Finset.univ.image (solutionCost (G := G) (I := I) π ell nb))
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hh _)
  exact ⟨t, ht⟩

theorem public_optimum_eq (π : Equiv.Perm (Terminal S G I)) (ell : ℝ)
    (nb : C → Finset S) :
    optimum π ell nb = Steiner.optimum (G := G) (I := I) ell nb := by
  apply le_antisymm
  · obtain ⟨t, ht⟩ := Steiner.optimum_attained (G := G) (I := I) ell nb
    have hh := optimum_le π ell nb ((solutionEquiv π).symm t)
    rw [solutionCost_relabel, Equiv.apply_symm_apply, ht] at hh
    exact hh
  · obtain ⟨t, ht⟩ := optimum_attained π ell nb
    have hh := Steiner.optimum_le ell nb (solutionEquiv π t)
    rw [← solutionCost_relabel, ht] at hh
    exact hh

theorem public_optimum_padding {P : Type*} [Fintype P]
    (π : Equiv.Perm (Terminal S G I)) {ell : ℝ}
    (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S) :
    optimum π ell (Padding.extend (P := P) nb) = optimum π ell nb := by
  rw [public_optimum_eq, public_optimum_eq, Padding.optimum_padding hEll₀ hEll₂]

end Public

namespace Public

open Screening (Terminal)

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I] [Fintype C]

theorem point_count :
    Fintype.card (Points S G I C) =
      Fintype.card S + Fintype.card G * Fintype.card I + Fintype.card C := by
  simp [Points, Terminal, Fintype.card_sum, Fintype.card_prod, Nat.add_assoc]

noncomputable def terminalLabels : Finset (Points S G I C) :=
  Finset.univ.map Function.Embedding.inl

theorem terminal_count :
    (terminalLabels (S := S) (G := G) (I := I) (C := C)).card =
      Fintype.card S + Fintype.card G * Fintype.card I := by
  simp [terminalLabels, Terminal, Fintype.card_sum, Fintype.card_prod]

theorem point_count_padding {P : Type*} [Fintype P] :
    Fintype.card (Points S G I (C ⊕ P)) =
      Fintype.card (Points S G I C) + Fintype.card P :=
  Padding.cardinality

theorem terminal_count_padding {P : Type*} [Fintype P] :
    (terminalLabels (S := S) (G := G) (I := I) (C := C ⊕ P)).card =
      (terminalLabels (S := S) (G := G) (I := I) (C := C)).card := by
  rw [terminal_count, terminal_count]

theorem terminalLabels_correct (π : Equiv.Perm (Terminal S G I)) (x : Points S G I C) :
    x ∈ terminalLabels ↔ Point.terminals (place π x) := by
  classical
  cases x with
  | inl t => cases ht : π t <;> simp [terminalLabels, place, ht, Point.terminals]
  | inr c => simp [terminalLabels, place, Point.terminals]

theorem distance_padding_embed {P : Type*} (π : Equiv.Perm (Terminal S G I))
    (ell : ℝ) (nb : C → Finset S) (x y : Points S G I C) :
    distance π ell (Padding.extend (P := P) nb)
        (Padding.embedPoint x) (Padding.embedPoint y) = distance π ell nb x y := by
  rw [distance_eq_query, distance_eq_query]
  exact congrArg (replyValue ell)
    (Padding.staticAnswer_embed π nb (Sym2.mk x y))

theorem distance_padding_far {P : Type*} (π : Equiv.Perm (Terminal S G I))
    (ell : ℝ) (nb : C → Finset S) (p : P) (y : Points S G I (C ⊕ P))
    (hne : Sum.inr (Sum.inr p) ≠ y) :
    distance π ell (Padding.extend nb) (.inr (.inr p)) y = 2 := by
  rw [distance_eq_query, Padding.staticAnswer_padding, if_neg hne]
  rfl

theorem metricSpace_padding_embed {P : Type*} (π : Equiv.Perm (Terminal S G I))
    {ell : ℝ} (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S)
    (x y : Points S G I C) :
    @dist _ (metricSpace π hEll₀ hEll₂ (Padding.extend (P := P) nb)).toDist
      (Padding.embedPoint x) (Padding.embedPoint y) =
        @dist _ (metricSpace π hEll₀ hEll₂ nb).toDist x y := by
  rw [metricSpace_dist, metricSpace_dist, distance_padding_embed]

end Public

end SteinerLowerBound.MetricComparison

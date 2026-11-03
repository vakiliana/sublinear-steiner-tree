module

public import SteinerLowerBound.MetricComparison.Padding.Contraction

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Padding

open scoped BigOperators Classical

variable {S G I C D P : Type*}

def pointMap (f : C → D) : Point S G I C → Point S G I D
  | .special s => .special s
  | .ordinary g i => .ordinary g i
  | .center c => .center (f c)

theorem pointMap_surjective (f : C → D) (hf : Function.Surjective f) :
    Function.Surjective (pointMap (S := S) (G := G) (I := I) f) := by
  intro x
  cases x with
  | special s => exact ⟨.special s, rfl⟩
  | ordinary g i => exact ⟨.ordinary g i, rfl⟩
  | center d =>
    obtain ⟨c, rfl⟩ := hf d
    exact ⟨.center c, rfl⟩

theorem distance_pointMap (ell : ℝ) (nb : C → Finset S) (nb' : D → Finset S)
    (f : C → D) (hf : Function.Injective f) (hn : ∀ c, nb' (f c) = nb c)
    (x y : Point S G I C) :
    Point.distance ell (fun d => (nb' d : Set S)) (pointMap f x) (pointMap f y) =
      Point.distance ell (fun c => (nb c : Set S)) x y := by
  classical
  cases x <;> cases y <;>
    simp [pointMap, Point.distance, Point.sameCluster, Point.unitAdjacent, hf.eq_iff, hn]

variable [Fintype S] [Fintype G] [Fintype I] [Fintype C] [Fintype D]

noncomputable def selectedEquiv (f : C ↪ D) (X : Finset C) :
    {c // c ∈ X} ≃ {d // d ∈ X.map f} :=
  Equiv.ofBijective (fun c => ⟨f c.val, Finset.mem_map.mpr ⟨c.val, c.property, rfl⟩⟩)
    ⟨fun _ _ he => Subtype.ext (f.injective (congrArg Subtype.val he)), by
      intro d
      obtain ⟨c, hc, he⟩ := Finset.mem_map.mp d.property
      exact ⟨⟨c, hc⟩, Subtype.ext he⟩⟩

theorem optimum_embedding [Nonempty G] [Nonempty I] {ell : ℝ} (hEll : 0 ≤ ell)
    (nb : C → Finset S) (nb' : D → Finset S)
    (f : C ↪ D) (hn : ∀ c, nb' (f c) = nb c) :
    Steiner.optimum (G := G) (I := I) ell nb' ≤
      Steiner.optimum (G := G) (I := I) ell nb := by
  classical
  obtain ⟨t, ht⟩ := Steiner.optimum_attained (G := G) (I := I) ell nb
  let e := selectedEquiv f t.1
  let F := pointMap (S := S) (G := G) (I := I) e
  have hfn : ∀ c : {c // c ∈ t.1}, nb' (e c).val = nb c.val := by
    intro c
    change nb' (f c.val) = nb c.val
    exact hn c.val
  obtain ⟨T, hT, hcost⟩ := exists_tree_cost_le t.2.val t.2.property.connected F
    (pointMap_surjective e e.surjective)
    (HardCost.edgeWeight ell (fun c => (nb c.val : Set S)))
    (HardCost.edgeWeight ell (fun d => (nb' d.val : Set S)))
    (fun z => by
      induction z using Sym2.inductionOn with
      | _ x y => exact Point.distance_nonneg hEll _ x y)
    (fun z _ => by
      induction z using Sym2.inductionOn with
      | _ x y =>
        exact (distance_pointMap ell (fun c => nb c.val) (fun d => nb' d.val)
          e e.injective hfn x y).le)
  have hh := Steiner.optimum_le ell nb'
    (⟨t.1.map f, T, hT⟩ : Steiner.Solution S G I D)
  apply hh.trans
  rw [← ht]
  exact hcost

def extend (nb : C → Finset S) : C ⊕ P → Finset S
  | .inl c => nb c
  | .inr _ => ∅

variable [Fintype P]

noncomputable def kept (X : Finset (C ⊕ P)) : Finset C :=
  Finset.univ.filter (fun c => Sum.inl c ∈ X)

@[simp]
theorem mem_kept (X : Finset (C ⊕ P)) (c : C) : c ∈ kept X ↔ Sum.inl c ∈ X := by
  simp [kept]

noncomputable def keptCenter (X : Finset (C ⊕ P)) :
    {c // c ∈ kept X} ↪ {a // a ∈ X} where
  toFun c := ⟨.inl c.val, (mem_kept X c.val).mp c.property⟩
  inj' _ _ he := Subtype.ext (Sum.inl_injective (congrArg Subtype.val he))

noncomputable def collapse (X : Finset (C ⊕ P)) (g : G) (i : I) :
    Point S G I {a // a ∈ X} → Point S G I {c // c ∈ kept X}
  | .special s => .special s
  | .ordinary a j => .ordinary a j
  | .center ⟨.inl c, hc⟩ => .center ⟨c, (mem_kept X c).mpr hc⟩
  | .center ⟨.inr _, _⟩ => .ordinary g i

@[simp]
theorem collapse_kept (X : Finset (C ⊕ P)) (g : G) (i : I)
    (x : Point S G I {c // c ∈ kept X}) :
    collapse X g i (pointMap (keptCenter X) x) = x := by
  cases x <;> rfl

theorem collapse_surjective (X : Finset (C ⊕ P)) (g : G) (i : I) :
    Function.Surjective (collapse (S := S) X g i) :=
  fun x => ⟨pointMap (keptCenter X) x, collapse_kept X g i x⟩

theorem vertex_cases (X : Finset (C ⊕ P)) (x : Point S G I {a // a ∈ X}) :
    (∃ y, pointMap (keptCenter X) y = x) ∨
      ∃ p : P, ∃ hp : Sum.inr p ∈ X, x = .center ⟨Sum.inr p, hp⟩ := by
  cases x with
  | special s => exact Or.inl ⟨.special s, rfl⟩
  | ordinary g i => exact Or.inl ⟨.ordinary g i, rfl⟩
  | center a =>
    rcases a with ⟨a, ha⟩
    cases a with
    | inl c => exact Or.inl ⟨.center ⟨c, (mem_kept X c).mpr ha⟩, rfl⟩
    | inr p => exact Or.inr ⟨p, ha, rfl⟩

theorem distance_kept (ell : ℝ) (nb : C → Finset S) (X : Finset (C ⊕ P))
    (x y : Point S G I {c // c ∈ kept X}) :
    Point.distance ell (fun a => (extend nb a.val : Set S))
        (pointMap (keptCenter X) x) (pointMap (keptCenter X) y) =
      Point.distance ell (fun c => (nb c.val : Set S)) x y :=
  distance_pointMap ell (fun c => nb c.val) (fun a => extend nb a.val)
    (keptCenter X) (keptCenter X).injective (fun _ => rfl) x y

theorem distance_padding (ell : ℝ) (nb : C → Finset S) (X : Finset (C ⊕ P))
    (p : P) (hp : Sum.inr p ∈ X) (y : Point S G I {a // a ∈ X})
    (hne : Point.center (S := S) (G := G) (I := I) ⟨Sum.inr p, hp⟩ ≠ y) :
    Point.distance ell (fun a => (extend nb a.val : Set S)) (.center ⟨Sum.inr p, hp⟩) y = 2 := by
  classical
  cases y <;> simp [Point.distance, hne, Point.sameCluster, Point.unitAdjacent, extend]

theorem collapse_distance_le {ell : ℝ} (hEll : ell ≤ 2) (nb : C → Finset S)
    (X : Finset (C ⊕ P)) (g : G) (i : I)
    (x y : Point S G I {a // a ∈ X}) (hne : x ≠ y) :
    Point.distance ell (fun c => (nb c.val : Set S)) (collapse X g i x) (collapse X g i y) ≤
      Point.distance ell (fun a => (extend nb a.val : Set S)) x y := by
  rcases vertex_cases X x with ⟨x, rfl⟩ | ⟨p, hp, rfl⟩
  · rcases vertex_cases X y with ⟨y, rfl⟩ | ⟨p, hp, rfl⟩
    · rw [collapse_kept, collapse_kept, distance_kept]
    · rw [Point.distance_comm ell _ (pointMap (keptCenter X) x),
        distance_padding ell nb X p hp _ hne.symm]
      exact Point.distance_le_two hEll _ _ _
  · rw [distance_padding ell nb X p hp y hne]
    exact Point.distance_le_two hEll _ _ _

theorem optimum_remove_padding [Nonempty G] [Nonempty I]
    {ell : ℝ} (hEll₀ : 0 ≤ ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S) :
    Steiner.optimum (G := G) (I := I) ell nb ≤
      Steiner.optimum (G := G) (I := I) ell (extend (P := P) nb) := by
  classical
  obtain ⟨t, ht⟩ := Steiner.optimum_attained (G := G) (I := I) ell (extend (P := P) nb)
  let g : G := Classical.arbitrary G
  let i : I := Classical.arbitrary I
  obtain ⟨T, hT, hcost⟩ := exists_tree_cost_le t.2.val t.2.property.connected
    (collapse (S := S) t.1 g i) (collapse_surjective t.1 g i)
    (HardCost.edgeWeight ell (fun a => (extend nb a.val : Set S)))
    (HardCost.edgeWeight ell (fun c => (nb c.val : Set S)))
    (fun z => by
      induction z using Sym2.inductionOn with
      | _ x y => exact Point.distance_nonneg hEll₀ _ x y)
    (fun z hz => by
      induction z using Sym2.inductionOn with
      | _ x y =>
        have hxy := (SimpleGraph.mem_edgeSet t.2.val).mp (SimpleGraph.mem_edgeFinset.mp hz)
        exact collapse_distance_le hEll₂ nb t.1 g i x y hxy.ne)
  have hh := Steiner.optimum_le ell nb
    (⟨kept t.1, T, hT⟩ : Steiner.Solution S G I C)
  apply hh.trans
  rw [← ht]
  exact hcost

theorem optimum_padding [Nonempty G] [Nonempty I]
    {ell : ℝ} (hEll₀ : 0 < ell) (hEll₂ : ell ≤ 2) (nb : C → Finset S) :
    Steiner.optimum (G := G) (I := I) ell (extend (P := P) nb) =
      Steiner.optimum (G := G) (I := I) ell nb := by
  apply le_antisymm
  · exact optimum_embedding hEll₀.le nb (extend nb) Function.Embedding.inl (fun _ => rfl)
  · exact optimum_remove_padding hEll₀.le hEll₂ nb

end SteinerLowerBound.MetricComparison.Padding

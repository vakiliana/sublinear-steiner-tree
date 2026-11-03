module

public import SteinerUpperBound.Structural.BatchPromotion
public import SteinerUpperBound.Structural.Stars

@[expose] public section

namespace SteinerUpperBound.Structural.Tree

open SteinerLowerBound
open scoped Classical BigOperators

variable {V : Type*} [Fintype V] {I : Instance V}

namespace Limb

variable {S : TreeGeometry.TreeSolution I} {v : ↥S.vertices}

noncomputable def cherrySet (L : Limb S v) : Finset (CherryData I) :=
  match L with
  | .direct _ _ _ _ => ∅
  | .cherry C => {C.data}

theorem mem_cherrySet (L : Limb S v) (D : CherryData I) :
    D ∈ L.cherrySet ↔ ∃ C : Cherry S v, L = Limb.cherry C ∧ D = C.data := by
  cases L with
  | direct x hv hx h =>
    constructor
    · simp [cherrySet]
    · rintro ⟨C, h, _⟩
      cases h
  | cherry C =>
    constructor
    · intro h
      exact ⟨C, rfl, Finset.mem_singleton.mp h⟩
    · rintro ⟨D', h, rfl⟩
      have he := Limb.cherry.inj h
      subst D'
      simp [cherrySet]

theorem ports_in_region (L : Limb S v) : L.ports ⊆ L.region := by
  cases L with
  | direct x hv hx h =>
    intro z hz
    have he := Finset.mem_singleton.mp hz
    subst z
    exact (Limb.direct x hv hx h).primary_mem_region
  | cherry C =>
    intro z hz
    rcases Finset.mem_insert.mp hz with he | hz
    · simpa only [he, primary] using (Limb.cherry C).primary_mem_region
    · have he := Finset.mem_singleton.mp hz
      simpa only [he, region, stem] using C.secondary_mem_region

theorem cherry_center_in_region (L : Limb S v) {D : CherryData I} (hD : D ∈ L.cherrySet) :
    D.center ∈ L.region := by
  obtain ⟨C, rfl, rfl⟩ := (mem_cherrySet L D).mp hD
  exact (mem_region S v C.center C.center).mpr (SimpleGraph.Reachable.refl _)

theorem cherry_attachment (L : Limb S v) {D : CherryData I} (hD : D ∈ L.cherrySet) :
    D.attachment = (v : V) := by
  obtain ⟨C, _, rfl⟩ := (mem_cherrySet L D).mp hD
  rfl

theorem cherry_ports_in_region (L : Limb S v) {D : CherryData I} (hD : D ∈ L.cherrySet) :
    D.primary ∈ L.region ∧ D.secondary ∈ L.region := by
  obtain ⟨C, rfl, rfl⟩ := (mem_cherrySet L D).mp hD
  exact ⟨(Limb.cherry C).primary_mem_region, C.secondary_mem_region⟩

end Limb

theorem terminal_not_cherry_centers (A : Finset (CherryData I)) {x : V}
    (hx : x ∈ I.terminals) : x ∉ A.image CherryData.center := by
  intro h
  obtain ⟨D, _, he⟩ := Finset.mem_image.mp h
  exact D.center_nonterminal (by simpa only [he] using hx)

namespace ShortStar

variable {S : TreeGeometry.TreeSolution I}

noncomputable def cherries (A : ShortStar S) : Finset (CherryData I) :=
  Finset.univ.biUnion (fun i => (A.limb i).cherrySet)

theorem mem_cherries (A : ShortStar S) (D : CherryData I) :
    D ∈ A.cherries ↔ ∃ i : Fin 3, D ∈ (A.limb i).cherrySet := by
  classical
  simp only [cherries, Finset.mem_biUnion, Finset.mem_univ, true_and]

theorem attachment_outside_all (A : ShortStar S) (i j : Fin 3) :
    (A.attachment i : V) ∉ (A.limb j).region := by
  by_cases h : i = j
  · subst i
    exact region_attachment_outside S (A.attachment j) (A.limb j).stem (A.limb j).stem_adj
  · exact A.outside i j h

theorem cherries_onTree (A : ShortStar S) : ∀ D ∈ A.cherries, D.OnTree S := by
  intro D hD
  obtain ⟨i, hi⟩ := (A.mem_cherries D).mp hD
  obtain ⟨C, _, rfl⟩ := ((A.limb i).mem_cherrySet D).mp hi
  exact C.data_onTree

theorem cherries_away (A : ShortStar S) :
    ∀ C ∈ A.cherries, ∀ D ∈ A.cherries, C.center ≠ D.attachment := by
  intro C hC D hD he
  obtain ⟨i, hi⟩ := (A.mem_cherries C).mp hC
  obtain ⟨j, hj⟩ := (A.mem_cherries D).mp hD
  have hmem := (A.limb i).cherry_center_in_region hi
  have hd := (A.limb j).cherry_attachment hj
  rw [he, hd] at hmem
  exact A.attachment_outside_all j i hmem

theorem cherrySets_disjoint (A : ShortStar S) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (A.limb i).cherrySet (A.limb j).cherrySet := by
  apply Finset.disjoint_left.mpr
  intro D hi hj
  exact Finset.disjoint_left.mp (A.disjoint i j hij)
    ((A.limb i).cherry_center_in_region hi) ((A.limb j).cherry_center_in_region hj)

theorem cherries_center_injective (A : ShortStar S) :
    Set.InjOn CherryData.center (A.cherries : Set (CherryData I)) := by
  intro C hC D hD he
  obtain ⟨i, hi⟩ := (A.mem_cherries C).mp hC
  obtain ⟨j, hj⟩ := (A.mem_cherries D).mp hD
  by_cases hij : i = j
  · subst j
    obtain ⟨Ci, hLi, hCi⟩ := ((A.limb i).mem_cherrySet C).mp hi
    obtain ⟨Di, hLj, hDi⟩ := ((A.limb i).mem_cherrySet D).mp hj
    have hCD : Ci = Di := Limb.cherry.inj (hLi.symm.trans hLj)
    rw [hCi, hDi, hCD]
  · have hc := (A.limb i).cherry_center_in_region hi
    rw [he] at hc
    exact False.elim (Finset.disjoint_left.mp (A.disjoint i j hij) hc
      ((A.limb j).cherry_center_in_region hj))

theorem attachment_not_centers (A : ShortStar S) (j : Fin 3) :
    (A.attachment j : V) ∉ A.cherries.image CherryData.center := by
  intro h
  obtain ⟨D, hD, he⟩ := Finset.mem_image.mp h
  obtain ⟨i, hi⟩ := (A.mem_cherries D).mp hD
  have hc := (A.limb i).cherry_center_in_region hi
  rw [he] at hc
  exact A.attachment_outside_all j i hc

theorem batch_exists (A : ShortStar S) : Nonempty (BatchPromoted S A.cherries) :=
  batch_promoted_exists S A.cherries A.cherries_onTree A.cherries_away A.cherries_center_injective

theorem delta_sum (A : ShortStar S) (w : Sym2 V → ℝ) :
    (∑ D ∈ A.cherries, D.delta w) =
      ∑ i : Fin 3, ∑ D ∈ (A.limb i).cherrySet, D.delta w := by
  apply Finset.sum_biUnion
  intro i hi j hj hij
  exact A.cherrySets_disjoint hij

theorem batch_direct_edges (A : ShortStar S) (R : BatchPromoted S A.cherries) (i : Fin 3) :
    R.solution.ambient.Adj (A.attachment i) (A.port i) := by
  have hi := A.limb i
  cases hL : A.limb i with
  | direct x hv hx h =>
    have hold : S.ambient.Adj (A.attachment i) x := (ambient_adj_iff S _ _).mpr h
    have hnew := R.survives _ _ (A.attachment_not_centers i)
      (terminal_not_cherry_centers A.cherries hx) hold
    simpa only [port, hL, Limb.primary] using hnew
  | cherry C =>
    have hD : C.data ∈ A.cherries :=
      (A.mem_cherries _).mpr ⟨i, by simp only [hL, Limb.cherrySet, Finset.mem_singleton]⟩
    simpa only [port, hL, Limb.primary] using R.new_stems C.data hD

end ShortStar

end SteinerUpperBound.Structural.Tree

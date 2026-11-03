module

public import SteinerLowerBound.MetricComparison.Padding.Optimum
public import SteinerLowerBound.MetricComparison.Padding.Reduction

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Padding

open scoped BigOperators Classical
open Screening (Terminal Reply)

variable {S G I C P : Type*}

def embedPoint : Public.Points S G I C → Public.Points S G I (C ⊕ P)
  | .inl t => .inl t
  | .inr c => .inr (.inl c)

def projectPoint : Public.Points S G I (C ⊕ P) → Option (Public.Points S G I C)
  | .inl t => some (.inl t)
  | .inr (.inl c) => some (.inr c)
  | .inr (.inr _) => none

@[simp]
theorem project_embed (x : Public.Points S G I C) :
    projectPoint (P := P) (embedPoint x) = some x := by cases x <;> rfl

theorem project_eq_some (x : Public.Points S G I (C ⊕ P)) (y : Public.Points S G I C) :
    projectPoint x = some y ↔ x = embedPoint y := by
  cases x with
  | inl t => cases y <;> simp [projectPoint, embedPoint]
  | inr c =>
    cases c <;> cases y <;> simp [projectPoint, embedPoint]

def embedQuery : Public.Queries S G I C → Public.Queries S G I (C ⊕ P) :=
  Sym2.map embedPoint

noncomputable def paddingPairShape (x y : Public.Points S G I (C ⊕ P)) :
    Reply ⊕ Public.Queries S G I C :=
  match projectPoint x, projectPoint y with
  | some x', some y' => .inr (Sym2.mk x' y')
  | _, _ => .inl (if x = y then .diagonal else .far)

theorem paddingPairShape_comm (x y : Public.Points S G I (C ⊕ P)) :
    paddingPairShape x y = paddingPairShape y x := by
  classical
  unfold paddingPairShape
  cases hx : projectPoint (C := C) x <;> cases hy : projectPoint (C := C) y
  · simp only [eq_comm]
  · simp only [eq_comm]
  · simp only [eq_comm]
  · exact congrArg Sum.inr Sym2.eq_swap

noncomputable def paddingShape :
    Public.Queries S G I (C ⊕ P) → Reply ⊕ Public.Queries S G I C :=
  Sym2.lift ⟨paddingPairShape, paddingPairShape_comm⟩

@[simp]
theorem paddingShape_mk (x y : Public.Points S G I (C ⊕ P)) :
    paddingShape (Sym2.mk x y) = paddingPairShape x y := by
  rw [paddingShape, Sym2.lift_mk]

theorem paddingShape_recover (q : Public.Queries S G I (C ⊕ P))
    (q' : Public.Queries S G I C) (hq : paddingShape q = .inr q') :
    q = embedQuery q' := by
  induction q using Sym2.inductionOn with
  | _ x y =>
    cases hx : projectPoint (C := C) x with
    | none => simp [paddingPairShape, hx] at hq
    | some x' =>
      cases hy : projectPoint (C := C) y with
      | none => simp [paddingPairShape, hx, hy] at hq
      | some y' =>
        simp only [paddingShape_mk, paddingPairShape, hx, hy, Sum.inr.injEq] at hq
        have hxx : x = embedPoint x' := (project_eq_some x x').mp hx
        have hyy : y = embedPoint y' := (project_eq_some y y').mp hy
        rw [← hq, embedQuery, Sym2.map_mk, hxx, hyy]

@[simp]
theorem paddingShape_embed (q : Public.Queries S G I C) :
    paddingShape (embedQuery (P := P) q) = .inr q := by
  induction q using Sym2.inductionOn with
  | _ x y => simp [embedQuery, paddingPairShape]

theorem paddingShape_padding (p : P) (y : Public.Points S G I (C ⊕ P)) :
    paddingShape (Sym2.mk (.inr (.inr p)) y) =
      .inl (if Sum.inr (Sum.inr p) = y then .diagonal else .far) := by
  simp [paddingPairShape, projectPoint]

noncomputable def queryReduction :
    Reduction (Public.Queries S G I (C ⊕ P)) (Public.Queries S G I C) Reply where
  shape := paddingShape
  embed := embedQuery
  recover := paddingShape_recover

@[simp]
theorem oracle_embed (o : Public.Queries S G I C → Reply) (q : Public.Queries S G I C) :
    queryReduction.oracle o (embedQuery (P := P) q) = o q := by
  change Sum.elim id o (paddingShape (embedQuery q)) = o q
  rw [paddingShape_embed]
  rfl

variable [Fintype S] [Fintype G] [Fintype I]

theorem staticAnswer_embed (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S)
    (q : Public.Queries S G I C) :
    Public.staticAnswer π (extend (P := P) nb) (embedQuery q) =
      Public.staticAnswer π nb q := by
  classical
  induction q using Sym2.inductionOn with
  | _ x y =>
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        simp [embedQuery, embedPoint, Public.staticAnswer,
          Compiler.Decoder.publicAnswer, Public.shape_mk, Public.pairShape]
      | inr c =>
        cases hu : π u <;>
          simp [embedQuery, embedPoint, Public.staticAnswer,
            Compiler.Decoder.publicAnswer, Public.shape_mk, Public.pairShape, extend, hu] <;>
            exact congrArg Public.respond (decide_eq_decide.mpr Iff.rfl)
    | inr c =>
      cases y with
      | inl u =>
        cases hu : π u <;>
          simp [embedQuery, embedPoint, Public.staticAnswer,
            Compiler.Decoder.publicAnswer, Public.shape_mk, Public.pairShape, extend, hu] <;>
            exact congrArg Public.respond (decide_eq_decide.mpr Iff.rfl)
      | inr c' =>
        simp [embedQuery, embedPoint, Public.staticAnswer,
          Compiler.Decoder.publicAnswer, Public.shape_mk, Public.pairShape]

theorem staticAnswer_padding (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S)
    (p : P) (y : Public.Points S G I (C ⊕ P)) :
    Public.staticAnswer π (extend nb) (Sym2.mk (.inr (.inr p)) y) =
      if Sum.inr (Sum.inr p) = y then Reply.diagonal else .far := by
  classical
  cases y with
  | inl t =>
    cases ht : π t <;>
      simp [Public.staticAnswer, Public.decoder, Compiler.Decoder.publicAnswer,
        Public.shape_mk, Public.pairShape, extend, ht, Public.respond]
  | inr c =>
    simp [Public.staticAnswer, Public.decoder, Compiler.Decoder.publicAnswer,
      Public.shape_mk, Public.pairShape]

theorem public_point_cases (x : Public.Points S G I (C ⊕ P)) :
    (∃ y, embedPoint y = x) ∨ ∃ p : P, x = .inr (.inr p) := by
  cases x with
  | inl t => exact Or.inl ⟨.inl t, rfl⟩
  | inr c =>
    cases c with
    | inl c => exact Or.inl ⟨.inr c, rfl⟩
    | inr p => exact Or.inr ⟨p, rfl⟩

theorem staticAnswer_extension (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S) :
    Public.staticAnswer π (extend (P := P) nb) =
      queryReduction.oracle (Public.staticAnswer π nb) := by
  classical
  funext q
  induction q using Sym2.inductionOn with
  | _ x y =>
    rcases public_point_cases x with ⟨x, rfl⟩ | ⟨p, rfl⟩
    · rcases public_point_cases y with ⟨y, rfl⟩ | ⟨p, rfl⟩
      · change Public.staticAnswer π (extend nb) (embedQuery (Sym2.mk x y)) = _
        rw [staticAnswer_embed]
        change Public.staticAnswer π nb (Sym2.mk x y) =
          queryReduction.oracle (Public.staticAnswer π nb) (embedQuery (Sym2.mk x y))
        exact (oracle_embed _ _).symm
      · rw [Sym2.eq_swap]
        rw [staticAnswer_padding]
        simp only [Reduction.oracle, queryReduction, paddingShape_padding, Sum.elim_inl, id_eq]
    · rw [staticAnswer_padding]
      simp only [Reduction.oracle, queryReduction, paddingShape_padding, Sum.elim_inl, id_eq]

variable {Z : Type*}

theorem simulate_public (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S)
    (t : DecisionTree (Public.Queries S G I (C ⊕ P)) Reply Z) :
    (queryReduction.simulate t).output (Public.staticAnswer π nb) =
      (t.output (Public.staticAnswer π (extend nb)),
        t.transcript (Public.staticAnswer π (extend nb))) := by
  rw [staticAnswer_extension]
  exact queryReduction.simulate_result t (Public.staticAnswer π nb)

theorem simulate_public_queries (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S)
    (t : DecisionTree (Public.Queries S G I (C ⊕ P)) Reply Z) :
    (queryReduction.simulateOutput t).queries (Public.staticAnswer π nb) ≤
      t.queries (Public.staticAnswer π (extend nb)) := by
  rw [staticAnswer_extension]
  exact queryReduction.simulateOutput_queries t (Public.staticAnswer π nb)

theorem simulate_public_output (π : Equiv.Perm (Terminal S G I)) (nb : C → Finset S)
    (t : DecisionTree (Public.Queries S G I (C ⊕ P)) Reply Z) :
    (queryReduction.simulateOutput t).output (Public.staticAnswer π nb) =
      t.output (Public.staticAnswer π (extend nb)) := by
  rw [staticAnswer_extension]
  exact queryReduction.simulateOutput_result t (Public.staticAnswer π nb)

theorem simulate_public_bounded
    (t : DecisionTree (Public.Queries S G I (C ⊕ P)) Reply Z) (q : ℕ)
    (hq : Screening.DecisionTree.Bounded t q) :
    Screening.DecisionTree.Bounded (queryReduction.simulateOutput t) q :=
  queryReduction.simulateOutput_bounded t q hq

theorem simulate_public_noRepeats
    (t : DecisionTree (Public.Queries S G I (C ⊕ P)) Reply Z) (ht : t.NoRepeats) :
    (queryReduction.simulateOutput t).NoRepeats :=
  queryReduction.simulateOutput_noRepeats t ht

theorem cardinality [Fintype C] [Fintype P] :
    Fintype.card (Public.Points S G I (C ⊕ P)) =
      Fintype.card (Public.Points S G I C) + Fintype.card P := by
  simp [Public.Points, Fintype.card_sum, Nat.add_assoc]

end SteinerLowerBound.MetricComparison.Padding

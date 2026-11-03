module

public import SteinerLowerBound.MetricComparison.CompilerExecution

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Public

open scoped BigOperators Classical
open HardDistribution
open Screening (Terminal Reply)

abbrev Points (S G I C : Type*) := Terminal S G I ⊕ C
abbrev Queries (S G I C : Type*) := Sym2 (Points S G I C)

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable def pairShape (π : Equiv.Perm (Terminal S G I)) :
    Points S G I C → Points S G I C → Reply ⊕ (C × S)
  | .inl u, .inl v =>
      .inl (if u = v then .diagonal else if Screening.SameCluster π u v then .cluster else .far)
  | .inr c, .inr c' => .inl (if c = c' then .diagonal else .far)
  | .inl u, .inr c | .inr c, .inl u =>
      match π u with
      | .inl s => .inr (c, s)
      | .inr _ => .inl .far

theorem pairShape_comm (π : Equiv.Perm (Terminal S G I)) (x y : Points S G I C) :
    pairShape π x y = pairShape π y x := by
  classical
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      have hs : Screening.SameCluster π u v ↔ Screening.SameCluster π v u := by
        simp only [Screening.SameCluster, and_comm]
      simp only [pairShape, eq_comm, hs]
    | inr c => rfl
  | inr c =>
    cases y with
    | inl u => rfl
    | inr c' => simp only [pairShape, eq_comm]

noncomputable def shape (π : Equiv.Perm (Terminal S G I)) :
    Queries S G I C → Reply ⊕ (C × S) :=
  Sym2.lift ⟨pairShape π, pairShape_comm π⟩

@[simp]
theorem shape_mk (π : Equiv.Perm (Terminal S G I)) (x y : Points S G I C) :
    shape π (Sym2.mk x y) = pairShape π x y := by
  rw [shape, Sym2.lift_mk]

def contactQuery (π : Equiv.Perm (Terminal S G I)) (c : C) (s : S) :
    Queries S G I C :=
  Sym2.mk (.inr c) (.inl (π.symm (.inl s)))

theorem shape_contact_recover (π : Equiv.Perm (Terminal S G I))
    (q : Queries S G I C) (c : C) (s : S) (hq : shape π q = .inr (c, s)) :
    q = contactQuery π c s := by
  classical
  induction q using Sym2.inductionOn with
  | _ x y =>
    cases x with
    | inl u =>
      cases y with
      | inl v => simp [pairShape] at hq
      | inr c' =>
        cases hp : π u with
        | inl s' =>
          simp only [shape_mk, pairShape, hp, Sum.inr.injEq, Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hu : π.symm (.inl s') = u := by rw [← hp, π.symm_apply_apply]
          simp only [contactQuery, hu]
          exact Sym2.eq_swap
        | inr gi => simp [pairShape, hp] at hq
    | inr c' =>
      cases y with
      | inl u =>
        cases hp : π u with
        | inl s' =>
          simp only [shape_mk, pairShape, hp, Sum.inr.injEq, Prod.mk.injEq] at hq
          obtain ⟨rfl, rfl⟩ := hq
          have hu : π.symm (.inl s') = u := by rw [← hp, π.symm_apply_apply]
          simp only [contactQuery, hu]
        | inr gi => simp [pairShape, hp] at hq
      | inr c'' => simp [pairShape] at hq

@[simp]
theorem shape_contact (π : Equiv.Perm (Terminal S G I)) (c : C) (s : S) :
    shape π (contactQuery π c s) = .inr (c, s) := by
  simp [contactQuery, pairShape]

def respond (b : Bool) : Reply := if b then .unit else .far

@[reducible] noncomputable def decoder (π : Equiv.Perm (Terminal S G I)) :
    Compiler.Decoder (Queries S G I C) Reply C S where
  shape := shape π
  respond := respond
  contact_unique q q' c u hq hq' :=
    (shape_contact_recover π q c u hq).trans (shape_contact_recover π q' c u hq').symm

def encode : Screening.Query (Terminal S G I) C → Queries S G I C
  | .tt u v => Sym2.mk (.inl u) (.inl v)
  | .ct c u => Sym2.mk (.inr c) (.inl u)
  | .cc c c' => Sym2.mk (.inr c) (.inr c')

def orientPair : Points S G I C → Points S G I C → Screening.Query (Terminal S G I) C
  | .inl u, .inl v => .tt u v
  | .inr c, .inr c' => .cc c c'
  | .inl u, .inr c | .inr c, .inl u => .ct c u

noncomputable def orient (q : Queries S G I C) : Screening.Query (Terminal S G I) C :=
  orientPair (Quot.out q).1 (Quot.out q).2

theorem encode_orientPair (x y : Points S G I C) :
    encode (orientPair x y) = Sym2.mk x y := by
  cases x <;> cases y <;> simp only [orientPair, encode]
  exact Sym2.eq_swap

@[simp]
theorem encode_orient (q : Queries S G I C) : encode (orient q) = q :=
  (encode_orientPair (Quot.out q).1 (Quot.out q).2).trans (Quot.out_eq q)

noncomputable def specialLabel (π : Equiv.Perm (Terminal S G I)) : S ↪ Terminal S G I :=
  ⟨fun s => π.symm (.inl s), fun _ _ he => Sum.inl_injective (π.symm.injective he)⟩

@[simp]
theorem specialLabel_position (π : Equiv.Perm (Terminal S G I)) (s : S) :
    π (specialLabel π s) = .inl s := π.apply_symm_apply _

def specialPart (π : Equiv.Perm (Terminal S G I)) (u : Terminal S G I) : Option S :=
  match π u with
  | .inl s => some s
  | .inr _ => none

@[simp]
theorem specialPart_label (π : Equiv.Perm (Terminal S G I)) (s : S) :
    specialPart π (specialLabel π s) = some s := by
  simp [specialPart]

theorem specialPart_eq_some (π : Equiv.Perm (Terminal S G I)) (u : Terminal S G I) (s : S) :
    specialPart π u = some s ↔ u = specialLabel π s := by
  classical
  unfold specialPart
  cases hp : π u with
  | inl s' =>
    simp only [Option.some.injEq]
    constructor
    · intro he
      apply π.injective
      simpa only [specialLabel_position, he] using hp
    · intro he
      have hh := congrArg π he
      rw [specialLabel_position, hp] at hh
      exact Sum.inl.inj hh
  | inr gi =>
    constructor
    · intro he
      cases he
    · intro he
      have hh := congrArg π he
      rw [specialLabel_position, hp] at hh
      cases hh

def replyValue (ell : ℝ) : Reply → ℝ
  | .diagonal => 0
  | .cluster => ell
  | .unit => 1
  | .far => 2

def place (π : Equiv.Perm (Terminal S G I)) : Points S G I C → Point S G I C
  | .inl u =>
      match π u with
      | .inl s => .special s
      | .inr (g, i) => .ordinary g i
  | .inr c => .center c

@[reducible] noncomputable def staticAnswer (π : Equiv.Perm (Terminal S G I))
    (N : C → Finset S) : Queries S G I C → Reply :=
  (decoder π).publicAnswer (fun _ cu => decide (cu.2 ∈ N cu.1)) []

theorem staticAnswer_metric (π : Equiv.Perm (Terminal S G I)) (N : C → Finset S)
    (ell : ℝ) (x y : Points S G I C) :
    replyValue ell (staticAnswer π N (Sym2.mk x y)) =
      Point.distance ell (fun c => (N c : Set S)) (place π x) (place π y) := by
  classical
  have he (u v : Terminal S G I) : u = v ↔ π u = π v := π.injective.eq_iff.symm
  cases x with
  | inl u =>
    cases y with
    | inl v =>
      cases hu : π u <;> cases hv : π v <;>
        simp [staticAnswer, decoder, Compiler.Decoder.publicAnswer, shape_mk, pairShape,
          replyValue, place, hu, hv, he u v, Screening.SameCluster, Screening.clusterPosition,
          Point.distance, Point.sameCluster, Point.unitAdjacent] <;> clear he <;>
          split_ifs <;>
          simp_all only [replyValue, and_true, true_and, and_false, false_and, not_true_eq_false] <;>
          aesop (add safe Prod.ext)
    | inr c =>
      cases hu : π u <;>
        simp [staticAnswer, decoder, Compiler.Decoder.publicAnswer, shape_mk, pairShape,
          respond, replyValue, place, hu, Point.distance, Point.sameCluster, Point.unitAdjacent] <;> clear he <;>
          split_ifs <;> simp_all
  | inr c =>
    cases y with
    | inl u =>
      cases hu : π u <;>
        simp [staticAnswer, decoder, Compiler.Decoder.publicAnswer, shape_mk, pairShape,
          respond, replyValue, place, hu, Point.distance, Point.sameCluster, Point.unitAdjacent] <;> clear he <;>
          split_ifs <;> simp_all
    | inr c' =>
      simp [staticAnswer, decoder, Compiler.Decoder.publicAnswer, shape_mk, pairShape,
        replyValue, place, Point.distance, Point.sameCluster, Point.unitAdjacent] <;> clear he <;>
        split_ifs <;> simp_all

end SteinerLowerBound.MetricComparison.Public

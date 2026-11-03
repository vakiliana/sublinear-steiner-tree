module

public import SteinerLowerBound.MetricComparison.Embedding

@[expose] public section

namespace SteinerLowerBound.MetricComparison.Public

open scoped BigOperators Classical
open HardDistribution
open Screening (Terminal Reply)

variable {S G I C : Type*} [Fintype S] [Fintype G] [Fintype I]

noncomputable def labelEmbedding (π : Equiv.Perm (Terminal S G I)) :
    PartialEmbedding S (Terminal S G I) where
  embed := specialLabel π
  project := specialPart π
  project_iff := specialPart_eq_some π

noncomputable def internalSupport (F : C → Finset S) (c : C) : Finset (Terminal S G I) :=
  (F c).map Function.Embedding.inl

theorem relabel_internalSupport (π : Equiv.Perm (Terminal S G I)) (F : C → Finset S) :
    Screening.relabel π (internalSupport F) = (labelEmbedding π).lift F := by
  funext c
  unfold Screening.relabel internalSupport PartialEmbedding.lift labelEmbedding
  rw [Finset.map_map]
  rfl

noncomputable def screenShape (π : Equiv.Perm (Terminal S G I)) :
    Screening.Query (Terminal S G I) C → Reply ⊕ (C × S)
  | .tt u v =>
      .inl (if u = v then .diagonal else if Screening.SameCluster π u v then .cluster else .far)
  | .ct c u =>
      match π u with
      | .inl s => .inr (c, s)
      | .inr _ => .inl .far
  | .cc c c' => .inl (if c = c' then .diagonal else .far)

theorem shape_encode (π : Equiv.Perm (Terminal S G I))
    (q : Screening.Query (Terminal S G I) C) :
    shape π (encode q) = screenShape π q := by
  cases q with
  | tt u v => simp only [encode, shape_mk, pairShape, screenShape]
  | cc c c' => simp only [encode, shape_mk, pairShape, screenShape]
  | ct c u =>
    cases hp : π u <;> simp only [encode, shape_mk, pairShape, screenShape, hp]

theorem shape_orient (π : Equiv.Perm (Terminal S G I)) (q : Queries S G I C) :
    shape π q = screenShape π (orient q) :=
  (congrArg (shape π) (encode_orient q)).symm.trans (shape_encode π (orient q))

theorem centerHistory_append (h : List (Screening.Query (Terminal S G I) C))
    (q : Screening.Query (Terminal S G I) C) :
    Screening.centerHistory (h ++ [q]) = Screening.centerHistory h ++
      (match q with | .ct c u => [(c, u)] | _ => []) := by
  cases q <;> simp [Screening.centerHistory, List.filterMap_append]

theorem contacts_oriented_history (π : Equiv.Perm (Terminal S G I))
    (h : List (Queries S G I C)) :
    (decoder π).contacts h =
      (labelEmbedding π).history (Screening.centerHistory (h.map orient)) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h q ih =>
    rw [Compiler.Decoder.contacts_append, List.map_append, List.map_singleton,
      centerHistory_append]
    have hs := shape_orient π q
    change (decoder π).contacts h ++ ((shape π q).getRight?).toList = _
    rw [hs, ih]
    cases hq : orient q with
    | tt u v => simp only [screenShape, Sum.getRight?, Option.toList_none, List.append_nil]
    | cc c c' => simp only [screenShape, Sum.getRight?, Option.toList_none, List.append_nil]
    | ct c u =>
      rw [PartialEmbedding.history_append]
      cases hu : π u <;>
        simp only [screenShape, hu, Sum.getRight?, labelEmbedding, specialPart,
          Option.map_some, Option.map_none, Option.toList_some, Option.toList_none,
          List.append_nil]

noncomputable def gatedAnswer (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset S) (h : List (Queries S G I C)) (q : Queries S G I C) : Reply :=
  Screening.queryAnswer π (internalSupport F) (internalSupport H) (h.map orient) (orient q)

theorem gatedAnswer_eq_decoded (π : Equiv.Perm (Terminal S G I))
    (F H : C → Finset S) (h : List (Queries S G I C)) (q : Queries S G I C) :
    gatedAnswer π F H h q =
      (decoder π).publicAnswer (fun hs cu => TwoAnchor.answer F H hs cu.1 cu.2) h q := by
  classical
  unfold gatedAnswer Compiler.Decoder.publicAnswer
  simp only [decoder]
  rw [shape_orient π q]
  cases hq : orient q with
  | tt u v =>
    simp only [Screening.queryAnswer, screenShape]
    split_ifs <;> rfl
  | cc c c' => rfl
  | ct c u =>
    simp only [Screening.queryAnswer, screenShape,
      relabel_internalSupport π F, relabel_internalSupport π H]
    cases hu : π u with
    | inl s =>
      have he : u = (labelEmbedding π).embed s := (Equiv.eq_symm_apply π).mpr hu
      rw [he, PartialEmbedding.answer, ← contacts_oriented_history π h]
      rfl
    | inr gi =>
      have hp : (labelEmbedding π).project u = none := by simp [labelEmbedding, specialPart, hu]
      rw [PartialEmbedding.answer_outside _ F H _ c u hp]
      rfl

end SteinerLowerBound.MetricComparison.Public

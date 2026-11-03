module

public import SteinerUpperBound.PortGraph.Addresses

@[expose] public section

namespace SteinerUpperBound.PortGraph

open QueryProgram
open scoped Classical BigOperators
open Covers.Geometry

variable {n k b B : ℕ} {Q : Type}

noncomputable def reply (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (D : Vertex I bits cfg B) (v x y : Fin n) (hx : x ∈ I.terminals) (hy : y ∈ D.val)
    (ci : Fin b) : LocalAccess.PortReply n k b B where
  otherRoot := rootEmbedding I bits cfg B hT D
  other := canonicalFrame I cfg b B D.val
  reverse := (ci, pointPosition I bits cfg b B hT hnd D y hy, terminalPosition I cfg hT x hx)
  name := (v, s(x, y))

theorem finish_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (D : Vertex I bits cfg B) (v x y : Fin n) (hx : x ∈ I.terminals) (hy : y ∈ D.val)
    (ci : Fin b) (c : Cache Q) :
    (LocalAccess.finishResult cfg v x y (canonicalFrame I cfg b B D.val) ci c).value.1 =
      some (reply I bits cfg hT hnd D v x y hx hy ci) := by
  simp only [LocalAccess.finishResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure]
  rw [pointPosition_index I bits cfg b B hT hnd D y hy,
    terminalPosition_index I cfg hT hnd x hx, frame_head I bits cfg b B hT D]
  rfl

theorem hits_frame_iff (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) {C : Finset (Fin n)}
    (hC : C ∈ parts I bits cfg) :
    (LocalAccess.hitsResult cfg.covered (canonicalFrame I cfg b B C).points).value = true ↔
      ¬ Disjoint C (removed I cfg) := by
  rw [LocalAccess.hits_value, canonicalFrame_points]
  have hsub := (componentsOn_subset I _ _ hC).trans (retained_subset I bits cfg)
  constructor
  · rintro ⟨x, hx, hc⟩ hd
    have hxC := (pointList_mem I cfg hT C hsub x).mp hx
    exact Finset.disjoint_left.mp hd hxC (Finset.mem_filter.mpr ⟨hsub hxC, hc⟩)
  · intro hn
    by_contra hnone
    apply hn
    apply Finset.disjoint_left.mpr
    intro x hxC hxD
    exact hnone ⟨x, (pointList_mem I cfg hT C hsub x).mpr hxC, (Finset.mem_filter.mp hxD).2⟩

theorem hits_vertex_false (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (D : Vertex I bits cfg B) :
    (LocalAccess.hitsResult cfg.covered (canonicalFrame I cfg b B D.val).points).value = false := by
  have hf := hits_frame_iff I bits cfg b B hT (vertex_part I bits cfg B D)
  cases he : (LocalAccess.hitsResult cfg.covered (canonicalFrame I cfg b B D.val).points).value with
  | false => rfl
  | true => exact (hf.mp he (vertex_disjoint I bits cfg B D)).elim

/-- This is the actual full-terminal third-point scan. Original eligibility is
proved from complete partition blocks, without deleting large or covered parts. -/
theorem third_eligible (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C D : Vertex I bits cfg B) (v x y : Fin n)
    (hx : x ∈ C.val) (hy : y ∈ D.val) (hne : C.val ≠ D.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v y ≤ radius cfg)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.thirdResult I.weight bits cfg.key (radius cfg) v
      (canonicalFrame I cfg b B C.val).points (canonicalFrame I cfg b B D.val).points
      cfg.terminals.toList c).value.found = true ↔ v ∈ eligible I bits cfg := by
  rw [LocalAccess.third_value _ _ _ _ _ _ _ _ _ hc, canonicalFrame_points, canonicalFrame_points]
  have hCsub := (vertex_subset I bits cfg B C).trans (retained_subset I bits cfg)
  have hDsub := (vertex_subset I bits cfg B D).trans (retained_subset I bits cfg)
  have hCrow : C.val ∈ rows I bits cfg v :=
    (mem_rowOn I _ _ _ v C.val).mpr ⟨vertex_part I bits cfg B C, x, hx, hdx⟩
  have hDrow : D.val ∈ rows I bits cfg v :=
    (mem_rowOn I _ _ _ v D.val).mpr ⟨vertex_part I bits cfg B D, y, hy, hdy⟩
  have he := eligible_iff_third I (retained I bits cfg) cfg.scale (radius cfg) v hCrow hDrow hne
  constructor
  · rintro ⟨z, hzT, hzC, hzD, hd, hb⟩
    apply he.mpr
    refine ⟨z, (mem_retained I bits cfg z).mpr ⟨(terminal_mem I cfg hT z).mp hzT, hb⟩, ?_, ?_, ?_⟩
    · exact fun hz => hzC ((pointList_mem I cfg hT C.val hCsub z).mpr hz)
    · exact fun hz => hzD ((pointList_mem I cfg hT D.val hDsub z).mpr hz)
    · simpa only [Instance.weight_mk] using hd
  · intro hv
    obtain ⟨z, hzN, hzC, hzD, hd⟩ := he.mp hv
    obtain ⟨hzT, hb⟩ := (mem_retained I bits cfg z).mp hzN
    refine ⟨z, (terminal_mem I cfg hT z).mpr hzT, ?_, ?_, ?_, hb⟩
    · exact fun hz => hzC ((pointList_mem I cfg hT C.val hCsub z).mp hz)
    · exact fun hz => hzD ((pointList_mem I cfg hT D.val hDsub z).mp hz)
    · simpa only [Instance.weight_mk] using hd

theorem eligibility_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C D : Vertex I bits cfg B) (v x y : Fin n)
    (hx : x ∈ C.val) (hy : y ∈ D.val) (hne : C.val ≠ D.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v y ≤ radius cfg)
    (ci : Fin b) (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.eligibilityResult I.weight bits cfg v x y
      (canonicalFrame I cfg b B C.val) (canonicalFrame I cfg b B D.val) ci c).value.1 =
      if v ∈ eligible I bits cfg then some (reply I bits cfg hT hnd D v x y
        ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg) hx) hy ci) else none := by
  have he := third_eligible (b := b) I bits cfg hT C D v x y hx hy hne hdx hdy c hc
  by_cases hv : v ∈ eligible I bits cfg
  · have hf := he.mpr hv
    dsimp only [radius] at hf
    simp only [LocalAccess.eligibilityResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure]
    rw [hf]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false, ite_eq_left hv]
    exact finish_value I bits cfg hT hnd D v x y _ hy ci _
  · have hf : (LocalAccess.thirdResult I.weight bits cfg.key (radius cfg) v
        (canonicalFrame I cfg b B C.val).points (canonicalFrame I cfg b B D.val).points
        cfg.terminals.toList c).value.found = false := by
      cases hb : (LocalAccess.thirdResult I.weight bits cfg.key (radius cfg) v
        (canonicalFrame I cfg b B C.val).points (canonicalFrame I cfg b B D.val).points
        cfg.terminals.toList c).value.found <;> simp_all
    dsimp only [radius] at hf
    simp only [LocalAccess.eligibilityResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure]
    rw [hf]
    simp [Bool.not_false, hv, LocalAccess.replyResult, Outcome.add, Outcome.pure]

theorem center_index_none (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (D : Vertex I bits cfg B)
    (v : Fin n) (hv : v ∉ lists I bits cfg b D.val) :
    (LocalAccess.indexResult (canonicalFrame I cfg b B D.val).rows.slots.get v).value = none := by
  cases he : (LocalAccess.indexResult (canonicalFrame I cfg b B D.val).rows.slots.get v).value with
  | none => rfl
  | some i =>
    exact (hv (rowSlot_mem I bits cfg b B hT (vertex_part I bits cfg B D)
      (LocalAccess.index_some _ v he))).elim

theorem mutual_value (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C D : Vertex I bits cfg B) (v x y : Fin n)
    (hx : x ∈ C.val) (hy : y ∈ D.val) (hne : C.val ≠ D.val)
    (hdx : I.distance v x ≤ radius cfg) (hdy : I.distance v y ≤ radius cfg)
    (c : Cache Q) (hc : Cache.Correct bits c) :
    (LocalAccess.mutualResult I.weight bits cfg v x y
      (canonicalFrame I cfg b B C.val) (canonicalFrame I cfg b B D.val) c).value.1 =
      if hv : v ∈ lists I bits cfg b D.val then
        if v ∈ eligible I bits cfg then some (reply I bits cfg hT hnd D v x y
          ((vertex_subset I bits cfg B C).trans (retained_subset I bits cfg) hx) hy
          (centerPosition I bits cfg b B hT D v hv)) else none
      else none := by
  simp only [LocalAccess.mutualResult, bind, outcomeMonad, Outcome.combine, Outcome.add, Outcome.pure]
  rw [hits_vertex_false (b := b) I bits cfg hT D]
  simp only [Bool.false_eq_true, ite_false]
  by_cases hv : v ∈ lists I bits cfg b D.val
  · rw [centerPosition_index I bits cfg b B hT D v hv, dite_eq_left hv]
    exact eligibility_value I bits cfg hT hnd C D v x y hx hy hne hdx hdy _ c hc
  · rw [center_index_none I bits cfg hT D v hv, dite_eq_right hv]
    rfl

end SteinerUpperBound.PortGraph

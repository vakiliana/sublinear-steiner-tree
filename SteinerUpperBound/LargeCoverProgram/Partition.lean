module

public import SteinerUpperBound.LargeCoverProgram.Saving

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {Q : Type} {n k : ℕ}

private theorem component_mem_iff {V : Type*} (I : Instance V) (N : Finset V) (a : ℝ)
    (C : Finset V) :
    C ∈ Covers.Geometry.componentsOn I N a ↔
      ∃ v ∈ N, Covers.Geometry.componentOn I N a v = C := by
  simp only [Covers.Geometry.componentsOn, Finset.mem_image]

private theorem fiber_mem_iff {X P : Type*} [Fintype X] (part : X → P) (C : P) (x : X) :
    x ∈ SavingScores.fiber part C ↔ part x = C := by
  simp [SavingScores.fiber]

abbrev Part (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) := ↥(PortGraph.parts I bits cfg)

theorem retainedIndex_bit (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (x : RetainedIndex bits cfg) : bits (cfg.key (cfg.terminals.get x.val)) = true := by
  simpa [Covers.Rejection.retained, CategoricalCoupling.selected] using x.property

theorem retainedIndex_mem (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (x : RetainedIndex bits cfg) :
    cfg.terminals.get x.val ∈ PortGraph.retained I bits cfg :=
  (PortGraph.mem_retained I bits cfg _).mpr
    ⟨(PortGraph.terminal_mem I cfg hT _).mp (terminal_get_mem cfg x.val), retainedIndex_bit bits cfg x⟩

theorem retainedIndex_exists (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (v : Fin n)
    (hv : v ∈ PortGraph.retained I bits cfg) :
    ∃ x : RetainedIndex bits cfg, cfg.terminals.get x.val = v := by
  have ht := (PortGraph.terminal_mem I cfg hT v).mpr
    ((PortGraph.mem_retained I bits cfg v).mp hv).1
  obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp ht)
  let u : Fin (k + 1) := ⟨i, hi⟩
  have hu : cfg.terminals.get u = v := by simpa only [Vector.get_eq_getElem] using he
  refine ⟨⟨u, ?_⟩, hu⟩
  have hb := ((PortGraph.mem_retained I bits cfg v).mp hv).2
  simpa [Covers.Rejection.retained, CategoricalCoupling.selected, hu] using hb

theorem terminal_injective (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hnd : cfg.terminals.toList.Nodup) : Function.Injective cfg.terminals.get := by
  intro i j hij
  have hlist := List.nodup_iff_injective_get.mp hnd
  let i' : Fin cfg.terminals.toList.length := ⟨i.val, by simpa using i.isLt⟩
  let j' : Fin cfg.terminals.toList.length := ⟨j.val, by simpa using j.isLt⟩
  have hi : cfg.terminals.toList.get i' = cfg.terminals.get i := by
    simp [i', List.get_eq_getElem, Vector.get_eq_getElem]
  have hj : cfg.terminals.toList.get j' = cfg.terminals.get j := by
    simp [j', List.get_eq_getElem, Vector.get_eq_getElem]
  have hv := congrArg (fun z : Fin cfg.terminals.toList.length => z.val)
    (hlist (hi.trans (hij.trans hj.symm)))
  exact Fin.ext hv

noncomputable def partition (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) :
    RetainedIndex bits cfg → Part I bits cfg :=
  fun x => ⟨componentAt I bits cfg x.val,
    componentAt_part I bits cfg hT x.val (retainedIndex_bit bits cfg x)⟩

theorem partition_surjective (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) :
    Function.Surjective (partition I bits cfg hT) := by
  intro C
  have hm : C.val ∈ Covers.Geometry.componentsOn I (PortGraph.retained I bits cfg) cfg.scale := C.property
  obtain ⟨v, hv, he⟩ := (component_mem_iff I _ _ _).mp hm
  obtain ⟨x, hx⟩ := retainedIndex_exists I bits cfg hT v hv
  refine ⟨x, Subtype.ext ?_⟩
  dsimp [partition, componentAt, PortGraph.portComponent]
  rw [hx]
  exact he

theorem partition_fiber_iff (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals)
    (x : RetainedIndex bits cfg) (C : Part I bits cfg) :
    partition I bits cfg hT x = C ↔ cfg.terminals.get x.val ∈ C.val := by
  constructor
  · intro he
    have hm := Covers.Geometry.componentOn_self I (PortGraph.retained I bits cfg) cfg.scale
      (retainedIndex_mem I bits cfg hT x)
    change cfg.terminals.get x.val ∈ (partition I bits cfg hT x).val at hm
    rwa [he] at hm
  · intro hx
    apply Subtype.ext
    exact PortGraph.portComponent_eq I bits cfg C.property hx

theorem partition_size (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Part I bits cfg) :
    SavingScores.partSize (partition I bits cfg hT) C = C.val.card := by
  have hi : Function.Injective (fun x : RetainedIndex bits cfg => cfg.terminals.get x.val) :=
    (terminal_injective cfg hnd).comp Subtype.val_injective
  have he : (SavingScores.fiber (partition I bits cfg hT) C).image
      (fun x => cfg.terminals.get x.val) = C.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact (partition_fiber_iff I bits cfg hT x C).mp ((fiber_mem_iff _ _ _).mp hx)
    · intro hv
      have hret := Covers.Geometry.componentsOn_subset I _ _ C.property hv
      obtain ⟨x, hx⟩ := retainedIndex_exists I bits cfg hT v hret
      refine Finset.mem_image.mpr ⟨x, (fiber_mem_iff _ _ _).mpr
        ((partition_fiber_iff I bits cfg hT x C).mpr ?_), hx⟩
      rwa [hx]
  rw [SavingScores.partSize, ← Finset.card_image_of_injective _ hi, he]

theorem retainedIndex_card (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    Nat.card (RetainedIndex bits cfg) = (PortGraph.retained I bits cfg).card := by
  have hi : Function.Injective (fun x : RetainedIndex bits cfg => cfg.terminals.get x.val) :=
    (terminal_injective cfg hnd).comp Subtype.val_injective
  have he : (Finset.univ : Finset (RetainedIndex bits cfg)).image
      (fun x => cfg.terminals.get x.val) = PortGraph.retained I bits cfg := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
      exact retainedIndex_mem I bits cfg hT x
    · intro hv
      obtain ⟨x, hx⟩ := retainedIndex_exists I bits cfg hT v hv
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := RetainedIndex bits cfg),
    ← Finset.card_image_of_injective _ hi, he]

noncomputable def partRows (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (v : Fin n) : Finset (Part I bits cfg) :=
  Finset.univ.filter fun C => C.val ∈ PortGraph.rows I bits cfg v

theorem saving_subtype {R U : Type*} (S : Finset U) (E : Finset R) (rows : R → Finset U) :
    SetSystem.saving E (fun r => (Finset.univ : Finset ↥S).filter (fun u => u.val ∈ rows r)) Finset.univ =
      SetSystem.saving E rows S := by
  letI : DecidableEq ↥S := Classical.decEq _
  have hc (F : Finset R) :
      ((Finset.univ : Finset ↥S) ∩ F.biUnion
        (fun r => (Finset.univ : Finset ↥S).filter (fun u => u.val ∈ rows r))).card =
        (S ∩ F.biUnion rows).card := by
    rw [← Finset.card_image_of_injective _ (Subtype.val_injective : Function.Injective (Subtype.val : ↥S → U))]
    congr 1
    ext u
    simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨r, hr, hxr⟩, rfl⟩
      exact ⟨x.property, r, hr, hxr⟩
    · rintro ⟨hu, r, hr, hur⟩
      exact ⟨⟨u, hu⟩, ⟨r, hr, hur⟩, rfl⟩
  unfold Structural.saving
  congr 1
  funext F
  rw [hc F]

theorem partSaving_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) :
    SavingScores.fullSaving (PortGraph.eligible I bits cfg) (partRows I bits cfg) =
      Covers.Geometry.savingOn I (PortGraph.retained I bits cfg) cfg.scale (PortGraph.radius cfg) := by
  have he := saving_subtype (PortGraph.parts I bits cfg) (PortGraph.eligible I bits cfg)
    (PortGraph.rows I bits cfg)
  apply Eq.trans ?_ he
  unfold SavingScores.fullSaving
  congr 1
  funext v
  ext C
  simp [partRows]

noncomputable def largeClasses (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ) : Finset (Part I bits cfg) :=
  Finset.univ.filter fun C => B < C.val.card

noncomputable def coveredClasses (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ) : Finset (Part I bits cfg) :=
  Finset.univ.filter fun C => C.val.card ≤ B ∧ coveredComponent cfg C.val = true

noncomputable def residualClasses (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ) : Finset (Part I bits cfg) :=
  Finset.univ.filter fun C => C.val.card ≤ B ∧ coveredComponent cfg C.val = false

theorem classes_partition (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ) :
    (Finset.univ : Finset (Part I bits cfg)) ⊆
      largeClasses I bits cfg B ∪ coveredClasses I bits cfg B ∪ residualClasses I bits cfg B ∧
      Disjoint (coveredClasses I bits cfg B) (residualClasses I bits cfg B) := by
  constructor
  · intro C _
    by_cases hs : C.val.card ≤ B
    · cases hh : coveredComponent cfg C.val <;>
        simp [largeClasses, coveredClasses, residualClasses, hs, hh]
    · simp [largeClasses, coveredClasses, residualClasses, hs, Nat.lt_of_not_ge hs]
  · apply Finset.disjoint_left.mpr
    intro C hc hu
    simp only [coveredClasses, residualClasses, Finset.mem_filter, Finset.mem_univ, true_and] at hc hu
    exact Bool.false_ne_true (hu.2.symm.trans hc.2)

theorem coveredComponent_false (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (C : Part I bits cfg) :
    coveredComponent cfg C.val = false ↔ Disjoint C.val (PortGraph.removed I cfg) := by
  have hsub : C.val ⊆ I.terminals :=
    (Covers.Geometry.componentsOn_subset I _ _ C.property).trans (PortGraph.retained_subset I bits cfg)
  have hm := PortGraph.pointList_mem I cfg hT C.val hsub
  constructor
  · intro hf
    apply Finset.disjoint_left.mpr
    intro x hx hr
    have hd := (Finset.mem_filter.mp hr).2
    have hh := (LocalAccess.hits_value cfg.covered (PortGraph.pointList cfg C.val)).mpr
      ⟨x, (hm x).mpr hx, hd⟩
    exact Bool.false_ne_true (hf.symm.trans hh)
  · intro hd
    by_contra hf
    have ht : coveredComponent cfg C.val = true := by cases h : coveredComponent cfg C.val <;> simp_all
    obtain ⟨x, hx, hDx⟩ := (LocalAccess.hits_value cfg.covered (PortGraph.pointList cfg C.val)).mp ht
    exact Finset.disjoint_left.mp hd ((hm x).mp hx)
      (Finset.mem_filter.mpr ⟨hsub ((hm x).mp hx), hDx⟩)

theorem residualClasses_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (B : ℕ) :
    residualClasses I bits cfg B =
      Finset.univ.filter (fun C : Part I bits cfg => C.val ∈ PortGraph.smallParts I bits cfg B) := by
  ext C
  simp only [residualClasses, PortGraph.smallParts, Finset.mem_filter, Finset.mem_univ,
    true_and, C.property]
  rw [coveredComponent_false I bits cfg hT C]

theorem coveredClasses_cover (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (B : ℕ)
    (selected : Selection (Fin n))
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value) :
    coveredClasses I bits cfg B ⊆ selected.centers.toFinset.biUnion (partRows I bits cfg) := by
  intro C hc
  have hh := (Finset.mem_filter.mp hc).2.2
  have hsub : C.val ⊆ I.terminals :=
    (Covers.Geometry.componentsOn_subset I _ _ C.property).trans (PortGraph.retained_subset I bits cfg)
  obtain ⟨x, hx, hd⟩ := (LocalAccess.hits_value cfg.covered (PortGraph.pointList cfg C.val)).mp hh
  have hxC := (PortGraph.pointList_mem I cfg hT C.val hsub x).mp hx
  rw [hD] at hd
  obtain ⟨v, hv, hdist⟩ := (LocalAccess.covered_get I.weight _ selected.centers x).mp hd
  refine Finset.mem_biUnion.mpr ⟨v, List.mem_toFinset.mpr hv, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (Covers.Geometry.mem_rowOn I _ _ _ v C.val).mpr
  exact ⟨C.property, x, hxC, by simpa only [Instance.weight_mk] using hdist⟩

theorem partRows_card (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (v : Fin n) :
    (partRows I bits cfg v).card = (PortGraph.rows I bits cfg v).card := by
  have he : (partRows I bits cfg v).image Subtype.val = PortGraph.rows I bits cfg v := by
    ext C
    constructor
    · intro h
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hc).2
    · intro h
      have hp := Covers.Geometry.rowOn_subset_componentsOn I (PortGraph.retained I bits cfg)
        cfg.scale (PortGraph.radius cfg) v h
      exact Finset.mem_image.mpr ⟨⟨C, hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  rw [← Finset.card_image_of_injective _ Subtype.val_injective, he]

theorem partRows_ineligible (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (v : Fin n) (hv : v ∉ PortGraph.eligible I bits cfg) :
    (partRows I bits cfg v).card ≤ 2 := by
  have hh : ¬ 3 ≤ (PortGraph.rows I bits cfg v).card := by
    simpa only [PortGraph.eligible, PortGraph.rows, Covers.Geometry.eligibleOn, Finset.mem_filter,
      Finset.mem_univ, true_and] using hv
  rw [partRows_card]
  omega

noncomputable def matchedPart {D : Type*} [Fintype D]
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (G : Matching.Graph (Part I bits cfg) D) (C : Finset (Fin n)) (rank : Matching.Rank D) : Bool :=
  if h : C ∈ PortGraph.parts I bits cfg then (G.vertexOracle rank ⟨C, h⟩).value.isSome else false

theorem matchedPart_partition {D : Type*} [Fintype D]
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (G : Matching.Graph (Part I bits cfg) D)
    (x : RetainedIndex bits cfg) (rank : Matching.Rank D) :
    matchedPart I bits cfg G (componentAt I bits cfg x.val) rank =
      (G.vertexOracle rank (partition I bits cfg hT x)).value.isSome := by
  have hc : componentAt I bits cfg x.val ∈ PortGraph.parts I bits cfg :=
    (partition I bits cfg hT x).property
  rw [matchedPart, dif_pos hc]
  rfl

end SteinerUpperBound.LargeCoverProgram

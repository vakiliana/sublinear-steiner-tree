module

public import SteinerUpperBound.PortGraph.Basic
public import SteinerUpperBound.SetSystem.CappedMatching

@[expose] public section

namespace SteinerUpperBound.PortGraph

open scoped Classical BigOperators
open Covers.Geometry

variable {n k : ℕ} {Q : Type}

abbrev RawCopy (n k : ℕ) := Fin n × (Fin k × Fin k)
abbrev Name (n : ℕ) := Fin n × Sym2 (Fin n)

def leftPort (cfg : LocalAccess.SlotConfig Q n k) (p : RawCopy n k) : Fin n :=
  cfg.terminals.get p.2.1

def rightPort (cfg : LocalAccess.SlotConfig Q n k) (p : RawCopy n k) : Fin n :=
  cfg.terminals.get p.2.2

noncomputable def portComponent (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (x : Fin n) : Finset (Fin n) :=
  componentOn I (retained I bits cfg) cfg.scale x

structure ValidCopy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (p : RawCopy n k) : Prop where
  ordered : p.2.1 < p.2.2
  left_retained : leftPort cfg p ∈ retained I bits cfg
  right_retained : rightPort cfg p ∈ retained I bits cfg
  left_small : portComponent I bits cfg (leftPort cfg p) ∈ smallParts I bits cfg B
  right_small : portComponent I bits cfg (rightPort cfg p) ∈ smallParts I bits cfg B
  different : portComponent I bits cfg (leftPort cfg p) ≠ portComponent I bits cfg (rightPort cfg p)
  eligible : p.1 ∈ eligible I bits cfg
  left_list : p.1 ∈ lists I bits cfg b (portComponent I bits cfg (leftPort cfg p))
  right_list : p.1 ∈ lists I bits cfg b (portComponent I bits cfg (rightPort cfg p))
  near_left : I.distance p.1 (leftPort cfg p) ≤ radius cfg
  near_right : I.distance p.1 (rightPort cfg p) ≤ radius cfg

abbrev Copy (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :=
  {p : RawCopy n k // ValidCopy I bits cfg b B p}

noncomputable instance (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :
    Fintype (Copy I bits cfg b B) := Fintype.ofFinite _

noncomputable def graph (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :
    Matching.Graph (Vertex I bits cfg B) (Copy I bits cfg b B) where
  left e := ⟨portComponent I bits cfg (leftPort cfg e.val), e.property.left_small⟩
  right e := ⟨portComponent I bits cfg (rightPort cfg e.val), e.property.right_small⟩
  loopless e h := e.property.different (congrArg Subtype.val h)

def name (cfg : LocalAccess.SlotConfig Q n k) {I : Instance (Fin n)} {bits : Q → Bool}
    {b B : ℕ} (e : Copy I bits cfg b B) : Name n :=
  (e.val.1, s(leftPort cfg e.val, rightPort cfg e.val))

def rawName (cfg : LocalAccess.SlotConfig Q n k) (p : RawCopy n k) : Name n :=
  (p.1, s(leftPort cfg p, rightPort cfg p))

noncomputable def publicNames (cfg : LocalAccess.SlotConfig Q n k) : Finset (Name n) :=
  Finset.univ.image (rawName cfg)

theorem name_mem_publicNames (cfg : LocalAccess.SlotConfig Q n k)
    {I : Instance (Fin n)} {bits : Q → Bool} {b B : ℕ} (e : Copy I bits cfg b B) :
    name cfg e ∈ publicNames cfg := by
  classical
  exact Finset.mem_image.mpr ⟨e.val, Finset.mem_univ _, rfl⟩

theorem publicNames_card_le (cfg : LocalAccess.SlotConfig Q n k) :
    (publicNames cfg).card ≤ n * k ^ 2 := by
  classical
  have h : (publicNames cfg).card ≤ Fintype.card (RawCopy n k) :=
    Finset.card_image_le
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

noncomputable def underlying (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) : SimpleGraph (Vertex I bits cfg B) :=
  (SetSystem.mutualGraph (smallParts I bits cfg B) (eligible I bits cfg)
    (lists I bits cfg b)).comap Subtype.val

theorem copies_card_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) :
    Fintype.card (Copy I bits cfg b B) ≤ n * k ^ 2 := by
  have h := Fintype.card_le_of_injective
    (fun e : Copy I bits cfg b B => e.val) Subtype.val_injective
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

theorem terminal_index (I : Instance (Fin n)) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) {x : Fin n} (hx : x ∈ I.terminals) :
    ∃ i : Fin k, cfg.terminals.get i = x := by
  have hm : x ∈ cfg.terminals.toList := List.mem_toFinset.mp (hT.symm ▸ hx)
  obtain ⟨i, hi, he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hm)
  exact ⟨⟨i, hi⟩, by simpa only [Vector.get_eq_getElem] using he⟩

theorem vector_get_injective {V : Type*} {d : ℕ} (v : Vector V d) (h : v.toList.Nodup) :
    Function.Injective v.get := by
  intro i j hij
  apply Fin.ext
  have hi : i.val < v.toList.length := by simpa only [Vector.length_toList] using i.isLt
  have hj : j.val < v.toList.length := by simpa only [Vector.length_toList] using j.isLt
  apply (h.getElem_inj_iff (hi := hi) (hj := hj)).mp
  rw [Vector.getElem_toList hi, Vector.getElem_toList hj]
  simpa only [Vector.get_eq_getElem] using hij

theorem portComponent_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) {C : Finset (Fin n)}
    (hC : C ∈ parts I bits cfg) {x : Fin n} (hx : x ∈ C) :
    portComponent I bits cfg x = C :=
  componentOn_eq_of_mem I _ _ hC hx

theorem graph_realizes (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) :
    SetSystem.Realizes (graph I bits cfg b B) (underlying I bits cfg b B) := by
  classical
  intro C C'
  constructor
  · intro h
    obtain ⟨_, _, hne, v, hv, hvC, hvC'⟩ := h
    obtain ⟨_, x, hx, hdx⟩ := (mem_rowOn I _ _ _ v C.val).mp
      (lists_sound I bits cfg b C.val hvC)
    obtain ⟨_, y, hy, hdy⟩ := (mem_rowOn I _ _ _ v C'.val).mp
      (lists_sound I bits cfg b C'.val hvC')
    have hxN := vertex_subset I bits cfg B C hx
    have hyN := vertex_subset I bits cfg B C' hy
    obtain ⟨i, hi⟩ := terminal_index I cfg hT (retained_subset I bits cfg hxN)
    obtain ⟨j, hj⟩ := terminal_index I cfg hT (retained_subset I bits cfg hyN)
    have hc : portComponent I bits cfg x = C.val := portComponent_eq I bits cfg
      (vertex_part I bits cfg B C) hx
    have hc' : portComponent I bits cfg y = C'.val := portComponent_eq I bits cfg
      (vertex_part I bits cfg B C') hy
    have hij : i ≠ j := by
      intro he
      have hxy : x = y := hi.symm.trans (he ▸ hj)
      exact hne (hc.symm.trans (hxy ▸ hc'))
    rcases lt_or_gt_of_ne hij with hij | hji
    · let e : Copy I bits cfg b B := ⟨(v, i, j),
        ⟨hij, by simpa [leftPort, hi] using hxN, by simpa [rightPort, hj] using hyN,
          by simpa [leftPort, hi, hc] using C.property,
          by simpa [rightPort, hj, hc'] using C'.property,
          by simpa [leftPort, rightPort, hi, hj, hc, hc'] using hne,
          hv, by simpa [leftPort, hi, hc] using hvC,
          by simpa [rightPort, hj, hc'] using hvC',
          by simpa [leftPort, hi] using hdx, by simpa [rightPort, hj] using hdy⟩⟩
      exact ⟨e, Or.inl ⟨Subtype.ext (by simpa [graph, e, leftPort, hi] using hc),
        Subtype.ext (by simpa [graph, e, rightPort, hj] using hc')⟩⟩
    · let e : Copy I bits cfg b B := ⟨(v, j, i),
        ⟨hji, by simpa [leftPort, hj] using hyN, by simpa [rightPort, hi] using hxN,
          by simpa [leftPort, hj, hc'] using C'.property,
          by simpa [rightPort, hi, hc] using C.property,
          by simpa [leftPort, rightPort, hi, hj, hc, hc'] using hne.symm,
          hv, by simpa [leftPort, hj, hc'] using hvC',
          by simpa [rightPort, hi, hc] using hvC,
          by simpa [leftPort, hj] using hdy, by simpa [rightPort, hi] using hdx⟩⟩
      exact ⟨e, Or.inr ⟨Subtype.ext (by simpa [graph, e, leftPort, hj] using hc'),
        Subtype.ext (by simpa [graph, e, rightPort, hi] using hc)⟩⟩
  · rintro ⟨e, he | he⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e.property.left_small, e.property.right_small, e.property.different,
        e.val.1, e.property.eligible, e.property.left_list, e.property.right_list⟩
    · obtain ⟨rfl, rfl⟩ := he
      exact ⟨e.property.right_small, e.property.left_small, e.property.different.symm,
        e.val.1, e.property.eligible, e.property.right_list, e.property.left_list⟩

theorem name_injective (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (hT : cfg.terminals.toList.Nodup) :
    Function.Injective (name cfg : Copy I bits cfg b B → Name n) := by
  intro e f hef
  have hcenter := congrArg Prod.fst hef
  have hports := congrArg Prod.snd hef
  change s(leftPort cfg e.val, rightPort cfg e.val) =
    s(leftPort cfg f.val, rightPort cfg f.val) at hports
  have hinj := vector_get_injective cfg.terminals hT
  simp only [Sym2.eq_iff] at hports
  apply Subtype.ext
  apply Prod.ext
  · exact hcenter
  rcases hports with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact Prod.ext (hinj hl) (hinj hr)
  · have hi := hinj hl
    have hj := hinj hr
    have hlt := e.property.ordered
    have hlt' := f.property.ordered
    omega

theorem copy_ports_outside_removed (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (b B : ℕ) (e : Copy I bits cfg b B) :
    leftPort cfg e.val ∉ removed I cfg ∧ rightPort cfg e.val ∉ removed I cfg := by
  have hl := vertex_disjoint I bits cfg B ((graph I bits cfg b B).left e)
  have hr := vertex_disjoint I bits cfg B ((graph I bits cfg b B).right e)
  exact ⟨fun h => Finset.disjoint_left.mp hl
      (componentOn_self I _ _ e.property.left_retained) h,
    fun h => Finset.disjoint_left.mp hr (componentOn_self I _ _ e.property.right_retained) h⟩

end SteinerUpperBound.PortGraph

module

public import SteinerUpperBound.LargeCoverProgram.Partition
public import SteinerUpperBound.PortGraph.Degree

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical

variable {Q : Type} {n k : ℕ}

theorem image_previousUnion_empty {U V : Type*} {nr : ℕ}
    (R : Fin nr → Finset U) (T : Fin nr → Bool) (j : Fin nr) (f : U → V) :
    (ReusableSample.previousUnion R T ∅ j).image f =
      ReusableSample.previousUnion (fun i => (R i).image f) T ∅ j := by
  letI : DecidableEq U := Classical.decEq _
  letI : DecidableEq V := Classical.decEq _
  ext v
  have hU (x : U) : x ∉ (∅ : Finset U) := by simp
  have hV (y : V) : y ∉ (∅ : Finset V) := by simp
  simp only [Finset.mem_image, ReusableSample.mem_previousUnion, hU, hV, false_or]
  constructor
  · rintro ⟨x, ⟨i, hij, ht, hx⟩, rfl⟩
    exact ⟨i, hij, ht, x, hx, rfl⟩
  · rintro ⟨i, hij, ht, x, hx, rfl⟩
    exact ⟨x, ⟨i, hij, ht, hx⟩, rfl⟩

theorem image_fresh_empty {U V : Type*} {nr : ℕ}
    (R : Fin nr → Finset U) (T : Fin nr → Bool) (j : Fin nr)
    (f : U → V) (hf : Function.Injective f) :
    (ReusableSample.fresh R T ∅ j).image f =
      ReusableSample.fresh (fun i => (R i).image f) T ∅ j := by
  letI : DecidableEq U := Classical.decEq _
  letI : DecidableEq V := Classical.decEq _
  rw [ReusableSample.fresh, Finset.image_sdiff _ _ hf, image_previousUnion_empty]
  rfl

noncomputable def ambientPoolRows (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (v : Fin n) : Finset (Fin n) :=
  (PortGraph.retained I bits cfg).filter (fun y => I.distance v y ≤ PortGraph.radius cfg)

theorem retainedRows_image (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (v : Fin n) :
    (retainedRows I.weight bits cfg.terminals cfg.key cfg.scale v).image
      (fun x => cfg.terminals.get x.val) = ambientPoolRows I bits cfg v := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨retainedIndex_mem I bits cfg hT x, ?_⟩
    simpa only [retainedRows, ReusableSample.OracleProgram.rows, Finset.mem_filter,
      Finset.mem_univ, true_and, Instance.weight_mk, PortGraph.radius] using hx
  · intro hy
    obtain ⟨hret, hnear⟩ := Finset.mem_filter.mp hy
    obtain ⟨x, hx⟩ := retainedIndex_exists I bits cfg hT y hret
    refine Finset.mem_image.mpr ⟨x, ?_, hx⟩
    simpa only [retainedRows, ReusableSample.OracleProgram.rows, Finset.mem_filter,
      Finset.mem_univ, true_and, Instance.weight_mk, PortGraph.radius, hx] using hnear

/-- Every accepted row has the requested TRUE fresh size in the ambient point
universe, in the fixed public processing order. -/
theorem poolGood_accepted_fresh (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (selected : Selection (Fin n))
    (hgood : PoolGood I.weight bits p cfg.terminals cfg.key cfg.scale (some (selected, cfg.covered))) :
    ∀ v ∈ selected.centers,
      ((PortGraph.retained I bits cfg).card : ℝ) / p.t ≤
        (ReusableSample.fresh (ambientPoolRows I bits cfg) (selectionBits selected) ∅ v).card := by
  letI : DecidableEq (RetainedIndex bits cfg) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  let R := retainedRows I.weight bits cfg.terminals cfg.key cfg.scale
  let f := fun x : RetainedIndex bits cfg => cfg.terminals.get x.val
  have hinj : Function.Injective f := (terminal_injective cfg hnd).comp Subtype.val_injective
  have hrows : (fun i => (R i).image f) = ambientPoolRows I bits cfg := by
    funext i
    ext y
    have hh := Finset.ext_iff.mp (retainedRows_image I bits cfg hT i) y
    simpa only [Finset.mem_image, R, f] using hh
  have hspec : ReusableSample.Specification R p.t (selectionBits selected) := hgood
  intro v hv
  have ht : selectionBits selected v = true := by simpa only [selectionBits, decide_eq_true_eq] using hv
  have hh := hspec.2.1 v ht
  have hcard : (ReusableSample.fresh R (selectionBits selected) ∅ v).card =
      (ReusableSample.fresh (ambientPoolRows I bits cfg) (selectionBits selected) ∅ v).card := by
    rw [← Finset.card_image_of_injective _ hinj, image_fresh_empty R _ v f hinj, hrows]
  have hc : Fintype.card (RetainedIndex bits cfg) = (PortGraph.retained I bits cfg).card := by
    rw [← Nat.card_eq_fintype_card, retainedIndex_card I bits cfg hT hnd]
  simpa only [hc, hcard] using hh

theorem finalUnion_covered (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (selected : Selection (Fin n))
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value)
    (x : RetainedIndex bits cfg) :
    x ∈ ReusableSample.finalUnion (retainedRows I.weight bits cfg.terminals cfg.key cfg.scale)
      (selectionBits selected) ∅ ↔ cfg.covered.get (cfg.terminals.get x.val) = true := by
  rw [ReusableSample.mem_finalUnion, hD]
  simp [selectionBits, retainedRows, ReusableSample.OracleProgram.rows,
    LocalAccess.covered_get, PortGraph.radius]

/-- The retained-label specification is transported to actual ambient point
IDs. Injectivity uses the FIXED public terminal list, not the sampled records. -/
theorem poolGood_residual (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (selected : Selection (Fin n))
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value)
    (hgood : PoolGood I.weight bits p cfg.terminals cfg.key cfg.scale (some (selected, cfg.covered))) :
    ∀ v, ((PortGraph.residualNeighbors I bits cfg v).card : ℝ) ≤
      4 * (PortGraph.retained I bits cfg).card / p.t := by
  letI : DecidableEq (RetainedIndex bits cfg) := Classical.decEq _
  letI : DecidableEq (Fin n) := Classical.decEq _
  let R := retainedRows I.weight bits cfg.terminals cfg.key cfg.scale
  let T := selectionBits selected
  have hmem (v : Fin n) (x : RetainedIndex bits cfg) :
      x ∈ R v \ ReusableSample.finalUnion R T ∅ ↔
        cfg.terminals.get x.val ∈ PortGraph.residualNeighbors I bits cfg v := by
    have hr := retainedIndex_mem I bits cfg hT x
    have ht := PortGraph.retained_subset I bits cfg hr
    rw [Finset.mem_sdiff, finalUnion_covered I bits cfg selected hD x,
      PortGraph.mem_residualNeighbors]
    rw [PortGraph.not_mem_removed I cfg ht]
    simp only [R, retainedRows, ReusableSample.OracleProgram.rows, Finset.mem_filter,
      Finset.mem_univ, true_and, Instance.weight_mk, PortGraph.radius, hr]
    cases cfg.covered.get (cfg.terminals.get x.val) <;> simp
  have himage (v : Fin n) :
      (R v \ ReusableSample.finalUnion R T ∅).image (fun x => cfg.terminals.get x.val) =
        PortGraph.residualNeighbors I bits cfg v := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hmem v x).mp hx
    · intro hy
      obtain ⟨x, hx⟩ := retainedIndex_exists I bits cfg hT y
        ((PortGraph.mem_residualNeighbors I bits cfg v y).mp hy).1
      exact Finset.mem_image.mpr ⟨x, (hmem v x).mpr (hx ▸ hy), hx⟩
  have hinj : Function.Injective (fun x : RetainedIndex bits cfg => cfg.terminals.get x.val) :=
    (terminal_injective cfg hnd).comp Subtype.val_injective
  have hspec : ReusableSample.Specification R p.t T := hgood
  intro v
  have hh := hspec.2.2 v
  rw [← Finset.card_image_of_injective _ hinj, himage] at hh
  have hc : Fintype.card (RetainedIndex bits cfg) = (PortGraph.retained I bits cfg).card := by
    rw [← Nat.card_eq_fintype_card, retainedIndex_card I bits cfg hT hnd]
  simpa only [hc] using hh

theorem poolGood_residual_nat (I : Instance (Fin n)) (bits : Q → Bool) (p : Parameters)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (selected : Selection (Fin n))
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value)
    (hgood : PoolGood I.weight bits p cfg.terminals cfg.key cfg.scale (some (selected, cfg.covered)))
    (P : ℕ) (hP : 4 * ((PortGraph.retained I bits cfg).card : ℝ) / p.t ≤ P) :
    ∀ v, (PortGraph.residualNeighbors I bits cfg v).card ≤ P := by
  intro v
  exact_mod_cast (poolGood_residual I bits p cfg hT hnd selected hD hgood v).trans hP

end SteinerUpperBound.LargeCoverProgram

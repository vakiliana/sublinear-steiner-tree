module

public import SteinerUpperBound.FiniteMST.Program
public import SteinerUpperBound.MSTLocality
public import SteinerUpperBound.TreeGeometry.Basic
public import SteinerUpperBound.SetSystem.Rank

@[expose] public section

namespace SteinerUpperBound.FiniteMST

open SteinerLowerBound
open scoped Classical

variable {U V : Type*} [Fintype U] [Fintype V]

noncomputable def labels (f : U → V) : Finset V := Finset.univ.image f

omit [Fintype V] in
theorem mem_labels (f : U → V) (x : V) : x ∈ labels f ↔ ∃ i, f i = x := by simp [labels]

def pullWeight (w : Sym2 V → ℝ) (f : U → V) (e : Sym2 U) : ℝ := w (e.map f)

omit [Fintype V] in
theorem graph_comap_map (G : SimpleGraph V) (f : U → V)
    (hT : Network.TerminalOnly (labels f) G) : (G.comap f).map f = G := by
  ext x y
  constructor
  · intro h
    obtain ⟨_, i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj' f _ x y).mp h
    exact hij
  · intro h
    obtain ⟨hx, hy⟩ := hT x y h
    obtain ⟨i, rfl⟩ := (mem_labels f x).mp hx
    obtain ⟨j, rfl⟩ := (mem_labels f y).mp hy
    exact (SimpleGraph.map_adj' f _ _ _).mpr ⟨h.ne, i, j, h, rfl, rfl⟩

theorem value_image (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (f : U → V) (hf : Function.Injective f) :
    TerminalMST.value (pullWeight w f) (Finset.univ : Finset U) =
      TerminalMST.value w (labels f) := by
  have hwp : ∀ e, 0 ≤ pullWeight w f e := fun _ => hw _
  have hforward : TerminalMST.value w (labels f) ≤
      TerminalMST.value (pullWeight w f) (Finset.univ : Finset U) := by
    let H := TerminalMST.graph (pullWeight w f) (Finset.univ : Finset U)
    have hfeas : Network.Feasible (labels f) (H.map f) := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := (mem_labels f x).mp hx
      obtain ⟨j, rfl⟩ := (mem_labels f y).mp hy
      exact TreeGeometry.reachable_map
        (TerminalMST.graph_feasible _ _ i (Finset.mem_univ _) j (Finset.mem_univ _)) f
    have hterm : Network.TerminalOnly (labels f) (H.map f) := by
      intro x y h
      obtain ⟨_, i, j, _, rfl, rfl⟩ := (SimpleGraph.map_adj' f H x y).mp h
      exact ⟨(mem_labels f _).mpr ⟨i, rfl⟩, (mem_labels f _).mpr ⟨j, rfl⟩⟩
    calc
      _ ≤ GraphCost.cost w (H.map f) := Network.minimum_le _ _ _ _ ⟨hfeas, hterm⟩
      _ = GraphCost.cost (pullWeight w f) H := TreeGeometry.cost_map_eq H f hf w
      _ = _ := (TerminalMST.value_eq_cost _ _ hwp).symm
  have hback : TerminalMST.value (pullWeight w f) (Finset.univ : Finset U) ≤
      TerminalMST.value w (labels f) := by
    let G := TerminalMST.graph w (labels f)
    let H := G.comap f
    have hmap : H.map f = G := graph_comap_map G f (TerminalMST.graph_terminalOnly _ _)
    have hfeas : Network.Feasible (Finset.univ : Finset U) H := by
      intro i _ j _
      have hh := SetSystem.quotient_reachable (⊥ : SimpleGraph U) H f
        (by intro x y; simp [hf.eq_iff]) i j
      rw [bot_sup_eq, hmap] at hh
      exact hh.mpr (TerminalMST.graph_feasible w (labels f)
        (f i) ((mem_labels f _).mpr ⟨i, rfl⟩)
        (f j) ((mem_labels f _).mpr ⟨j, rfl⟩))
    have hterm : Network.TerminalOnly (Finset.univ : Finset U) H :=
      fun x y _ => ⟨Finset.mem_univ x, Finset.mem_univ y⟩
    calc
      _ ≤ GraphCost.cost (pullWeight w f) H := Network.minimum_le _ _ _ _ ⟨hfeas, hterm⟩
      _ = GraphCost.cost w (H.map f) := (TreeGeometry.cost_map_eq H f hf w).symm
      _ = GraphCost.cost w G := by rw [hmap]
      _ = _ := (TerminalMST.value_eq_cost _ _ hw).symm
  exact le_antisymm hback hforward

theorem on_labels_correct {m : ℕ} (d : Matrix m)
    (hd₀ : ∀ i j, 0 ≤ SmallCoverProgram.Closure.entry d i j)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (f : Fin m → V) (hf : Function.Injective f)
    (hd : ∀ i j, i ≠ j → SmallCoverProgram.Closure.entry d i j = w (Sym2.mk (f i) (f j))) :
    (run d).value = TerminalMST.value w (labels f) := by
  rw [program_correct d hd₀]
  apply Eq.trans _ (value_image w hw f hf)
  apply TerminalMST.value_congr
  intro e he
  induction e using Sym2.inductionOn with
  | _ i j =>
      have hij := ((Network.completeOn_adj Finset.univ i j).mp
        ((SimpleGraph.mem_edgeSet _).mp he)).1
      simp only [weight_mk, pairWeight, pullWeight, Sym2.map_mk]
      split_ifs
      · exact hd i j hij
      · simpa only [Sym2.eq_swap] using hd j i hij.symm

end SteinerUpperBound.FiniteMST

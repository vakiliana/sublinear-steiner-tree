module

public import SteinerLowerBound.GraphCost
public import SteinerLowerBound.LawOperations

@[expose] public section

namespace SteinerUpperBound

open SteinerLowerBound
open scoped Classical BigOperators

structure Instance (V : Type*) where
  metric : MetricSpace V
  terminals : Finset V

namespace Instance

variable {V : Type*}

noncomputable def distance (I : Instance V) (x y : V) : ℝ :=
  @dist V I.metric.toDist x y

theorem distance_self (I : Instance V) (x : V) : I.distance x x = 0 := by
  letI := I.metric
  exact dist_self x

theorem distance_comm (I : Instance V) (x y : V) :
    I.distance x y = I.distance y x := by
  letI := I.metric
  exact dist_comm x y

theorem distance_nonneg (I : Instance V) (x y : V) : 0 ≤ I.distance x y := by
  letI := I.metric
  exact dist_nonneg

theorem distance_triangle (I : Instance V) (x y z : V) :
    I.distance x z ≤ I.distance x y + I.distance y z := by
  letI := I.metric
  exact dist_triangle x y z

theorem distance_pos (I : Instance V) (x y : V) (hxy : x ≠ y) :
    0 < I.distance x y := by
  letI := I.metric
  exact dist_pos.mpr hxy

noncomputable def weight (I : Instance V) : Sym2 V → ℝ :=
  Sym2.lift ⟨I.distance, I.distance_comm⟩

@[simp]
theorem weight_mk (I : Instance V) (x y : V) :
    I.weight (Sym2.mk x y) = I.distance x y := by
  rw [weight, Sym2.lift_mk]

theorem weight_nonneg (I : Instance V) (e : Sym2 V) : 0 ≤ I.weight e := by
  rcases e with ⟨x, y⟩
  simpa only [weight_mk] using I.distance_nonneg x y

end Instance

namespace Network

variable {V : Type*}

def Feasible (T : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, G.Reachable x y

def TerminalOnly (T : Finset V) (G : SimpleGraph V) : Prop :=
  ∀ x y, G.Adj x y → x ∈ T ∧ y ∈ T

noncomputable def completeOn (T : Finset V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => x ∈ T ∧ y ∈ T)

theorem completeOn_adj (T : Finset V) (x y : V) :
    (completeOn T).Adj x y ↔ x ≠ y ∧ x ∈ T ∧ y ∈ T := by
  simp [completeOn, SimpleGraph.fromRel, and_comm, and_left_comm, and_assoc]

theorem completeOn_feasible (T : Finset V) : Feasible T (completeOn T) := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.refl x
  · exact ((completeOn_adj T x y).mpr ⟨hxy, hx, hy⟩).reachable

theorem completeOn_terminalOnly (T : Finset V) : TerminalOnly T (completeOn T) := by
  intro x y hxy
  exact ((completeOn_adj T x y).mp hxy).2

theorem bot_feasible (T : Finset V) (hT : T.card ≤ 1) : Feasible T ⊥ := by
  intro x hx y hy
  have hxy : x = y := Finset.card_le_one.mp hT x hx y hy
  subst y
  exact SimpleGraph.Reachable.refl x

theorem bot_terminalOnly (T : Finset V) : TerminalOnly T ⊥ := by
  intro x y hxy
  exact False.elim hxy

variable [Fintype V]

theorem cost_bot (w : Sym2 V → ℝ) : GraphCost.cost w (⊥ : SimpleGraph V) = 0 := by
  unfold GraphCost.cost
  apply Finset.sum_eq_zero
  intro e he
  have hbad : False := by
    simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_bot,
      Set.mem_empty_iff_false] using he
  exact hbad.elim

noncomputable def values (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop) : Finset ℝ :=
  (Finset.univ.filter P).image (GraphCost.cost w)

theorem values_nonempty (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) : (values w P).Nonempty := by
  obtain ⟨G, hG⟩ := hP
  exact ⟨GraphCost.cost w G, Finset.mem_image.mpr
    ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, rfl⟩⟩

noncomputable def minimum (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) : ℝ :=
  (values w P).min' (values_nonempty w P hP)

theorem minimum_le (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) (G : SimpleGraph V) (hG : P G) :
    minimum w P hP ≤ GraphCost.cost w G :=
  Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨G, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG⟩, rfl⟩)

theorem minimum_attained (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) :
    ∃ G, P G ∧ GraphCost.cost w G = minimum w P hP := by
  have hm := Finset.min'_mem (values w P) (values_nonempty w P hP)
  obtain ⟨G, hG, he⟩ := Finset.mem_image.mp hm
  exact ⟨G, (Finset.mem_filter.mp hG).2, he⟩

theorem minimum_nonneg (w : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) (hw : ∀ e, 0 ≤ w e) :
    0 ≤ minimum w P hP := by
  obtain ⟨G, _, hG⟩ := minimum_attained w P hP
  rw [← hG]
  exact Finset.sum_nonneg fun e _ => hw e

theorem minimum_mono (w w' : Sym2 V → ℝ) (P : SimpleGraph V → Prop)
    (hP : ∃ G, P G) (hww' : ∀ e, w e ≤ w' e) :
    minimum w P hP ≤ minimum w' P hP := by
  obtain ⟨G, hG, he⟩ := minimum_attained w' P hP
  apply (minimum_le w P hP G hG).trans
  rw [← he]
  exact Finset.sum_le_sum fun e _ => hww' e

end Network

namespace Instance

variable {V : Type*} [Fintype V]

noncomputable def optimum (I : Instance V) : ℝ :=
  Network.minimum I.weight (Network.Feasible I.terminals)
    ⟨Network.completeOn I.terminals, Network.completeOn_feasible _⟩

noncomputable def mst (I : Instance V) : ℝ :=
  Network.minimum I.weight
    (fun G => Network.Feasible I.terminals G ∧ Network.TerminalOnly I.terminals G)
    ⟨Network.completeOn I.terminals, Network.completeOn_feasible _,
      Network.completeOn_terminalOnly _⟩

theorem optimum_attained (I : Instance V) :
    ∃ G, Network.Feasible I.terminals G ∧ GraphCost.cost I.weight G = I.optimum :=
  Network.minimum_attained _ _ _

theorem mst_attained (I : Instance V) :
    ∃ G, Network.Feasible I.terminals G ∧ Network.TerminalOnly I.terminals G ∧
      GraphCost.cost I.weight G = I.mst := by
  obtain ⟨G, hG, he⟩ := Network.minimum_attained I.weight
    (fun G => Network.Feasible I.terminals G ∧ Network.TerminalOnly I.terminals G) _
  exact ⟨G, hG.1, hG.2, he⟩

theorem optimum_le (I : Instance V) (G : SimpleGraph V) (hG : Network.Feasible I.terminals G) :
    I.optimum ≤ GraphCost.cost I.weight G :=
  Network.minimum_le _ _ _ G hG

theorem mst_le (I : Instance V) (G : SimpleGraph V)
    (hG : Network.Feasible I.terminals G) (hT : Network.TerminalOnly I.terminals G) :
    I.mst ≤ GraphCost.cost I.weight G :=
  Network.minimum_le _ _ _ G ⟨hG, hT⟩

theorem optimum_nonneg (I : Instance V) : 0 ≤ I.optimum :=
  Network.minimum_nonneg _ _ _ I.weight_nonneg

theorem mst_nonneg (I : Instance V) : 0 ≤ I.mst :=
  Network.minimum_nonneg _ _ _ I.weight_nonneg

theorem optimum_le_mst (I : Instance V) : I.optimum ≤ I.mst := by
  obtain ⟨G, hG, _, he⟩ := I.mst_attained
  exact (I.optimum_le G hG).trans_eq he

theorem optimum_eq_zero (I : Instance V) (hT : I.terminals.card ≤ 1) : I.optimum = 0 := by
  apply le_antisymm _ I.optimum_nonneg
  have h := I.optimum_le ⊥ (Network.bot_feasible _ hT)
  simpa only [Network.cost_bot] using h

theorem mst_eq_zero (I : Instance V) (hT : I.terminals.card ≤ 1) : I.mst = 0 := by
  apply le_antisymm _ I.mst_nonneg
  have h := I.mst_le ⊥ (Network.bot_feasible _ hT) (Network.bot_terminalOnly _)
  simpa only [Network.cost_bot] using h

end Instance

end SteinerUpperBound

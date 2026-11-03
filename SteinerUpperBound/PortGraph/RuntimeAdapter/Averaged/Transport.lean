module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Roots
public import SteinerUpperBound.Matching.Padded.CounterTail
public import SteinerUpperBound.Matching.Padded.ClosedCost

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

theorem copies_le_sum_degree (G : Matching.Graph V E) :
    Fintype.card E ≤ ∑ v, G.degree v := by
  let f : E → Σ v, {e : E // G.Incident e v} :=
    fun e => ⟨G.left e, e, G.incident_left e⟩
  have hf : Function.Injective f := by
    intro e e' he
    exact congrArg (fun x : Σ v, {e : E // G.Incident e v} => x.2.val) he
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_sigma, Fintype.card_subtype, Matching.Graph.degree] using hc

theorem publicPrice_initiation {G : Matching.Graph V E} (S : Slots G) (A : Account S)
    (g : ℝ) (hg : 0 < g) :
    ((Fintype.card V : ℝ) / g) * Account.publicPrice S A ≤
      initiationAverage (fun v => A.Cstar * (1 + (G.degree v : ℝ)) + A.W v) g := by
  by_cases hm : Fintype.card V = 0
  · rw [initiation_empty _ _ hm]
    simp only [hm, Nat.cast_zero, zero_div, zero_mul, le_refl]
  · have hm' : (0 : ℝ) < Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hm
    unfold Account.publicPrice initiationAverage
    rw [normalized_budget_algebra g _ _ _ _ hg hm', sum_price]
    apply (div_le_div_iff_of_pos_right hg).mpr
    have hd : (Fintype.card E : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
      exact_mod_cast copies_le_sum_degree G
    nlinarith [mul_le_mul_of_nonneg_left hd A.Cstar_nonneg]

theorem closed_model_initiation {G : Matching.Graph V E} (S : Slots G) (P : Parameters S)
    (A : Account S) (g : ℝ) (hg : 0 < g) :
    initiationAverage (Execution.goodCost S P A) g ≤
      Parameters.costFactor S P *
        initiationAverage (fun v => A.Cstar * (1 + (G.degree v : ℝ)) + A.W v) g := by
  by_cases hm : Fintype.card V = 0
  · simp only [initiation_empty _ _ hm, mul_zero, le_refl]
  · have hm' := Nat.pos_of_ne_zero hm
    let _ : Nonempty V := Fintype.card_pos_iff.mp hm'
    have he := Execution.expected_goodCost_le S P A
    rw [← uniformAverage_eq] at he
    rw [root_normalization _ _ hg hm']
    calc
      _ ≤ ((Fintype.card V : ℝ) / g) * (Parameters.costFactor S P * Account.publicPrice S A) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = Parameters.costFactor S P * (((Fintype.card V : ℝ) / g) * Account.publicPrice S A) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (publicPrice_initiation S A g hg) (by
        unfold Parameters.costFactor
        positivity)

variable {n k b B : ℕ} {Q : Type}

theorem answer_counter_test {Vertex Label M T : Type*} (C : Runtime.Config Vertex)
    (I : Runtime.Primitives C.length Label M T) (m : M → ℝ) (bits : T → Bool)
    (root : Vertex) (counter : Causal.Counter) (f : ℝ → ℝ) :
    (Runtime.answer C I root).evaluate m bits (fun o => f (counter.value o)) =
      (Runtime.vertex C I root).evaluate m bits (fun o => f (counter.value o)) := by
  rw [Runtime.answer, Code.evaluate_map]
  rfl

theorem oracle_counter_test (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (Nstar : ℕ) (cache : Cache Q) (counter : Causal.Counter) (f : ℝ → ℝ) :
    (oracle cfg Nstar (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits (fun o => f (counter.value o)) =
      (Runtime.vertex (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate
          I.weight bits (fun o => f (counter.value o + 12 * counter.work)) := by
  rw [oracle, frame_head I bits cfg b B hT C]
  simp only [Code.evaluate]
  rw [Code.evaluate_bind]
  calc
    _ = (Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate
          I.weight bits (fun o => f (counter.value o + 12 * counter.work)) := by
      apply congrArg ((Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate I.weight bits)
      funext o
      simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure]
      congr 1
      simp only [Causal.Counter.value]
      push_cast
      ring
    _ = _ := answer_counter_test (config n b B k Nstar)
      (primitives cfg (canonicalFrame I cfg b B C.val) cache) I.weight bits
      (rootEmbedding I bits cfg B hT C) counter (fun z => f (z + 12 * counter.work))

inductive CounterKind where
  | ordinary
  | positive

noncomputable def CounterKind.counter : CounterKind → Causal.Counter
  | .ordinary => workCounter
  | .positive => positiveCounter

noncomputable def CounterKind.account (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    Account (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd) :=
  match kind with
  | .ordinary => workAccount I bits cfg hT hnd
  | .positive => positiveAccount I bits cfg hT hnd

noncomputable def CounterKind.price (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) : ℝ :=
  let A := kind.account (b := b) (B := B) I bits cfg hT hnd
  A.Cstar * (1 + ((graph I bits cfg b B).degree C : ℝ)) + A.W C

noncomputable def CounterKind.modelCost (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) : ℝ :=
  Execution.goodCost (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
    (parameters I bits cfg hT hnd) (kind.account I bits cfg hT hnd) C

noncomputable def costFactor (n k b B : ℕ) : ℝ :=
  (2 : ℝ) ^ 64 * (Nat.log 2 (publicSize n k b B) + 1 : ℝ) ^ 8

noncomputable def rankError (n k b B : ℕ) : ℝ := 1 / (publicSize n k b B : ℝ) ^ 30

theorem costFactor_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Parameters.costFactor (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
      (parameters I bits cfg hT hnd) = costFactor n k b B := by
  simp only [Parameters.costFactor, Parameters.logarithm, parameters, costFactor, Nat.cast_add, Nat.cast_one]

theorem callback_counter_tail (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (cache : Cache Q) (hc : Cache.Correct bits cache)
    (threshold : ℝ) (ht : 0 < threshold) :
    (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if threshold + 12 * kind.counter.work ≤ kind.counter.value o then 1 else 0) ≤
      rankError n k b B + kind.modelCost (b := b) I bits cfg hT hnd C / threshold := by
  let P := parameters (b := b) (B := B) I bits cfg hT hnd
  let J := presentation I bits cfg hT hnd P (publicSize n k b B) rfl
  let A := kind.account (b := b) (B := B) I bits cfg hT hnd
  let prim := primitives cfg (canonicalFrame I cfg b B C.val) cache
  let K := contract I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  let D := deterministic I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  have R : J.Resources prim I.weight bits K A kind.counter := by
    cases kind
    · exact workResources I bits cfg hT hnd P (publicSize n k b B) rfl
        (canonicalFrame I cfg b B C.val) cache C rfl hc
    · exact positiveResources I bits cfg hT hnd P (publicSize n k b B) rfl
        (canonicalFrame I cfg b B C.val) cache C rfl hc
  rw [oracle_counter_test I bits cfg hT C (publicSize n k b B) cache kind.counter
    (fun z => if threshold + 12 * kind.counter.work ≤ z then 1 else 0)]
  simp only [add_le_add_iff_right]
  exact Presentation.vertex_counter_tail J prim I.weight bits K D A kind.counter R C threshold ht

noncomputable def callbackTail (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (caches : Vertex I bits cfg B → Cache Q) (threshold : ℝ) (C : Vertex I bits cfg B) : ℝ :=
  (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) (caches C)).evaluate I.weight bits
    (fun o => if threshold + 12 * kind.counter.work ≤ kind.counter.value o then 1 else 0)

theorem initiated_counter_tail_model (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (threshold : ℝ) (ht : 0 < threshold) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card ≤
      ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) * rankError n k b B +
        initiationAverage (kind.modelCost (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card / threshold := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun C _ =>
    callback_counter_tail (b := b) kind I bits cfg hT hnd C (caches C) (hc C) threshold ht)
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg (retained I bits cfg).card)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div] at hd
  unfold initiationAverage callbackTail
  convert hd using 1
  ring

theorem model_cost_price (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (kind.modelCost (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card ≤
      costFactor n k b B *
        initiationAverage (kind.price (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card := by
  have h := closed_model_initiation (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
    (parameters (b := b) (B := B) I bits cfg hT hnd)
    (kind.account (b := b) (B := B) I bits cfg hT hnd)
    ((retained I bits cfg).card : ℝ) (by exact_mod_cast hg)
  rw [costFactor_eq I bits cfg hT hnd] at h
  exact h

theorem initiated_counter_tail (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (hg : 0 < (retained I bits cfg).card) (threshold : ℝ) (ht : 0 < threshold) :
    initiationAverage (callbackTail (b := b) kind I bits cfg caches threshold) (retained I bits cfg).card ≤
      ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) * rankError n k b B +
        costFactor n k b B *
          initiationAverage (kind.price (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card / threshold :=
  (initiated_counter_tail_model kind I bits cfg hT hnd caches hc threshold ht).trans
    (add_le_add (le_refl _) (div_le_div_of_nonneg_right
      (model_cost_price (b := b) (B := B) kind I bits cfg hT hnd hg) (le_of_lt ht)))

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

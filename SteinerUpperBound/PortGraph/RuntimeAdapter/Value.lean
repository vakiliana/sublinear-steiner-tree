module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Reuse
public import SteinerUpperBound.Matching.Padded.ValueKernel

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {n k b B : ℕ} {Q : Type}

def publicSize (n k b B : ℕ) : ℕ := n * (b * B * k + 1) + 2

/-- The model size is computed entirely from public array lengths and caps,
not the unknown retained graph. -/
noncomputable def parameters (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd) where
  Nstar := publicSize n k b B
  two_le := by unfold publicSize; omega
  size_le := by
    have hg : (retained I bits cfg).card ≤ n := by
      simpa only [Fintype.card_fin] using (Finset.card_le_univ (s := retained I bits cfg))
    have hm := (vertices_card_le I bits cfg B).trans hg
    have ht : (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd).totalSlots =
        Fintype.card (Vertex I bits cfg B) * (b * B * k) := by
      change (∑ _ : Vertex I bits cfg B, b * B * k) = _
      simp
    rw [ht]
    unfold publicSize
    have hp := Nat.mul_le_mul_right (b * B * k + 1) hm
    nlinarith [hp]

noncomputable def builder (key : Fin n → Q) (scale : ℝ) (terminals : Vector (Fin n) k) (B : ℕ) :
    (covered : Vector Bool n) → (d : ℕ) → Frame n d B → Cache Q →
      Code (Sym2 (Fin n)) Q (Bool × Cache Q) :=
  fun covered d frame cache =>
    oracle { key := key, scale := scale, terminals := terminals, covered := covered }
      (publicSize n k d B) frame cache

/-- Generic wrappers keep the finite-rank instance used by `Rank.uniform`
fixed before specializing to metric-dependent subtype carriers. -/
noncomputable def strictMean {V E : Type*} [Fintype E] (G : Matching.Graph V E)
    (v : V) (f : Bool → ℝ) : ℝ :=
  (Matching.Rank.uniform (E := E)).expect (fun rank => f (G.vertexOracle rank v).value.isSome)

noncomputable def strictProbability {V E : Type*} [Fintype E] (G : Matching.Graph V E)
    (v : V) (event : Set Bool) : ℝ :=
  (Matching.Rank.uniform (E := E)).prob {rank | (G.vertexOracle rank v).value.isSome ∈ event}

theorem strictProbability_eq {V E : Type*} [Fintype E] (G : Matching.Graph V E)
    (v : V) (event : Set Bool) :
    strictProbability G v event = strictMean G v (fun value => if value ∈ event then 1 else 0) :=
  Law.prob_eq_expect _ _

theorem oracle_evaluate (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (Nstar : ℕ) (cache : Cache Q) (F : Bool × Cache Q → ℝ) :
    (oracle cfg Nstar (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits (fun o => F o.value) =
      (Matching.Padded.Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate
          I.weight bits (fun o => F (o.value.1, o.value.2.cache)) := by
  rw [oracle, frame_head I bits cfg b B hT C]
  simp only [Code.evaluate, Outcome.add]
  rw [Code.evaluate_bind]
  rfl

theorem oracle_counter (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (Nstar : ℕ) (cache : Cache Q) (counter : Matching.Padded.Causal.Counter) :
    (oracle cfg Nstar (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits counter.value =
      (Matching.Padded.Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate
          I.weight bits counter.value + 12 * counter.work := by
  rw [oracle, frame_head I bits cfg b B hT C]
  simp only [Code.evaluate]
  rw [Code.evaluate_bind]
  calc
    _ = (Matching.Padded.Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate
          I.weight bits (fun o => counter.value o + 12 * counter.work) := by
      apply congrArg ((Matching.Padded.Runtime.answer (config n b B k Nstar)
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate I.weight bits)
      funext o
      simp only [Code.evaluate, Outcome.add, Outcome.combine, Outcome.pure, Matching.Padded.Causal.Counter.value]
      push_cast
      ring
    _ = _ := by rw [Code.evaluate_add, Code.evaluate_const]

/-- Derived by instantiating the matching owner's actual CODE theorem with the
proved concrete metric primitives, never by assuming a VO kernel certificate. -/
theorem oracle_mean_error (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (cache : Cache Q) (hc : Cache.Correct bits cache)
    (f : Bool → ℝ) (hf₀ : ∀ value, 0 ≤ f value) (hf₁ : ∀ value, f value ≤ 1) :
    |(oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => f o.value.1) -
      strictMean (graph I bits cfg b B) C f| ≤
      1 / (publicSize n k b B : ℝ) ^ 30 := by
  let P := parameters (b := b) (B := B) I bits cfg hT hnd
  let J := presentation I bits cfg hT hnd P (publicSize n k b B) rfl
  let A := workAccount (b := b) (B := B) I bits cfg hT hnd
  let prim := primitives cfg (canonicalFrame I cfg b B C.val) cache
  let K := contract I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  let D := deterministic I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  have R := workResources I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  have h := Matching.Padded.Presentation.answer_mean_error J prim I.weight bits K D A workCounter R C f hf₀ hf₁
  have he := oracle_evaluate (b := b) I bits cfg hT C (publicSize n k b B) cache (fun answer => f answer.1)
  rw [he]
  exact h

theorem oracle_event_error (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) (event : Set Bool) :
    |(oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if o.value.1 ∈ event then 1 else 0) -
      strictProbability (graph I bits cfg b B) C event| ≤
      1 / (publicSize n k b B : ℝ) ^ 30 := by
  rw [strictProbability_eq]
  exact oracle_mean_error I bits cfg hT hnd C cache hc
    (fun value => if value ∈ event then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)

theorem oracle_preserves (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    Matching.Padded.Causal.Ensures I.weight bits
      (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache)
      (fun answer => Cache.Correct bits answer.2) := by
  let P := parameters (b := b) (B := B) I bits cfg hT hnd
  let J := presentation I bits cfg hT hnd P (publicSize n k b B) rfl
  let A := workAccount (b := b) (B := B) I bits cfg hT hnd
  let prim := primitives cfg (canonicalFrame I cfg b B C.val) cache
  let K := contract I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  let D := deterministic I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  have R := workResources I bits cfg hT hnd P (publicSize n k b B) rfl
    (canonicalFrame I cfg b B C.val) cache C rfl hc
  have hp := Matching.Padded.Presentation.answer_preserves J prim I.weight bits K D A workCounter R C
  intro F hF
  change (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
    (fun o => F o.value) = 0
  rw [oracle_evaluate (b := b) I bits cfg hT C (publicSize n k b B) cache F]
  exact hp (fun answer => F (answer.1, answer.2.cache)) (fun answer ha => hF _ ha.1)

theorem oracle_cache_failure_zero (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) (C : Vertex I bits cfg B)
    (cache : Cache Q) (hc : Cache.Correct bits cache) :
    (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
      (fun o => if Cache.Correct bits o.value.2 then 0 else 1) = 0 := by
  exact oracle_preserves I bits cfg hT hnd C cache hc
    (fun answer => if Cache.Correct bits answer.2 then 0 else 1) (fun _ h => by simp [h])

end SteinerUpperBound.PortGraph.RuntimeAdapter

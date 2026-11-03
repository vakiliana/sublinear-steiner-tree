module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Bounds
public import SteinerUpperBound.Matching.Padded.RuntimeTruncatedCost

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical BigOperators

variable {n k b B : ℕ} {Q : Type}

def CounterKind.unit (kind : CounterKind) (n k b B : ℕ) : ℕ :=
  match kind with
  | .ordinary => workCap n k b B
  | .positive => B + 2

def truncationExponent (n k b B : ℕ) : ℕ := 100 + 20 * (Nat.log 2 (publicSize n k b B) + 1)

def runtimeLimit (kind : CounterKind) (n k b B : ℕ) : ℕ :=
  kind.unit n k b B * 2 ^ truncationExponent n k b B

def counterCeiling (kind : CounterKind) (n k b B : ℕ) : ℕ :=
  runtimeLimit kind n k b B + match kind with | .ordinary => 12 | .positive => 0

noncomputable def truncatedFactor (n k b B : ℕ) : ℝ :=
  (2 : ℝ) ^ 128 * (Nat.log 2 (publicSize n k b B) + 1 : ℝ) ^ 9

theorem unit_pos (kind : CounterKind) (n k b B : ℕ) : 0 < kind.unit n k b B := by
  cases kind <;> dsimp only [CounterKind.unit, workCap] <;> positivity

theorem account_Cstar_eq (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    (kind.account (b := b) (B := B) I bits cfg hT hnd).Cstar = (kind.unit n k b B : ℝ) := by
  cases kind
  · rfl
  · simp only [CounterKind.account, positiveAccount, CounterKind.unit, Nat.cast_add, Nat.cast_ofNat]

theorem runtimeLimit_eq (kind : CounterKind) (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Account.truncationLimit (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
      (parameters I bits cfg hT hnd) (kind.account I bits cfg hT hnd) = (runtimeLimit kind n k b B : ℝ) := by
  simp only [Account.truncationLimit, account_Cstar_eq, Parameters.truncationScale,
    Parameters.truncationExponent, Parameters.logarithm, parameters, runtimeLimit,
    truncationExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem counterCeiling_eq (kind : CounterKind) (n k b B : ℕ) :
    (counterCeiling kind n k b B : ℝ) = (runtimeLimit kind n k b B : ℝ) + 12 * kind.counter.work := by
  cases kind <;> simp only [counterCeiling, CounterKind.counter, workCounter, positiveCounter,
    Nat.cast_add, Nat.cast_ofNat, mul_one, mul_zero, add_zero]

theorem truncatedFactor_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (hnd : cfg.terminals.toList.Nodup) :
    Parameters.truncatedFactor (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
      (parameters I bits cfg hT hnd) = truncatedFactor n k b B := by
  simp only [Parameters.truncatedFactor, Parameters.logarithm, parameters, truncatedFactor,
    Nat.cast_add, Nat.cast_one]

theorem truncatedFactor_nonneg (n k b B : ℕ) : 0 ≤ truncatedFactor n k b B := by
  unfold truncatedFactor
  positivity

noncomputable def runtimeCallback (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    Code (Sym2 (Fin n)) Q (Bool × Memory Q n b B) :=
  Runtime.answer (config n b B k (publicSize n k b B))
    (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)

theorem oracle_good_counter_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (cache : Cache Q) (counter : Causal.Counter) (L : ℝ) :
    (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if counter.value o ≤ L + 12 * counter.work then counter.value o else 0) ≤
      (runtimeCallback (b := b) I bits cfg hT C cache).evaluate I.weight bits
        (fun o => if counter.value o ≤ L then counter.value o else 0) + 12 * counter.work := by
  rw [oracle_counter_test I bits cfg hT C (publicSize n k b B) cache counter
    (fun z => if z ≤ L + 12 * counter.work then z else 0)]
  simp only [add_le_add_iff_right]
  have ho : 0 ≤ 12 * counter.work := mul_nonneg (by norm_num) counter.work_nonneg
  calc
    _ ≤ (Runtime.vertex (config n b B k (publicSize n k b B))
        (primitives cfg (canonicalFrame I cfg b B C.val) cache) (rootEmbedding I bits cfg B hT C)).evaluate I.weight bits
          (fun o => (if counter.value o ≤ L then counter.value o else 0) + 12 * counter.work) := by
      apply Code.evaluate_mono
      intro o
      split_ifs <;> linarith
    _ = _ := by
      rw [Code.evaluate_add, Code.evaluate_const]
      exact congrArg (fun z : ℝ => z + 12 * counter.work)
        (answer_counter_test (config n b B k (publicSize n k b B))
          (primitives cfg (canonicalFrame I cfg b B C.val) cache) I.weight bits
          (rootEmbedding I bits cfg B hT C) counter (fun z => if z ≤ L then z else 0)).symm

theorem oracle_good_failure_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (hT : cfg.terminals.toList.toFinset = I.terminals)
    (C : Vertex I bits cfg B) (cache : Cache Q) (counter : Causal.Counter) (L : ℝ) :
    (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if ¬ counter.value o ≤ L + 12 * counter.work then 1 else 0) =
      (runtimeCallback (b := b) I bits cfg hT C cache).evaluate I.weight bits
        (fun o => if ¬ counter.value o ≤ L then 1 else 0) := by
  rw [oracle_counter_test I bits cfg hT C (publicSize n k b B) cache counter
    (fun z => if ¬ z ≤ L + 12 * counter.work then 1 else 0)]
  simp only [add_le_add_iff_right]
  exact (answer_counter_test _ _ _ _ _ counter (fun z => if ¬ z ≤ L then 1 else 0)).symm

noncomputable def originalGood (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q)
    (seed : ((oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).compile I.weight).Seed) : Prop :=
  Causal.counterGood I.weight bits (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache)
    kind.counter (counterCeiling kind n k b B) seed

noncomputable def originalGoodCost (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) : ℝ :=
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  (p.compile I.weight).law.expect (fun seed => if originalGood kind I bits cfg C cache seed then
    Causal.counterSeed I.weight bits p kind.counter seed else 0)

noncomputable def originalGoodFailure (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) : ℝ :=
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  (p.compile I.weight).law.prob {seed | ¬ originalGood kind I bits cfg C cache seed}

theorem originalGoodCost_eq (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    originalGoodCost (b := b) kind I bits cfg C cache =
      (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if kind.counter.value o ≤ (counterCeiling kind n k b B : ℝ) then kind.counter.value o else 0) :=
  Causal.counterGood_cost _ _ _ _ _

theorem originalGoodFailure_eq (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    originalGoodFailure (b := b) kind I bits cfg C cache =
      (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if ¬ kind.counter.value o ≤ (counterCeiling kind n k b B : ℝ) then 1 else 0) :=
  Causal.counterGood_failure _ _ _ _ _

theorem original_good_cost_model (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (C : Vertex I bits cfg B) (cache : Cache Q) (hc : Cache.Correct bits cache) :
    originalGoodCost (b := b) kind I bits cfg C cache ≤
      (kind.unit n k b B : ℝ) + 2 * rankError n k b B * (runtimeLimit kind n k b B : ℝ) +
        2 * (truncationExponent n k b B : ℝ) * kind.modelCost (b := b) I bits cfg hT hnd C +
          12 * kind.counter.work := by
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
  have hC : 0 < A.Cstar := by
    rw [account_Cstar_eq]
    exact_mod_cast unit_pos kind n k b B
  have hraw := Presentation.answer_truncated_counter J prim I.weight bits K D A kind.counter R C hC
  have hlimit : Account.truncationLimit (PortGraph.slots I bits cfg hT hnd) J.parameters A =
      (runtimeLimit kind n k b B : ℝ) := runtimeLimit_eq kind I bits cfg hT hnd
  rw [hlimit] at hraw
  have hraw' :
      (runtimeCallback (b := b) I bits cfg hT C cache).evaluate I.weight bits
        (fun o => if kind.counter.value o ≤ (runtimeLimit kind n k b B : ℝ) then kind.counter.value o else 0) ≤
      (kind.unit n k b B : ℝ) + 2 * rankError n k b B * (runtimeLimit kind n k b B : ℝ) +
        2 * (truncationExponent n k b B : ℝ) * kind.modelCost (b := b) I bits cfg hT hnd C := by
    convert hraw using 1
    · rfl
    · simp only [A, account_Cstar_eq, Parameters.truncationScale, Parameters.truncationExponent,
        Parameters.logarithm, Presentation.parameters, config, parameters, truncationExponent, runtimeLimit, rankError,
        CounterKind.modelCost, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring
  rw [originalGoodCost_eq, counterCeiling_eq]
  exact (oracle_good_counter_le I bits cfg hT C cache kind.counter _).trans
    (add_le_add hraw' (le_refl _))

theorem counterCeiling_polynomial (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup) :
    (counterCeiling kind n k b B : ℝ) ≤
      (2 : ℝ) ^ 120 * (kind.unit n k b B : ℝ) * (publicSize n k b B : ℝ) ^ 20 + 12 * kind.counter.work := by
  let S := PortGraph.slots (b := b) (B := B) I bits cfg hT hnd
  let P := parameters (b := b) (B := B) I bits cfg hT hnd
  have h := mul_le_mul_of_nonneg_left (Parameters.truncationScale_bounds S P).2
    (Nat.cast_nonneg (kind.unit n k b B) : (0 : ℝ) ≤ kind.unit n k b B)
  have he : (kind.unit n k b B : ℝ) * Parameters.truncationScale S P =
      (runtimeLimit kind n k b B : ℝ) := by
    simp only [P, Parameters.truncationScale, Parameters.truncationExponent, Parameters.logarithm,
      parameters, runtimeLimit, truncationExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [he] at h
  rw [counterCeiling_eq]
  have h' : (runtimeLimit kind n k b B : ℝ) ≤
      (2 : ℝ) ^ 120 * (kind.unit n k b B : ℝ) * (publicSize n k b B : ℝ) ^ 20 := by
    simpa only [P, parameters, mul_assoc, mul_comm, mul_left_comm] using h
  exact add_le_add h' (le_refl _)

theorem runtime_uniform_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    [Nonempty (Vertex I bits cfg B)]
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C)) :
    (Law.uniform (Vertex I bits cfg B)).expect (fun C =>
      (runtimeCallback (b := b) I bits cfg hT C (caches C)).evaluate I.weight bits
        (fun o => if kind.counter.value o ≤ (runtimeLimit kind n k b B : ℝ) then kind.counter.value o else 0)) ≤
        truncatedFactor n k b B *
          Account.publicPrice (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)
            (kind.account (b := b) (B := B) I bits cfg hT hnd) ∧
      (Law.uniform (Vertex I bits cfg B)).expect (fun C =>
        (runtimeCallback (b := b) I bits cfg hT C (caches C)).evaluate I.weight bits
          (fun o => if ¬ kind.counter.value o ≤ (runtimeLimit kind n k b B : ℝ) then 1 else 0)) ≤
        1 / (publicSize n k b B : ℝ) ^ 3 := by
  let P := parameters (b := b) (B := B) I bits cfg hT hnd
  let J := presentation I bits cfg hT hnd P (publicSize n k b B) rfl
  let A := kind.account (b := b) (B := B) I bits cfg hT hnd
  let family (C : Vertex I bits cfg B) := primitives cfg (canonicalFrame I cfg b B C.val) (caches C)
  let contracts (C : Vertex I bits cfg B) :=
    contract I bits cfg hT hnd P (publicSize n k b B) rfl
      (canonicalFrame I cfg b B C.val) (caches C) C rfl (hc C)
  let deterministic (C : Vertex I bits cfg B) :=
    RuntimeAdapter.deterministic I bits cfg hT hnd P (publicSize n k b B) rfl
      (canonicalFrame I cfg b B C.val) (caches C) C rfl (hc C)
  have resources (C : Vertex I bits cfg B) :
      J.Resources (family C) I.weight bits (contracts C) A kind.counter := by
    cases kind
    · exact workResources I bits cfg hT hnd P (publicSize n k b B) rfl
        (canonicalFrame I cfg b B C.val) (caches C) C rfl (hc C)
    · exact positiveResources I bits cfg hT hnd P (publicSize n k b B) rfl
        (canonicalFrame I cfg b B C.val) (caches C) C rfl (hc C)
  have hC : 0 < A.Cstar := by
    rw [account_Cstar_eq]
    exact_mod_cast unit_pos kind n k b B
  have hgood := Presentation.family_answer_truncated_counter J I.weight bits A kind.counter
    family contracts deterministic resources hC
  have hbad := Presentation.family_answer_original_good_failure J I.weight bits A kind.counter
    family contracts deterministic resources hC
  have hlimit : Account.truncationLimit (PortGraph.slots I bits cfg hT hnd) J.parameters A =
      (runtimeLimit kind n k b B : ℝ) := runtimeLimit_eq kind I bits cfg hT hnd
  have hfactor : Parameters.truncatedFactor (PortGraph.slots I bits cfg hT hnd) J.parameters =
      truncatedFactor n k b B := truncatedFactor_eq I bits cfg hT hnd
  rw [hlimit, hfactor] at hgood
  simp_rw [Causal.counterGood_failure] at hbad
  rw [hlimit] at hbad
  exact ⟨hgood, hbad⟩

theorem uniform_original_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    [Nonempty (Vertex I bits cfg B)]
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C)) :
    uniformAverage (fun C => originalGoodCost (b := b) kind I bits cfg C (caches C)) ≤
        truncatedFactor n k b B *
          Account.publicPrice (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd) (kind.account I bits cfg hT hnd) +
            12 * kind.counter.work ∧
      uniformAverage (fun C => originalGoodFailure (b := b) kind I bits cfg C (caches C)) ≤
        1 / (publicSize n k b B : ℝ) ^ 3 := by
  have hraw := runtime_uniform_good_accounts (b := b) kind I bits cfg hT hnd caches hc
  have hcost (C : Vertex I bits cfg B) :
      originalGoodCost (b := b) kind I bits cfg C (caches C) ≤
        (runtimeCallback (b := b) I bits cfg hT C (caches C)).evaluate I.weight bits
          (fun o => if kind.counter.value o ≤ (runtimeLimit kind n k b B : ℝ) then kind.counter.value o else 0) +
            12 * kind.counter.work := by
    rw [originalGoodCost_eq, counterCeiling_eq]
    exact oracle_good_counter_le I bits cfg hT C (caches C) kind.counter _
  have hfailure (C : Vertex I bits cfg B) :
      originalGoodFailure (b := b) kind I bits cfg C (caches C) =
        (runtimeCallback (b := b) I bits cfg hT C (caches C)).evaluate I.weight bits
          (fun o => if ¬ kind.counter.value o ≤ (runtimeLimit kind n k b B : ℝ) then 1 else 0) := by
    rw [originalGoodFailure_eq, counterCeiling_eq]
    exact oracle_good_failure_eq I bits cfg hT C (caches C) kind.counter _
  have hsum := (Law.uniform (Vertex I bits cfg B)).expect_mono hcost
  rw [Law.expect_add, Law.expect_const] at hsum
  rw [uniformAverage_eq, uniformAverage_eq]
  refine ⟨hsum.trans (add_le_add hraw.1 (le_refl _)), ?_⟩
  simpa only [hfailure] using hraw.2

theorem initiated_original_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (fun C => originalGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B *
            initiationAverage (kind.price (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => originalGoodFailure (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  by_cases hm : Fintype.card (Vertex I bits cfg B) = 0
  · simp only [initiation_empty _ _ hm, hm, Nat.cast_zero, zero_div, mul_zero, zero_mul,
      add_zero, le_refl, and_self]
  · have hm' := Nat.pos_of_ne_zero hm
    let _ : Nonempty (Vertex I bits cfg B) := Fintype.card_pos_iff.mp hm'
    have hgR : (0 : ℝ) < (retained I bits cfg).card := by exact_mod_cast hg
    have hu := uniform_original_good_accounts (b := b) kind I bits cfg hT hnd caches hc
    have hr : 0 ≤ (Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card := by positivity
    refine ⟨?_, ?_⟩
    · rw [root_normalization _ _ hgR hm']
      calc
        _ ≤ ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
            (truncatedFactor n k b B *
              Account.publicPrice (PortGraph.slots I bits cfg hT hnd) (kind.account I bits cfg hT hnd) +
                12 * kind.counter.work) := mul_le_mul_of_nonneg_left hu.1 hr
        _ = truncatedFactor n k b B *
              (((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
                Account.publicPrice (PortGraph.slots I bits cfg hT hnd) (kind.account I bits cfg hT hnd)) +
            12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) := by ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left
            (publicPrice_initiation (PortGraph.slots I bits cfg hT hnd)
              (kind.account I bits cfg hT hnd) _ hgR) (truncatedFactor_nonneg n k b B)) (le_refl _)
    · rw [root_normalization _ _ hgR hm']
      exact mul_le_mul_of_nonneg_left hu.2 hr

theorem closed_original_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (fun C => originalGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B * geometricBudget kind n B t +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => originalGoodFailure (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  have ha := initiated_original_good_accounts (b := b) kind I bits cfg hT hnd caches hc hg
  have hp := initiated_price_bound kind I bits cfg hT hnd P hres hk hb t ht hinc hprod hg
  exact ⟨ha.1.trans (add_le_add
    (mul_le_mul_of_nonneg_left hp (truncatedFactor_nonneg n k b B)) (le_refl _)), ha.2⟩

theorem calibrated_original_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (t epsilon xi gm : ℝ) (ht : 0 < t) (he : 0 < epsilon) (he₁ : epsilon ≤ 1) (hxi : xi ≤ 1 / 2)
    (hg : 0 < (retained I bits cfg).card)
    (hcal : (1 - xi) * (retained I bits cfg).card ≤ gm)
    (hb : (b : ℝ) ≤ 100 * n / (epsilon * gm) + 1)
    (hB : 10 / epsilon ≤ (B : ℝ)) (hk : k ≤ n) (hsquare : b ^ 2 ≤ 50 * (n + 1))
    (hinc : (b : ℝ) ≤ 4 * n / t + 1)
    (hres : ∀ v, ((residualNeighbors I bits cfg v).card : ℝ) ≤ 4 * (retained I bits cfg).card / t) :
    initiationAverage (fun C => originalGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B * geometricBudget kind n B t +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => originalGoodFailure (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  exact closed_original_good_accounts kind I bits cfg hT hnd caches hc (residualCap I bits cfg t)
    (residualCap_bounds I bits cfg t ht hres).2 hk hsquare t ht hinc
    (calibrated_residual_product I bits cfg t epsilon xi gm ht he he₁ hxi hg hcal hb hB) hg

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

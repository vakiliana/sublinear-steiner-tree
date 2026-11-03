module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged.Truncated

@[expose] public section

namespace SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

open SteinerLowerBound QueryProgram Matching.Padded
open scoped Classical

variable {n k b B : ℕ} {Q : Type}

noncomputable def jointGood (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) (cache : Cache Q)
    (seed : ((oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).compile I.weight).Seed) : Prop :=
  originalGood (b := b) .ordinary I bits cfg C cache seed ∧
    originalGood (b := b) .positive I bits cfg C cache seed

noncomputable def jointGoodCost (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) : ℝ :=
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  (p.compile I.weight).law.expect (fun seed => if jointGood (b := b) I bits cfg C cache seed then
    Causal.counterSeed I.weight bits p kind.counter seed else 0)

noncomputable def jointGoodFailure (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) (cache : Cache Q) : ℝ :=
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  (p.compile I.weight).law.prob {seed | ¬ jointGood (b := b) I bits cfg C cache seed}

def jointOutcomeGood {R : Type*} (n k b B : ℕ) (o : Outcome R) : Prop :=
  o.work ≤ counterCeiling .ordinary n k b B ∧
    o.positiveReplies ≤ counterCeiling .positive n k b B

theorem jointGood_iff (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) (cache : Cache Q)
    (seed : ((oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).compile I.weight).Seed) :
    jointGood (b := b) I bits cfg C cache seed ↔
      jointOutcomeGood n k b B
        ((((oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).compile I.weight).tree seed).output bits) := by
  simp only [jointGood, originalGood, Causal.counterGood, Causal.counterSeed,
    CounterKind.counter, workCounter_value, positiveCounter_value, jointOutcomeGood, Nat.cast_le]

theorem jointGoodCost_eq (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    jointGoodCost (b := b) kind I bits cfg C cache =
      (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if jointOutcomeGood n k b B o then kind.counter.value o else 0) := by
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  have he := Code.compile_expect I.weight bits p
    (fun o => if jointOutcomeGood n k b B o then kind.counter.value o else 0)
  apply Eq.trans _ he
  apply congrArg (p.compile I.weight).law.expect
  funext seed
  rw [jointGood_iff]
  rfl

theorem jointGoodFailure_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) (cache : Cache Q) :
    jointGoodFailure (b := b) I bits cfg C cache =
      (oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache).evaluate I.weight bits
        (fun o => if ¬ jointOutcomeGood n k b B o then 1 else 0) := by
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  change (p.compile I.weight).law.prob {seed | ¬ jointGood (b := b) I bits cfg C cache seed} = _
  rw [Law.prob_eq_expect]
  have he := Code.compile_expect I.weight bits p
    (fun o => if ¬ jointOutcomeGood n k b B o then (1 : ℝ) else 0)
  apply Eq.trans _ he
  apply congrArg (p.compile I.weight).law.expect
  funext seed
  simp only [Set.mem_ofPred_eq, jointGood_iff]
  split_ifs <;> rfl

theorem jointGoodCost_nonneg (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    0 ≤ jointGoodCost (b := b) kind I bits cfg C cache := by
  apply Law.expect_nonneg
  intro seed
  split_ifs
  · exact kind.counter.value_nonneg _
  · exact le_refl _

theorem jointGoodCost_le (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (C : Vertex I bits cfg B) (cache : Cache Q) :
    jointGoodCost (b := b) kind I bits cfg C cache ≤ originalGoodCost (b := b) kind I bits cfg C cache := by
  have hkind : ∀ seed, jointGood (b := b) I bits cfg C cache seed →
      originalGood (b := b) kind I bits cfg C cache seed := by
    intro seed hs
    cases kind
    · exact hs.1
    · exact hs.2
  apply Law.expect_mono
  intro seed
  by_cases hs : jointGood (b := b) I bits cfg C cache seed
  · simp only [hs, hkind seed hs, ↓reduceIte, le_refl]
  · simp only [hs, ↓reduceIte]
    split_ifs
    · exact kind.counter.value_nonneg _
    · exact le_refl _

theorem jointGoodFailure_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (C : Vertex I bits cfg B) (cache : Cache Q) :
    jointGoodFailure (b := b) I bits cfg C cache ≤
      originalGoodFailure (b := b) .ordinary I bits cfg C cache +
        originalGoodFailure (b := b) .positive I bits cfg C cache := by
  let p := oracle cfg (publicSize n k b B) (canonicalFrame I cfg b B C.val) cache
  have hs : {seed | ¬ jointGood (b := b) I bits cfg C cache seed} ⊆
      {seed | ¬ originalGood (b := b) .ordinary I bits cfg C cache seed} ∪
        {seed | ¬ originalGood (b := b) .positive I bits cfg C cache seed} := by
    intro seed hseed
    by_cases hw : originalGood (b := b) .ordinary I bits cfg C cache seed
    · exact Or.inr (fun hp => hseed ⟨hw, hp⟩)
    · exact Or.inl hw
  exact ((p.compile I.weight).law.prob_mono hs).trans ((p.compile I.weight).law.prob_union_le _ _)

theorem initiated_joint_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B *
            initiationAverage (kind.price (b := b) (B := B) I bits cfg hT hnd) (retained I bits cfg).card +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => jointGoodFailure (b := b) I bits cfg C (caches C)) (retained I bits cfg).card ≤
        2 * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  have ha := initiated_original_good_accounts (b := b) kind I bits cfg hT hnd caches hc hg
  have hw := (initiated_original_good_accounts (b := b) .ordinary I bits cfg hT hnd caches hc hg).2
  have hp := (initiated_original_good_accounts (b := b) .positive I bits cfg hT hnd caches hc hg).2
  have hn : (0 : ℝ) ≤ (retained I bits cfg).card := Nat.cast_nonneg _
  refine ⟨(initiation_mono _ _ _ hn (fun C => jointGoodCost_le kind I bits cfg C (caches C))).trans ha.1, ?_⟩
  have hfail := initiation_mono _ _ _ hn (fun C => jointGoodFailure_le (b := b) I bits cfg C (caches C))
  rw [initiation_add] at hfail
  have hbound := hfail.trans (add_le_add hw hp)
  convert hbound using 1
  ring

theorem closed_joint_good_accounts (kind : CounterKind)
    (I : Instance (Fin n)) (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n k)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (caches : Vertex I bits cfg B → Cache Q) (hc : ∀ C, Cache.Correct bits (caches C))
    (P : ℕ) (hres : ∀ v, (residualNeighbors I bits cfg v).card ≤ P)
    (hk : k ≤ n) (hb : b ^ 2 ≤ 50 * (n + 1)) (t : ℝ) (ht : 0 < t)
    (hinc : (b : ℝ) ≤ 4 * n / t + 1) (hprod : (b : ℝ) * P ≤ 81 * B * n / t)
    (hg : 0 < (retained I bits cfg).card) :
    initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B * geometricBudget kind n B t +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => jointGoodFailure (b := b) I bits cfg C (caches C)) (retained I bits cfg).card ≤
        2 * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  have ha := initiated_joint_good_accounts (b := b) kind I bits cfg hT hnd caches hc hg
  have hp := initiated_price_bound kind I bits cfg hT hnd P hres hk hb t ht hinc hprod hg
  exact ⟨ha.1.trans (add_le_add
    (mul_le_mul_of_nonneg_left hp (truncatedFactor_nonneg n k b B)) (le_refl _)), ha.2⟩

theorem calibrated_joint_good_accounts (kind : CounterKind)
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
    initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C)) (retained I bits cfg).card ≤
        truncatedFactor n k b B * geometricBudget kind n B t +
          12 * kind.counter.work * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) ∧
      initiationAverage (fun C => jointGoodFailure (b := b) I bits cfg C (caches C)) (retained I bits cfg).card ≤
        2 * ((Fintype.card (Vertex I bits cfg B) : ℝ) / (retained I bits cfg).card) *
          (1 / (publicSize n k b B : ℝ) ^ 3) := by
  exact closed_joint_good_accounts kind I bits cfg hT hnd caches hc (residualCap I bits cfg t)
    (residualCap_bounds I bits cfg t ht hres).2 hk hsquare t ht hinc
    (calibrated_residual_product I bits cfg t epsilon xi gm ht he he₁ hxi hg hcal hb hB) hg

theorem joint_accounts_empty (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n k) (caches : Vertex I bits cfg B → Cache Q)
    (hm : Fintype.card (Vertex I bits cfg B) = 0) :
    (∀ kind, initiationAverage (fun C => jointGoodCost (b := b) kind I bits cfg C (caches C))
      (retained I bits cfg).card = 0) ∧
      initiationAverage (fun C => jointGoodFailure (b := b) I bits cfg C (caches C)) (retained I bits cfg).card = 0 :=
  ⟨fun _ => initiation_empty _ _ hm, initiation_empty _ _ hm⟩

end SteinerUpperBound.PortGraph.RuntimeAdapter.Averaged

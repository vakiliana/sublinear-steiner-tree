module

public import SteinerUpperBound.LargeCoverProgram.Concrete
public import SteinerUpperBound.Matching.Padded.ClosedCost

@[expose] public section

set_option maxHeartbeats 800000

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram Matching.Padded
open scoped Classical BigOperators

theorem uniform_root_contraction {X A V : Type*} [Fintype X] [Nonempty X]
    [Fintype A] [Fintype V] (part : X → A) (hsurj : Function.Surjective part)
    (j : V → A) (w : V → ℝ) :
    (Law.uniform X).expect (fun x =>
      (∑ v, if j v = part x then w v else 0) /
        (SavingScores.partSize part (part x) : ℝ)) =
      (∑ v, w v) / (Nat.card X : ℝ) := by
  have h := SavingScores.uniform_part_mean part hsurj
    (fun a => ∑ v, if j v = a then w v else 0)
  apply h.trans
  congr 1
  rw [Finset.sum_comm]
  simp

/-- Root-family averaging remains valid when the incoming cache (and hence
the cost function) depends on the sampled point inside a component. A finite
fiber maximizer selects ONE valid cache/frame family before invoking the
uniform-root resource theorem. No conditioning on a cheap future is used. -/
theorem root_family_domination {X A V : Type*} [Fintype X] [Nonempty X]
    [Fintype A] [Fintype V] (part : X → A) (hsurj : Function.Surjective part)
    (j : V → A) (f : X → ℝ) :
    ∃ pick : V → X, (∀ v, part (pick v) = j v) ∧
      (Law.uniform X).expect (fun x =>
        (∑ v, if j v = part x then f x else 0) /
          (SavingScores.partSize part (part x) : ℝ)) ≤
        (∑ v, f (pick v)) / (Nat.card X : ℝ) := by
  have hex (v : V) :
      ∃ x ∈ SavingScores.fiber part (j v),
        ∀ y ∈ SavingScores.fiber part (j v), f y ≤ f x := by
    apply Finset.exists_max_image
    obtain ⟨x, hx⟩ := hsurj (j v)
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  choose pick hpick hmax using hex
  have hpart (v : V) : part (pick v) = j v := (Finset.mem_filter.mp (hpick v)).2
  have hm := Law.expect_mono (Law.uniform X) (fun x => show
      (∑ v, if j v = part x then f x else 0) /
          (SavingScores.partSize part (part x) : ℝ) ≤
        (∑ v, if j v = part x then f (pick v) else 0) /
          (SavingScores.partSize part (part x) : ℝ) by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro v _
    by_cases h : j v = part x
    · simp only [h, ite_true]
      exact hmax v x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm⟩)
    · simp only [h, ite_false, le_refl])
  rw [uniform_root_contraction part hsurj j (fun v => f (pick v))] at hm
  exact ⟨pick, hpart, hm⟩

theorem uniform_root_family_bound {X A V : Type*} [Fintype X] [Nonempty X]
    [Fintype A] [Fintype V] (part : X → A) (hsurj : Function.Surjective part)
    (j : V → A) (f : X → ℝ) (budget : ℝ)
    (hfamily : ∀ pick : V → X, (∀ v, part (pick v) = j v) →
      (∑ v, f (pick v)) ≤ (Fintype.card V : ℝ) * budget) :
    (Law.uniform X).expect (fun x =>
      (∑ v, if j v = part x then f x else 0) /
        (SavingScores.partSize part (part x) : ℝ)) ≤
      ((Fintype.card V : ℝ) / Nat.card X) * budget := by
  obtain ⟨pick, hpick, hm⟩ := root_family_domination part hsurj j f
  calc
    _ ≤ (∑ v, f (pick v)) / (Nat.card X : ℝ) := hm
    _ ≤ ((Fintype.card V : ℝ) * budget) / Nat.card X :=
      div_le_div_of_nonneg_right (hfamily pick hpick) (Nat.cast_nonneg _)
    _ = _ := by ring

theorem uniform_root_family_average_bound {X A V : Type*} [Fintype X] [Nonempty X]
    [Fintype A] [Fintype V] (part : X → A) (hsurj : Function.Surjective part)
    (j : V → A) (f : X → ℝ) (budget : ℝ)
    (hfamily : ∀ pick : V → X, (∀ v, part (pick v) = j v) →
      (∑ v, f (pick v)) / (Nat.card X : ℝ) ≤ budget) :
    (Law.uniform X).expect (fun x =>
      (∑ v, if j v = part x then f x else 0) /
        (SavingScores.partSize part (part x) : ℝ)) ≤ budget := by
  obtain ⟨pick, hpick, hm⟩ := root_family_domination part hsurj j f
  exact hm.trans (hfamily pick hpick)

theorem uniform_family_to_sum {X V A : Type*} [Fintype V] [Nonempty V]
    (part : X → A) (j : V → A) (f : X → ℝ) (budget : ℝ)
    (hfamily : ∀ pick : V → X, (∀ v, part (pick v) = j v) →
      (Law.uniform V).expect (fun v => f (pick v)) ≤ budget) :
    ∀ pick : V → X, (∀ v, part (pick v) = j v) →
      (∑ v, f (pick v)) ≤ (Fintype.card V : ℝ) * budget := by
  intro pick hpick
  have hh := hfamily pick hpick
  rw [SavingScores.uniform_expect, Nat.card_eq_fintype_card] at hh
  have hm : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  simpa only [mul_comm] using (div_le_iff₀ hm).mp hh

variable {Q : Type} {n k b B : ℕ}

/-- Analysis-only charge of a matching invocation at a retained point.
The initiation coin is included; the callback's root is the actual canonical
component, not the sampled initiating terminal. -/
noncomputable def initiatedRootCharge (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (w : PortGraph.Vertex I bits cfg B → ℝ) (u : Fin (k + 1)) : ℝ :=
  if bits (cfg.key (cfg.terminals.get u)) then
    (inverseRate (componentAt I bits cfg u).card : ℝ) *
      ∑ C : PortGraph.Vertex I bits cfg B,
        if C.val = componentAt I bits cfg u then w C else 0
  else 0

noncomputable def initiatedPointCharge (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (f : Fin (k + 1) → ℝ) (u : Fin (k + 1)) : ℝ :=
  if bits (cfg.key (cfg.terminals.get u)) then
    (inverseRate (componentAt I bits cfg u).card : ℝ) *
      ∑ C : PortGraph.Vertex I bits cfg B,
        if C.val = componentAt I bits cfg u then f u else 0
  else 0

theorem initiatedRootCharge_nonneg (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (w : PortGraph.Vertex I bits cfg B → ℝ) (hw : ∀ C, 0 ≤ w C) (u : Fin (k + 1)) :
    0 ≤ initiatedRootCharge I bits cfg w u := by
  unfold initiatedRootCharge
  split
  · apply mul_nonneg (inverseRate _).property.1
    exact Finset.sum_nonneg (fun C _ => by split_ifs; exact hw C; exact le_refl _)
  · exact le_refl _

/-- Exact cancellation of component size against the REAL initiation rate.
This sum formulation includes the zero-residual-vertex case without ever
constructing a uniform law on an empty type. -/
theorem initiatedRootCharge_mean (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (w : PortGraph.Vertex I bits cfg B → ℝ) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedRootCharge I bits cfg w) =
      (∑ C, w C) / (Nat.card (RetainedIndex bits cfg) : ℝ) := by
  letI : Nonempty (RetainedIndex bits cfg) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  letI : DecidableEq (Part I bits cfg) := Classical.decEq _
  rw [← uniformRetained_map (fun u => bits (cfg.key (cfg.terminals.get u))) hb, Law.expect_map]
  let part := partition I bits cfg hT
  have hpoint (x : RetainedIndex bits cfg) :
      initiatedRootCharge I bits cfg w x.val =
        (∑ C, if PortGraph.inclusion I bits cfg B C = part x then w C else 0) /
          (SavingScores.partSize part (part x) : ℝ) := by
    have hr := retainedIndex_bit bits cfg x
    have hsize : SavingScores.partSize part (part x) = (componentAt I bits cfg x.val).card := by
      simpa only [part, partition] using partition_size I bits cfg hT hnd (part x)
    have hp : 0 < (componentAt I bits cfg x.val).card := by
      rw [← hsize]
      exact SavingScores.partSize_pos part (partition_surjective I bits cfg hT) _
    have he (C : PortGraph.Vertex I bits cfg B) :
        PortGraph.inclusion I bits cfg B C = part x ↔ C.val = componentAt I bits cfg x.val :=
      Subtype.ext_iff
    simp only [initiatedRootCharge, hr, ite_true, inverseRate_value _ hp, he]
    rw [hsize]
    ring
  calc
    _ = (Law.uniform (RetainedIndex bits cfg)).expect (fun x =>
        (∑ C, if PortGraph.inclusion I bits cfg B C = part x then w C else 0) /
          (SavingScores.partSize part (part x) : ℝ)) :=
      congrArg (Law.uniform (RetainedIndex bits cfg)).expect (funext hpoint)
    _ = _ := uniform_root_contraction part (partition_surjective I bits cfg hT) _ w

theorem initiatedRootCharge_mean_uniform (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    [Nonempty (PortGraph.Vertex I bits cfg B)] (w : PortGraph.Vertex I bits cfg B → ℝ) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedRootCharge I bits cfg w) =
      ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) / Nat.card (RetainedIndex bits cfg)) *
        (Law.uniform (PortGraph.Vertex I bits cfg B)).expect w := by
  letI : Nonempty (RetainedIndex bits cfg) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  rw [initiatedRootCharge_mean I bits cfg hT hnd hb, SavingScores.uniform_expect]
  have hm : (Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Nat.card_eq_fintype_card]
  field_simp

theorem initiatedRootCharge_empty (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hm : Fintype.card (PortGraph.Vertex I bits cfg B) = 0)
    (w : PortGraph.Vertex I bits cfg B → ℝ) (u : Fin (k + 1)) :
    initiatedRootCharge I bits cfg w u = 0 := by
  letI : IsEmpty (PortGraph.Vertex I bits cfg B) := Fintype.card_eq_zero_iff.mp hm
  simp [initiatedRootCharge]

theorem initiatedPointCharge_empty (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hm : Fintype.card (PortGraph.Vertex I bits cfg B) = 0)
    (f : Fin (k + 1) → ℝ) (u : Fin (k + 1)) :
    initiatedPointCharge (B := B) I bits cfg f u = 0 := by
  letI : IsEmpty (PortGraph.Vertex I bits cfg B) := Fintype.card_eq_zero_iff.mp hm
  simp [initiatedPointCharge]

theorem residual_root_ratio_le_one (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty) :
    (Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) / Nat.card (RetainedIndex bits cfg) ≤ 1 := by
  have hg : 0 < Nat.card (RetainedIndex bits cfg) := by
    rw [retainedIndex_count bits cfg]
    exact Finset.card_pos.mpr hb
  have hm := PortGraph.vertices_card_le I bits cfg B
  rw [← retainedIndex_card I bits cfg hT hnd] at hm
  apply (div_le_one (by exact_mod_cast hg : (0 : ℝ) < Nat.card (RetainedIndex bits cfg))).mpr
  exact_mod_cast hm

theorem initiatedRootCharge_sum_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (w : PortGraph.Vertex I bits cfg B → ℝ) (budget : ℝ)
    (hw : (∑ C, w C) ≤ (Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) * budget) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedRootCharge I bits cfg w) ≤
      ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) / Nat.card (RetainedIndex bits cfg)) * budget := by
  rw [initiatedRootCharge_mean I bits cfg hT hnd hb]
  calc
    _ ≤ ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) * budget) /
        Nat.card (RetainedIndex bits cfg) := div_le_div_of_nonneg_right hw (Nat.cast_nonneg _)
    _ = _ := by ring

theorem initiatedPointCharge_family_domination (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (f : Fin (k + 1) → ℝ) :
    ∃ pick : PortGraph.Vertex I bits cfg B → RetainedIndex bits cfg,
      (∀ C, partition I bits cfg hT (pick C) = PortGraph.inclusion I bits cfg B C) ∧
      (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
        (initiatedPointCharge (B := B) I bits cfg f) ≤
        (∑ C, f (pick C).val) / (Nat.card (RetainedIndex bits cfg) : ℝ) := by
  letI : Nonempty (RetainedIndex bits cfg) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  letI : DecidableEq (Part I bits cfg) := Classical.decEq _
  rw [← uniformRetained_map (fun u => bits (cfg.key (cfg.terminals.get u))) hb, Law.expect_map]
  let part := partition I bits cfg hT
  have hpoint (x : RetainedIndex bits cfg) :
      initiatedPointCharge (B := B) I bits cfg f x.val =
        (∑ C, if PortGraph.inclusion I bits cfg B C = part x then f x.val else 0) /
          (SavingScores.partSize part (part x) : ℝ) := by
    have hr := retainedIndex_bit bits cfg x
    have hsize : SavingScores.partSize part (part x) = (componentAt I bits cfg x.val).card := by
      simpa only [part, partition] using partition_size I bits cfg hT hnd (part x)
    have hp : 0 < (componentAt I bits cfg x.val).card := by
      rw [← hsize]
      exact SavingScores.partSize_pos part (partition_surjective I bits cfg hT) _
    have he (C : PortGraph.Vertex I bits cfg B) :
        PortGraph.inclusion I bits cfg B C = part x ↔ C.val = componentAt I bits cfg x.val :=
      Subtype.ext_iff
    simp only [initiatedPointCharge, hr, ite_true, inverseRate_value _ hp, he]
    rw [hsize]
    ring
  rw [show (fun x : RetainedIndex bits cfg => initiatedPointCharge (B := B) I bits cfg f x.val) =
      (fun x => (∑ C, if PortGraph.inclusion I bits cfg B C = part x then f x.val else 0) /
        (SavingScores.partSize part (part x) : ℝ)) from funext hpoint]
  exact root_family_domination part (partition_surjective I bits cfg hT)
    (PortGraph.inclusion I bits cfg B) (fun x => f x.val)

theorem initiatedPointCharge_family_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (f : Fin (k + 1) → ℝ) (budget : ℝ)
    (hfamily : ∀ pick : PortGraph.Vertex I bits cfg B → RetainedIndex bits cfg,
      (∀ C, partition I bits cfg hT (pick C) = PortGraph.inclusion I bits cfg B C) →
      (∑ C, f (pick C).val) ≤ (Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) * budget) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedPointCharge (B := B) I bits cfg f) ≤
      ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) / Nat.card (RetainedIndex bits cfg)) * budget := by
  obtain ⟨pick, hpick, hm⟩ := initiatedPointCharge_family_domination I bits cfg hT hnd hb f
  calc
    _ ≤ (∑ C, f (pick C).val) / (Nat.card (RetainedIndex bits cfg) : ℝ) := hm
    _ ≤ ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) * budget) /
        Nat.card (RetainedIndex bits cfg) := div_le_div_of_nonneg_right (hfamily pick hpick) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Direct interface for already g-normalized ORIGINAL-code family bounds.
No division by m and no nonempty-residual hypothesis is introduced. -/
theorem initiatedPointCharge_family_average_bound (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (f : Fin (k + 1) → ℝ) (budget : ℝ)
    (hfamily : ∀ pick : PortGraph.Vertex I bits cfg B → RetainedIndex bits cfg,
      (∀ C, partition I bits cfg hT (pick C) = PortGraph.inclusion I bits cfg B C) →
      (∑ C, f (pick C).val) / (Nat.card (RetainedIndex bits cfg) : ℝ) ≤ budget) :
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedPointCharge (B := B) I bits cfg f) ≤ budget := by
  obtain ⟨pick, hpick, hm⟩ := initiatedPointCharge_family_domination I bits cfg hT hnd hb f
  exact hm.trans (hfamily pick hpick)

/-- Normalization of the CHECKED closed cost theorem, with the factor m/g
applied ONLY AFTER uniform component-root averaging. `goodCost` remains the
completed-priority MODEL good cost, not a purported original-code good seed. -/
theorem initiated_model_goodCost_le (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (P : Matching.Padded.Parameters (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd))
    (A : Matching.Padded.Account (PortGraph.slots (b := b) (B := B) I bits cfg hT hnd)) :
    let S := PortGraph.slots (b := b) (B := B) I bits cfg hT hnd
    (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb).expect
      (initiatedRootCharge I bits cfg (Execution.goodCost S P A)) ≤
      ((Fintype.card (PortGraph.Vertex I bits cfg B) : ℝ) / Nat.card (RetainedIndex bits cfg)) *
        (Matching.Padded.Parameters.costFactor S P * Account.publicPrice S A) := by
  dsimp only
  by_cases hm : Nonempty (PortGraph.Vertex I bits cfg B)
  · letI := hm
    rw [initiatedRootCharge_mean_uniform I bits cfg hT hnd hb]
    exact mul_le_mul_of_nonneg_left (Execution.expected_goodCost_le _ P A) (by positivity)
  · letI : IsEmpty (PortGraph.Vertex I bits cfg B) := not_nonempty_iff.mp hm
    rw [initiatedRootCharge_mean I bits cfg hT hnd hb]
    simp

end SteinerUpperBound.LargeCoverProgram

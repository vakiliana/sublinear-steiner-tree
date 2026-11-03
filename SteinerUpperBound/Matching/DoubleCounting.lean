module

public import SteinerUpperBound.Matching.CallCount

@[expose] public section

/-!
# Counting short invocation stacks

The map sends an invocation to its rotated order and its stack length.
Its injectivity is proved in `Rotation`, and invocation multiplicity (including
cache hits and different fresh-cache roots) is handled in `Trace`.
-/

namespace SteinerUpperBound.Matching

open SteinerLowerBound FiniteAveraging
open scoped Classical BigOperators

namespace Graph

theorem flatMap_stacks_nodup {A E : Type*} (xs : List A) (f : A → List (Invocation E))
    (hn : xs.Nodup) (hrow : ∀ a ∈ xs, ((f a).map Invocation.stack).Nodup)
    (hdisj : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b →
      ∀ c ∈ f a, ∀ c' ∈ f b, c.stack ≠ c'.stack) :
    ((xs.flatMap f).map Invocation.stack).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.nodup_cons.mp hn
    rw [List.flatMap_cons, List.map_append, List.nodup_append]
    refine ⟨hrow a (by simp), ih hxs (fun b hb => hrow b (by simp [hb]))
      (fun b hb c hc => hdisj b (by simp [hb]) c (by simp [hc])), ?_⟩
    intro s hs t ht
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp ht
    obtain ⟨b, hb, hcb⟩ := List.mem_flatMap.mp hc'
    exact hdisj a (by simp) b (by simp [hb]) (fun heq => ha (heq ▸ hb))
      c hc c' hcb

theorem requests_flatMap {A E : Type*} (xs : List A) (f : A → List (Invocation E))
    (d : Directed E) :
    requests (xs.flatMap f) d = (xs.map fun a => requests (f a) d).sum := by
  induction xs with
  | nil => simp [requests]
  | cons a xs ih => simp only [List.flatMap_cons, requests_append, List.map_cons,
      List.sum_cons, ih]

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : Graph V E)

noncomputable def allCalls (ρ : Rank E) : List (Invocation E) :=
  Finset.univ.toList.flatMap fun v => (G.vertexOracle ρ v).calls

theorem mem_allCalls (ρ : Rank E) (c : Invocation E) :
    c ∈ G.allCalls ρ ↔ ∃ v, c ∈ (G.vertexOracle ρ v).calls := by
  simp [allCalls]

theorem allCalls_stacks_nodup (ρ : Rank E) :
    ((G.allCalls ρ).map Invocation.stack).Nodup :=
  flatMap_stacks_nodup _ _ (Finset.nodup_toList _)
    (fun v _ => G.vertexOracle_stacks_nodup ρ v)
    (fun _ _ _ _ hne c hc c' hc' => G.vertexOracle_stacks_disjoint ρ hne c c' hc hc')

theorem allCalls_validStack (ρ : Rank E) (c : Invocation E) (hc : c ∈ G.allCalls ρ) :
    G.ValidStack ρ c.stack := by
  obtain ⟨v, hv⟩ := (G.mem_allCalls ρ c).mp hc
  exact G.vertexOracle_validStack ρ v c hv

theorem requests_allCalls (ρ : Rank E) (d : Directed E) :
    requests (G.allCalls ρ) d = G.Q ρ d := by
  rw [allCalls, requests_flatMap, ← List.sum_toFinset _ (Finset.nodup_toList _)]
  simp [Q]

noncomputable def shortTrace (ρ : Rank E) (d : Directed E) (D : ℕ) :
    List (Invocation E) :=
  (G.allCalls ρ).filter fun c => c.state = d ∧ c.ancestors.length < D

noncomputable def shortParents (ρ : Rank E) (d : Directed E) (D : ℕ) :
    List (List (Directed E)) := (G.shortTrace ρ d D).map Invocation.ancestors

noncomputable def shortCount (ρ : Rank E) (d : Directed E) (D : ℕ) : ℕ :=
  (G.shortParents ρ d D).length

theorem shortParents_nodup (ρ : Rank E) (d : Directed E) (D : ℕ) :
    (G.shortParents ρ d D).Nodup := by
  have hp := G.allCalls_stacks_nodup ρ
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hp
  have hf := hp.filter (fun c => decide (c.state = d ∧ c.ancestors.length < D))
  rw [shortParents, List.nodup_iff_pairwise_ne, List.pairwise_map]
  apply hf.imp_of_mem
  intro c c' hc hc' hne heq
  have hcs : c.state = d := (of_decide_eq_true (List.mem_filter.mp hc).2).1
  have hcs' : c'.state = d := (of_decide_eq_true (List.mem_filter.mp hc').2).1
  exact hne (by simp only [Invocation.stack, hcs, hcs', heq])

noncomputable def shortFin (ρ : Rank E) (d : Directed E) (D : ℕ) :
    Finset (List (Directed E)) := (G.shortParents ρ d D).toFinset

theorem shortFin_card (ρ : Rank E) (d : Directed E) (D : ℕ) :
    (G.shortFin ρ d D).card = G.shortCount ρ d D :=
  List.toFinset_card_of_nodup (G.shortParents_nodup ρ d D)

theorem shortFin_valid (ρ : Rank E) (d : Directed E) (D : ℕ)
    (parents : List (Directed E)) (hp : parents ∈ G.shortFin ρ d D) :
    G.ValidStack ρ (d :: parents) ∧ parents.length < D := by
  have hm : parents ∈ G.shortParents ρ d D := List.mem_toFinset.mp hp
  obtain ⟨c, hc, hcp⟩ := List.mem_map.mp hm
  obtain ⟨hall, hstate, hlen⟩ : c ∈ G.allCalls ρ ∧ c.state = d ∧ c.ancestors.length < D := by
    simpa [shortTrace] using hc
  have hv := G.allCalls_validStack ρ c hall
  simpa only [Invocation.stack, hstate, hcp] using And.intro hv hlen

/-- Counting pairs of orders and actual short invocation stacks. -/
theorem shortCount_sum_le (d : Directed E) (D : ℕ) :
    ∑ ρ : Rank E, G.shortCount ρ d D ≤ Fintype.card (Rank E) * D := by
  classical
  let A : Finset (Rank E × List (Directed E)) :=
    Finset.univ.biUnion fun ρ => (G.shortFin ρ d D).image fun p => (ρ, p)
  let F : Rank E × List (Directed E) → Rank E × ℕ := fun z =>
    (G.rotated z.1 d z.2, z.2.length)
  have hmem {z : Rank E × List (Directed E)} (hz : z ∈ A) :
      z.2 ∈ G.shortFin z.1 d D := by
    obtain ⟨ρ, _, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hz
    cases heq
    exact hp
  have hvalid {z : Rank E × List (Directed E)} (hz : z ∈ A) :
      G.ValidStack z.1 (d :: z.2) ∧ z.2.length < D :=
    G.shortFin_valid z.1 d D z.2 (hmem hz)
  have hinj : Set.InjOn F ↑A := by
    intro z hz z' hz' heq
    have h1 := hvalid hz
    have h2 := hvalid hz'
    have hh := G.rotation_preimage_unique z.1 z'.1 d z.2 z'.2 h1.1 h2.1
      (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    exact Prod.ext hh.1 hh.2
  have hsub : A.image F ⊆ Finset.univ ×ˢ Finset.range D := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (hvalid hw).2⟩
  have hcard : A.card ≤ Fintype.card (Rank E) * D := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans_eq (by simp)
  have hdisj : ((Finset.univ : Finset (Rank E)) : Set (Rank E)).PairwiseDisjoint
      (fun ρ => (G.shortFin ρ d D).image fun p => (ρ, p)) := by
    intro ρ _ σ _ hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨q, _, heq⟩ := Finset.mem_image.mp hz'
    exact hne (congrArg Prod.fst heq).symm
  have hcardA : A.card = ∑ ρ : Rank E, G.shortCount ρ d D := by
    rw [show A = _ from rfl, Finset.card_biUnion hdisj]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
      G.shortFin_card]
  rw [hcardA] at hcard
  exact hcard

/-- Unconditional rank-averaged bound for the short-stack portion of `Q`. -/
theorem shortCount_expect_le (d : Directed E) (D : ℕ) :
    (Rank.uniform (E := E)).expect (fun ρ => (G.shortCount ρ d D : ℝ)) ≤ D := by
  have hsum : (∑ ρ : Rank E, (G.shortCount ρ d D : ℝ)) ≤
      (Fintype.card (Rank E) : ℝ) * D := by
    exact_mod_cast G.shortCount_sum_le d D
  have hp : (0 : ℝ) < Fintype.card (Rank E) := by
    exact_mod_cast Fintype.card_pos
  change (∑ ρ : Rank E, (Fintype.card (Rank E) : ℝ)⁻¹ * (G.shortCount ρ d D : ℝ)) ≤ D
  rw [← Finset.mul_sum]
  calc
    _ ≤ (Fintype.card (Rank E) : ℝ)⁻¹ * ((Fintype.card (Rank E) : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp

def LongStack (D : ℕ) (ρ : Rank E) : Prop :=
  ∃ d parents, G.ValidStack ρ (d :: parents) ∧ D ≤ parents.length

theorem Q_eq_shortCount_of_not_long (ρ : Rank E) (d : Directed E) (D : ℕ)
    (h : ¬ G.LongStack D ρ) : G.Q ρ d = G.shortCount ρ d D := by
  classical
  rw [← G.requests_allCalls ρ d]
  unfold shortCount shortParents shortTrace
  rw [List.length_map, ← List.countP_eq_length_filter]
  apply List.countP_congr
  intro c hc
  have hlen : c.ancestors.length < D := by
    by_contra hn
    exact h ⟨c.state, c.ancestors, G.allCalls_validStack ρ c hc, Nat.le_of_not_gt hn⟩
  simp [hlen]

/-- The remaining probability term refers to an explicitly defined stack event. -/
theorem Q_expect_le_depth_tail (d : Directed E) (D : ℕ) :
    (Rank.uniform (E := E)).expect (fun ρ => (G.Q ρ d : ℝ)) ≤
      D + (Fintype.card V * (2 * Fintype.card E + 1) : ℕ) *
        (Rank.uniform (E := E)).prob {ρ | G.LongStack D ρ} := by
  have hpoint (ρ : Rank E) : (G.Q ρ d : ℝ) ≤
      G.shortCount ρ d D + (Fintype.card V * (2 * Fintype.card E + 1) : ℕ) *
        indicator (G.LongStack D) ρ := by
    by_cases h : G.LongStack D ρ
    · have hq : (G.Q ρ d : ℝ) ≤ (Fintype.card V * (2 * Fintype.card E + 1) : ℕ) := by
        exact_mod_cast G.Q_le ρ d
      simpa only [indicator, h, ↓reduceIte, mul_one] using
        hq.trans (le_add_of_nonneg_left (Nat.cast_nonneg (G.shortCount ρ d D)))
    · rw [G.Q_eq_shortCount_of_not_long ρ d D h]
      simp [indicator, h]
  have hh := (Rank.uniform (E := E)).expect_mono hpoint
  rw [Law.expect_add, Law.expect_const_mul, expect_indicator] at hh
  exact hh.trans (add_le_add (G.shortCount_expect_le d D) (le_refl _))

end Graph

end SteinerUpperBound.Matching

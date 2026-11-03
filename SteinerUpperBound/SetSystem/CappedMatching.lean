module

public import SteinerUpperBound.SetSystem.MutualCapping
public import SteinerUpperBound.Matching.Greedy

@[expose] public section

namespace SteinerUpperBound.SetSystem

open scoped Classical BigOperators

variable {R U D : Type*}

noncomputable def matchedEndpoints (G : Matching.Graph U D) (M : Finset D) :
    Finset U := M.biUnion (fun e => {G.left e, G.right e})

theorem mem_matchedEndpoints (G : Matching.Graph U D) (M : Finset D) (x : U) :
    x ∈ matchedEndpoints G M ↔ ∃ e ∈ M, G.Incident e x := by
  classical
  simp only [matchedEndpoints, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton, Matching.Graph.Incident]
  aesop

theorem matchedEndpoints_card (G : Matching.Graph U D) (M : Finset D)
    (hM : G.IsMatching M) : (matchedEndpoints G M).card = 2 * M.card := by
  classical
  have hd : (M : Set D).PairwiseDisjoint (fun e => ({G.left e, G.right e} : Finset U)) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hex : G.Incident e x := by
      simpa only [Matching.Graph.Incident, Finset.mem_insert, Finset.mem_singleton,
        eq_comm] using hx
    have hfx : G.Incident f x := by
      simpa only [Matching.Graph.Incident, Finset.mem_insert, Finset.mem_singleton,
        eq_comm] using hy
    exact hne (hM e he f hf ⟨x, hex, hfx⟩)
  rw [matchedEndpoints, Finset.card_biUnion hd]
  simp [G.loopless, Nat.mul_comm]

/-- Parallel copy labels are retained; only the underlying adjacency is compared. -/
def Realizes (G : Matching.Graph U D) (H : SimpleGraph U) : Prop :=
  ∀ x y, H.Adj x y ↔
    ∃ e, (G.left e = x ∧ G.right e = y) ∨ (G.left e = y ∧ G.right e = x)

theorem Realizes.copy_adj {G : Matching.Graph U D} {H : SimpleGraph U}
    (h : Realizes G H) (e : D) : H.Adj (G.left e) (G.right e) :=
  (h _ _).mpr ⟨e, Or.inl ⟨rfl, rfl⟩⟩

theorem unmatched_independent (G : Matching.Graph U D) (H : SimpleGraph U)
    (hreal : Realizes G H) (M : Finset D) (hM : G.IsMaximalMatching M)
    (A : Finset U) : IsIndependent H (A \ matchedEndpoints G M) := by
  classical
  intro x hx y hy _ hxy
  have hxM := (Finset.mem_sdiff.mp hx).2
  have hyM := (Finset.mem_sdiff.mp hy).2
  obtain ⟨e, he⟩ := (hreal x y).mp hxy
  obtain ⟨f, hf, v, hev, hfv⟩ := hM.2 e
  have hvM : v ∈ matchedEndpoints G M := (mem_matchedEndpoints G M v).mpr ⟨f, hf, hfv⟩
  rcases he with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · simp only [Matching.Graph.Incident, hl, hr] at hev
    rcases hev with h | h
    · exact hxM (h ▸ hvM)
    · exact hyM (h ▸ hvM)
  · simp only [Matching.Graph.Incident, hl, hr] at hev
    rcases hev with h | h
    · exact hyM (h ▸ hvM)
    · exact hxM (h ▸ hvM)

theorem matching_le_saving (E : Finset R) (rows : R → Finset U) (A : Finset U)
    (G : Matching.Graph U D) (M : Finset D) (hM : G.IsMatching M)
    (hports : ∀ e ∈ M, ∃ r ∈ E,
      G.left e ∈ A ∩ rows r ∧ G.right e ∈ A ∩ rows r) :
    (M.card : ℝ) ≤ saving E rows A := by
  classical
  let center (e : ↥M) : R := Classical.choose (hports e.val e.property)
  have hcenter (e : ↥M) :
      center e ∈ E ∧ G.left e.val ∈ A ∩ rows (center e) ∧
        G.right e.val ∈ A ∩ rows (center e) :=
    Classical.choose_spec (hports e.val e.property)
  let F := M.attach.image center
  have hFE : F ⊆ E := by
    intro r hr
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hcenter e).1
  have hFcard : F.card ≤ M.card := by
    exact Finset.card_image_le.trans (by simp)
  have hend : matchedEndpoints G M ⊆ A ∩ F.biUnion rows := by
    intro x hx
    obtain ⟨e, he, hex⟩ := (mem_matchedEndpoints G M x).mp hx
    let e' : ↥M := ⟨e, he⟩
    have hc := hcenter e'
    have hxrow : x ∈ A ∩ rows (center e') := by
      rcases hex with h | h
      · exact h ▸ hc.2.1
      · exact h ▸ hc.2.2
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hxrow).1,
      Finset.mem_biUnion.mpr ⟨center e', Finset.mem_image.mpr
        ⟨e', Finset.mem_attach _ _, rfl⟩, (Finset.mem_inter.mp hxrow).2⟩⟩
  have hc := Finset.card_le_card hend
  rw [matchedEndpoints_card G M hM] at hc
  have hc' : 2 * (M.card : ℝ) ≤ (A ∩ F.biUnion rows).card := by exact_mod_cast hc
  have hFcard' : (F.card : ℝ) ≤ M.card := by exact_mod_cast hFcard
  have hw := saving_witness E rows A F hFE
  linarith

theorem mutualCap_matching_bounds (allRows E : Finset R) (rows : R → Finset U)
    (hE : E ⊆ allRows) (A : Finset U) (b : ℕ) (hb : 1 ≤ b)
    (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (G : Matching.Graph U D) (hreal : Realizes G (mutualGraph A E cap.lists))
    (M : Finset D) (hM : G.IsMaximalMatching M) :
    (M.card : ℝ) ≤ saving E rows A ∧
      saving E rows A ≤ 2 * M.card + 2 * allRows.card / b := by
  classical
  have hedge (e : D) := hreal.copy_adj e
  have hends : matchedEndpoints G M ⊆ A := by
    intro x hx
    obtain ⟨e, _, hex⟩ := (mem_matchedEndpoints G M x).mp hx
    rcases hex with h | h
    · exact h ▸ (hedge e).1
    · exact h ▸ (hedge e).2.1
  have hlower : (M.card : ℝ) ≤ saving E rows A := by
    apply matching_le_saving E rows A G M hM.1
    intro e _
    obtain ⟨hl, hr, _, r, hrE, hrl, hrr⟩ := hedge e
    exact ⟨r, hrE,
      Finset.mem_inter.mpr ⟨hl, (cap.sound _ hl r hrl).2⟩,
      Finset.mem_inter.mpr ⟨hr, (cap.sound _ hr r hrr).2⟩⟩
  have hind := unmatched_independent G _ hreal M hM A
  have hu := mutualCap_independent_bound allRows E rows hE A b hb cap hineligible
    (A \ matchedEndpoints G M) Finset.sdiff_subset hind
  have hd := Finset.card_sdiff_add_card_eq_card hends
  rw [matchedEndpoints_card G M hM.1] at hd
  have hd' : ((A \ matchedEndpoints G M).card : ℝ) + 2 * (M.card : ℝ) = A.card := by
    exact_mod_cast hd
  exact ⟨hlower, by linarith⟩

theorem mutualCap_matching_half (allRows E : Finset R) (rows : R → Finset U)
    (hE : E ⊆ allRows) (A : Finset U) (b : ℕ) (hb : 1 ≤ b)
    (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (G : Matching.Graph U D) (hreal : Realizes G (mutualGraph A E cap.lists))
    (M : Finset D) (hM : G.IsMaximalMatching M) :
    saving E rows A / 2 - allRows.card / b ≤ (M.card : ℝ) ∧
      (M.card : ℝ) ≤ saving E rows A := by
  obtain ⟨hl, hu⟩ := mutualCap_matching_bounds allRows E rows hE A b hb cap hineligible
    G hreal M hM
  rw [mul_div_assoc] at hu
  constructor
  · linarith
  · exact hl

theorem mutualCap_greedy_half [Fintype D] (allRows E : Finset R)
    (rows : R → Finset U) (hE : E ⊆ allRows) (A : Finset U)
    (b : ℕ) (hb : 1 ≤ b) (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (G : Matching.Graph U D) (hreal : Realizes G (mutualGraph A E cap.lists))
    (order : Matching.Rank D) :
    saving E rows A / 2 - allRows.card / b ≤ ((G.greedy order).card : ℝ) ∧
      ((G.greedy order).card : ℝ) ≤ saving E rows A :=
  mutualCap_matching_half allRows E rows hE A b hb cap hineligible G hreal
    (G.greedy order) (G.greedy_isMaximalMatching order)

theorem mutualCap_expected_greedy_half [Fintype D] (allRows E : Finset R)
    (rows : R → Finset U) (hE : E ⊆ allRows) (A : Finset U)
    (b : ℕ) (hb : 1 ≤ b) (cap : IncidenceCap allRows rows A b)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (A ∩ rows r).card ≤ 2)
    (G : Matching.Graph U D) (hreal : Realizes G (mutualGraph A E cap.lists))
    (μ : SteinerLowerBound.Law (Matching.Rank D)) :
    saving E rows A / 2 - allRows.card / b ≤ μ.expect (fun order => (G.greedy order).card) ∧
      μ.expect (fun order => (G.greedy order).card) ≤ saving E rows A := by
  have h (order : Matching.Rank D) :=
    mutualCap_greedy_half allRows E rows hE A b hb cap hineligible G hreal order
  constructor
  · simpa only [SteinerLowerBound.Law.expect_const] using
      μ.expect_mono (fun order => (h order).1)
  · simpa only [SteinerLowerBound.Law.expect_const] using
      μ.expect_mono (fun order => (h order).2)

end SteinerUpperBound.SetSystem

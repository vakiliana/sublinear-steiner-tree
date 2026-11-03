module

public import SteinerUpperBound.Matching.WindowPaths

@[expose] public section

namespace SteinerUpperBound.Matching

open scoped Classical BigOperators

namespace Dyadic

noncomputable def stages (p h : ℕ) : Finset ℕ :=
  (Finset.range h).filter fun j => 2 * 2 ^ j ≤ p

theorem card_stages_le (p h : ℕ) : (stages p h).card ≤ h := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range h)

theorem cover (p h r : ℕ) (hp : p < 2 ^ h) (hr : 0 < r) (hrp : r < p) :
    ∃ j ∈ stages p h, 2 ^ j ≤ r ∧ r < 2 ^ j + 3 * 2 ^ j := by
  classical
  let q := Nat.log 2 r
  have hq : q < h := Nat.log_lt_of_lt_pow (Nat.ne_of_gt hr) (hrp.trans hp)
  have hlo : 2 ^ q ≤ r := Nat.pow_log_le_self 2 (Nat.ne_of_gt hr)
  have hhi : r < 2 * 2 ^ q := by
    simpa [q, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) r
  by_cases ha : 2 * 2 ^ q ≤ p
  · refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq, ha⟩, hlo, ?_⟩
    omega
  · have hqpos : 0 < q := by
      by_contra hn
      have hqzero : q = 0 := by omega
      simp only [hqzero, pow_zero] at ha hhi
      omega
    have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
      conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ]
      omega
    refine ⟨q - 1, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), by omega⟩, ?_, ?_⟩
    · have hpos : 0 < 2 ^ (q - 1) := pow_pos (by decide) _
      omega
    · omega

end Dyadic

theorem list_length_le_cover_counts {A J : Type*} (xs : List A) (s : Finset J)
    (P : A → Prop) (Q : J → A → Prop) [DecidablePred P] [∀ j, DecidablePred (Q j)]
    (hcover : ∀ a ∈ xs, P a ∨ ∃ j ∈ s, Q j a) :
    xs.length ≤ xs.countP (fun a => decide (P a)) +
      ∑ j ∈ s, xs.countP (fun a => decide (Q j a)) := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ht := ih (fun b hb => hcover b (by simp [hb]))
    have hpoint : 1 ≤ (if P a then 1 else 0) +
        ∑ j ∈ s, if Q j a then 1 else 0 := by
      rcases hcover a (by simp) with h | ⟨j, hj, hq⟩
      · simp only [h, ↓reduceIte]
        omega
      · have hh := Finset.single_le_sum (f := fun j => if Q j a then 1 else 0)
          (fun _ _ => Nat.zero_le _) hj
        simp only [hq, ↓reduceIte] at hh
        omega
    simp only [List.length_cons, List.countP_cons, decide_eq_true_eq,
      Finset.sum_add_distrib]
    omega

theorem isChain_filter_interval {A : Type*} (rank : A → ℕ) (R : A → A → Prop)
    (t b : ℕ) (xs : List A) (hs : xs.Pairwise (fun a c => rank a < rank c))
    (hc : xs.IsChain R) :
    (xs.filter fun a => decide (t ≤ rank a ∧ rank a < t + b)).IsChain R := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hst := (List.pairwise_cons.mp hs).2
    have ht := ih hst hc.tail
    by_cases ha : t ≤ rank a ∧ rank a < t + b
    · cases xs with
      | nil => simp [ha]
      | cons c xs =>
        by_cases hcc : t ≤ rank c ∧ rank c < t + b
        · simp only [List.filter_cons, ha, hcc] at ht ⊢
          exact List.isChain_cons_cons.mpr ⟨(List.isChain_cons_cons.mp hc).1, ht⟩
        · have hac := (List.pairwise_cons.mp hs).1 c (by simp)
          have hhigh : t + b ≤ rank c := by omega
          have hz : ((c :: xs).filter fun a =>
              decide (t ≤ rank a ∧ rank a < t + b)) = [] := by
            apply List.length_eq_zero_iff.mp
            rw [← List.countP_eq_length_filter]
            apply List.countP_eq_zero.mpr
            intro x hx
            simp only [decide_eq_true_eq]
            intro hp
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have hcx := (List.pairwise_cons.mp hst).1 x hx
              omega
          simp only [List.filter_cons, ha, hz]
          simp
    · simpa only [List.filter_cons, ha, decide_false, Bool.false_eq_true, ↓reduceIte] using ht

namespace Graph

variable {V E : Type*} [Fintype E]
variable (G : Graph V E) (ρ : Rank E)

noncomputable def windowStates (_G : Graph V E) (ρ : Rank E)
    (t b : ℕ) (ds : List (Directed E)) :
    List (Directed E) :=
  ds.filter fun d => ρ d.1 ∈ Rank.window E t b

theorem validStack_window (t b : ℕ) {ds : List (Directed E)} (h : G.ValidStack ρ ds) :
    G.ValidStack ρ (G.windowStates ρ t b ds) := by
  refine ⟨fun d hd => h.1 d (List.mem_filter.mp hd).1, ?_⟩
  have hc := isChain_filter_interval (fun d : Directed E => ρ.index d.1)
    (G.StackStep ρ) t b ds (G.validStack_pairwise ρ h) h.2
  have heq : G.windowStates ρ t b ds =
      ds.filter (fun d => decide (t ≤ ρ.index d.1 ∧ ρ.index d.1 < t + b)) := by
    unfold windowStates
    apply List.filter_congr
    intro d _
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hd
      exact decide_eq_true ((Rank.mem_window t b (ρ d.1)).mp (of_decide_eq_true hd))
    · intro hd
      exact decide_eq_true ((Rank.mem_window t b (ρ d.1)).mpr (of_decide_eq_true hd))
  rw [heq]
  exact hc

theorem validStack_take (n : ℕ) {ds : List (Directed E)} (h : G.ValidStack ρ ds) :
    G.ValidStack ρ (ds.take n) :=
  ⟨fun d hd => h.1 d (List.mem_of_mem_take hd), h.2.take n⟩

theorem validStack_tail_residual (t : ℕ) {ds : List (Directed E)}
    (h : G.ValidStack ρ ds) (hlo : ∀ d ∈ ds, t ≤ ρ.index d.1) :
    ∀ d ∈ ds.tail, d.1 ∈ G.residual ρ t := by
  induction ds with
  | nil => simp
  | cons c ds ih =>
    cases ds with
    | nil => simp
    | cons a ds =>
      have hstep := (List.isChain_cons_cons.mp h.2).1
      intro d hd
      rcases List.mem_cons.mp hd with hda | hd
      · subst d
        exact G.stack_step_residual ρ c a t
          (h.1 c (by simp)) (h.1 a (by simp)) hstep (hlo c (by simp))
      · exact ih (G.validStack_tail ρ h) (fun d hd => hlo d (by simp [hd])) d hd

theorem hasWindowPath_of_many (t b Δ L : ℕ) {ds : List (Directed E)}
    (h : G.ValidStack ρ ds) (hg : G.DegreeGood t Δ ρ)
    (hmany : L < (G.windowStates ρ t b ds).length) :
    G.HasWindowPath t b Δ L ρ := by
  classical
  let ws := G.windowStates ρ t b ds
  have hw := G.validStack_window ρ t b h
  change G.ValidStack ρ ws at hw
  change L < ws.length at hmany
  have hmem (d : Directed E) (hd : d ∈ ws) : ρ d.1 ∈ Rank.window E t b :=
    of_decide_eq_true (List.mem_filter.mp hd).2
  have hlo : ∀ d ∈ ws, t ≤ ρ.index d.1 := by
    intro d hd
    exact ((Rank.mem_window t b _).mp (hmem d hd)).1
  have hres := G.validStack_tail_residual ρ t hw hlo
  cases he : ws with
  | nil => simp [he] at hmany
  | cons c parents =>
    have hpar : G.ValidStack ρ parents := G.validStack_tail ρ (he ▸ hw)
    have hres' : ∀ d ∈ parents, d.1 ∈ G.residual ρ t := by
      simpa only [he, List.tail_cons] using hres
    let zs := parents.take L
    let rs := zs.map fun d => ρ d.1
    have hz : G.ValidStack ρ zs := G.validStack_take ρ L hpar
    have hlen : zs.length = L := by
      have hlp : L ≤ parents.length := by simpa [he] using hmany
      exact List.length_take_of_le hlp
    have hpair := G.validStack_pairwise ρ hz
    have hrn : rs.Nodup := by
      rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
      exact hpair.imp (fun hlt heq => by
        have heq' := congrArg Fin.val heq
        exact (ne_of_lt hlt) heq')
    have hsorted : rs.Pairwise (· ≤ ·) := by
      rw [List.pairwise_map]
      exact hpair.imp (fun hlt => hlt.le)
    have hrsort : rs.toFinset.sort (· ≤ ·) = rs :=
      (List.toFinset_sort (· ≤ ·) hrn).mpr hsorted
    have hsub : rs.toFinset ⊆ Rank.window E t b := by
      intro i hi
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      exact hmem d (by rw [he]; exact List.mem_cons_of_mem _ (List.mem_of_mem_take hd))
    have hcard : rs.toFinset.card = L := by
      rw [List.toFinset_card_of_nodup hrn, List.length_map, hlen]
    have hp : G.PositionPath t Δ rs ρ := by
      refine ⟨hg, ?_, ?_⟩
      · intro i hi
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hi
        rw [Rank.at_index]
        exact hres' d (List.mem_of_mem_take hd)
      · rw [List.isChain_map]
        apply hz.2.imp
        intro a b hs
        simp only [Rank.at_index]
        exact ⟨G.tail a, G.tail_incident a, by rw [hs.2]; exact G.head_incident b⟩
    refine ⟨rs.toFinset, Finset.mem_powersetCard.mpr ⟨hsub, hcard⟩, ?_⟩
    rw [hrsort]
    exact hp

theorem windowStates_length_le (t b Δ L : ℕ) {ds : List (Directed E)}
    (h : G.ValidStack ρ ds) (hg : G.DegreeGood t Δ ρ)
    (hn : ¬ G.HasWindowPath t b Δ L ρ) :
    (G.windowStates ρ t b ds).length ≤ L := by
  by_contra hm
  exact hn (G.hasWindowPath_of_many ρ t b Δ L h hg (Nat.lt_of_not_ge hm))

theorem validStack_dyadic_length (h L : ℕ)
    (hp : Fintype.card E < 2 ^ h) (Δ : ℕ → ℕ)
    (hgood : ∀ j ∈ Dyadic.stages (Fintype.card E) h,
      G.DegreeGood (2 ^ j) (Δ j) ρ ∧ ¬ G.HasWindowPath (2 ^ j) (3 * 2 ^ j) (Δ j) L ρ)
    {ds : List (Directed E)} (hs : G.ValidStack ρ ds) :
    ds.length ≤ 1 + h * L := by
  classical
  let S := Dyadic.stages (Fintype.card E) h
  have hcover := list_length_le_cover_counts ds S
    (fun d => ρ.index d.1 = 0)
    (fun j d => ρ d.1 ∈ Rank.window E (2 ^ j) (3 * 2 ^ j))
    (fun d _ => by
      by_cases hz : ρ.index d.1 = 0
      · exact Or.inl hz
      · obtain ⟨j, hj, hlo, hhi⟩ := Dyadic.cover (Fintype.card E) h (ρ.index d.1)
          hp (Nat.pos_of_ne_zero hz) (ρ.index_lt d.1)
        exact Or.inr ⟨j, hj, (Rank.mem_window _ _ _).mpr ⟨hlo, hhi⟩⟩)
  have hpair := G.validStack_pairwise ρ hs
  have hrn : (ds.map fun d => ρ.index d.1).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    exact hpair.imp (fun hlt => ne_of_lt hlt)
  have hzero : ds.countP (fun d => decide (ρ.index d.1 = 0)) ≤ 1 := by
    have hh := nodup_countP_eq_le_one (ds.map fun d => ρ.index d.1) id 0 hrn
      Function.injective_id
    simpa only [List.countP_map, Function.comp_def, id_eq] using hh
  have hstage (j : ℕ) (hj : j ∈ S) :
      ds.countP (fun d => decide (ρ d.1 ∈ Rank.window E (2 ^ j) (3 * 2 ^ j))) ≤ L := by
    rw [List.countP_eq_length_filter]
    exact G.windowStates_length_le ρ _ _ (Δ j) L hs (hgood j hj).1 (hgood j hj).2
  have hsum : (∑ j ∈ S, ds.countP
      (fun d => decide (ρ d.1 ∈ Rank.window E (2 ^ j) (3 * 2 ^ j)))) ≤ h * L := by
    calc
      _ ≤ ∑ _j ∈ S, L := Finset.sum_le_sum fun j hj => hstage j hj
      _ = S.card * L := by simp
      _ ≤ h * L := Nat.mul_le_mul_right L (Dyadic.card_stages_le _ _)
  omega

end Graph

end SteinerUpperBound.Matching

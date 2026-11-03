module

public import SteinerUpperBound.Matching.Padded.Resource

@[expose] public section

/-!
# Binary search with exact rational interval masses

`sample` evaluates the supplied arithmetic mass routine, samples a rational
Bernoulli using `IntegerCoin.sample`, and descends into one half. Its execution
does not enumerate the support of the distribution.
-/

namespace SteinerUpperBound.Matching.Padded.Binary

open SteinerLowerBound
open scoped Classical BigOperators

def total (w : ℕ → ℚ) (lo len : ℕ) : ℚ := ∑ i ∈ Finset.range len, w (lo + i)

def weighted (w : ℕ → ℚ) (f : ℕ → ℝ) (lo len : ℕ) : ℝ :=
  ∑ i ∈ Finset.range len, (w (lo + i) : ℝ) * f (lo + i)

theorem total_nonneg (w : ℕ → ℚ) (hw : ∀ i, 0 ≤ w i) (lo len : ℕ) :
    0 ≤ total w lo len :=
  Finset.sum_nonneg fun i _ => hw (lo + i)

theorem total_split (w : ℕ → ℚ) (lo len left : ℕ) (hl : left ≤ len) :
    total w lo len = total w lo left + total w (lo + left) (len - left) := by
  unfold total
  conv_lhs => rw [← Nat.add_sub_of_le hl]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  omega

theorem weighted_split (w : ℕ → ℚ) (f : ℕ → ℝ) (lo len left : ℕ) (hl : left ≤ len) :
    weighted w f lo len = weighted w f lo left + weighted w f (lo + left) (len - left) := by
  unfold weighted
  conv_lhs => rw [← Nat.add_sub_of_le hl]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [show lo + (left + i) = lo + left + i by omega]

theorem weighted_eq_zero (w : ℕ → ℚ) (hw : ∀ i, 0 ≤ w i) (f : ℕ → ℝ)
    (lo len : ℕ) (hzero : total w lo len = 0) : weighted w f lo len = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hwi := Finset.single_le_sum (f := fun j => w (lo + j)) (fun j _ => hw _) hi
  have hz : w (lo + i) = 0 := le_antisymm (hwi.trans_eq hzero) (hw _)
  simp [hz]

def sample (massFn : ℕ → ℕ → Arithmetic ℚ) : ℕ → ℕ → ℕ → Program ℕ ℕ
  | 0, lo, _ => .tick 1 (.ret lo)
  | h + 1, lo, len =>
    if len ≤ 1 then .tick 1 (.ret lo) else
      let left := len / 2
      let m := massFn lo len
      let l := massFn lo left
      .tick (m.operations + l.operations + 12)
        (if m.value ≤ 0 then .ret lo else
          (IntegerCoin.sample (l.value / m.value)).bind fun b =>
            match b with
            | true => sample massFn h lo left
            | false => sample massFn h (lo + left) (len - left))

theorem halves (h len : ℕ) (hl : 1 < len) (hp : len ≤ 2 ^ (h + 1)) :
    0 < len / 2 ∧ 0 < len - len / 2 ∧
      len / 2 ≤ 2 ^ h ∧ len - len / 2 ≤ 2 ^ h := by
  have hd := Nat.div_add_mod len 2
  have hm := Nat.mod_lt len (by decide : 0 < 2)
  rw [pow_succ] at hp
  omega

theorem sample_supported (massFn : ℕ → ℕ → Arithmetic ℚ) (h lo len : ℕ)
    (hl : 0 < len) (hp : len ≤ 2 ^ h) :
    (sample massFn h lo len).Supported (fun i => lo ≤ i ∧ i < lo + len) := by
  induction h generalizing lo len with
  | zero =>
    have he : len = 1 := by simpa using Nat.le_antisymm hp hl
    subst len
    intro x
    change lo ≤ lo ∧ lo < lo + 1
    exact ⟨le_refl _, by omega⟩
  | succ h ih =>
    by_cases hlen : len ≤ 1
    · have he : len = 1 := by omega
      subst len
      simp only [sample, le_refl, ↓reduceIte]
      exact Program.supported_tick _ _ _ (Program.supported_ret _ _ ⟨by omega, by omega⟩)
    · have hh := halves h len (by omega) hp
      rw [sample]
      simp only [hlen, ↓reduceIte]
      apply Program.supported_tick
      split_ifs
      · exact Program.supported_ret _ _ ⟨by omega, by omega⟩
      · refine Program.supported_bind
          (IntegerCoin.sample ((massFn lo (len / 2)).value / (massFn lo len).value))
          (fun b => match b with
            | true => sample massFn h lo (len / 2)
            | false => sample massFn h (lo + len / 2) (len - len / 2))
          (fun _ => True) (fun i => lo ≤ i ∧ i < lo + len) (fun _ => trivial) ?_
        intro b _
        cases b
        · change (sample massFn h (lo + len / 2) (len - len / 2)).Supported
            (fun i => lo ≤ i ∧ i < lo + len)
          have hs := ih (lo + len / 2) (len - len / 2) hh.2.1 hh.2.2.2
          intro x
          have hx := hs x
          exact ⟨by omega, by omega⟩
        · change (sample massFn h lo (len / 2)).Supported
            (fun i => lo ≤ i ∧ i < lo + len)
          have hs := ih lo (len / 2) hh.1 hh.2.2.1
          intro x
          have hx := hs x
          exact ⟨hx.1, by omega⟩

/-- Exact unnormalized law, including zero-mass intervals and the terminal leaf. -/
theorem sample_weighted (massFn : ℕ → ℕ → Arithmetic ℚ)
    (w : ℕ → ℚ) (hw : ∀ i, 0 ≤ w i) (cap : ℕ)
    (hmass : ∀ lo len, lo + len ≤ cap → (massFn lo len).value = total w lo len)
    (h lo len : ℕ) (hl : 0 < len) (hp : len ≤ 2 ^ h) (hcap : lo + len ≤ cap)
    (f : ℕ → ℝ) :
    ((massFn lo len).value : ℝ) * (sample massFn h lo len).expect f = weighted w f lo len := by
  induction h generalizing lo len with
  | zero =>
    have he : len = 1 := by simpa using Nat.le_antisymm hp hl
    subst len
    simp [sample, hmass lo 1 hcap, total, weighted]
  | succ h ih =>
    by_cases hlen : len ≤ 1
    · have he : len = 1 := by omega
      subst len
      simp [sample, hmass lo 1 hcap, total, weighted]
    · have hh := halves h len (by omega) hp
      have hleft : len / 2 ≤ len := Nat.div_le_self _ _
      have hcapL : lo + len / 2 ≤ cap := by omega
      have hcapR : (lo + len / 2) + (len - len / 2) ≤ cap := by omega
      have hM : 0 ≤ (massFn lo len).value := by
        rw [hmass lo len hcap]
        exact total_nonneg w hw lo len
      by_cases hzero : (massFn lo len).value ≤ 0
      · have hz : (massFn lo len).value = 0 := le_antisymm hzero hM
        have htz : total w lo len = 0 := (hmass lo len hcap).symm.trans hz
        rw [hz, Rat.cast_zero, zero_mul, weighted_eq_zero w hw f lo len htz]
      · have hpos : 0 < (massFn lo len).value := lt_of_not_ge hzero
        have hL : 0 ≤ (massFn lo (len / 2)).value := by
          rw [hmass lo (len / 2) hcapL]
          exact total_nonneg w hw lo (len / 2)
        have hR : 0 ≤ (massFn (lo + len / 2) (len - len / 2)).value := by
          rw [hmass _ _ hcapR]
          exact total_nonneg w hw _ _
        have hadd : (massFn lo len).value =
            (massFn lo (len / 2)).value + (massFn (lo + len / 2) (len - len / 2)).value := by
          rw [hmass lo len hcap, hmass lo (len / 2) hcapL, hmass _ _ hcapR]
          exact total_split w lo len (len / 2) hleft
        have hq0 : 0 ≤ (massFn lo (len / 2)).value / (massFn lo len).value :=
          div_nonneg hL hpos.le
        have hq1 : (massFn lo (len / 2)).value / (massFn lo len).value ≤ 1 :=
          (div_le_one hpos).mpr (by linarith)
        have hiL := ih lo (len / 2) hh.1 hh.2.2.1 hcapL
        have hiR := ih (lo + len / 2) (len - len / 2) hh.2.1 hh.2.2.2 hcapR
        rw [sample]
        simp only [hlen, hzero, ↓reduceIte, Program.expect_tick, Program.expect_bind]
        rw [IntegerCoin.expect_sample _ hq0 hq1]
        simp only
        have hposR : (0 : ℝ) < ((massFn lo len).value : ℝ) := by exact_mod_cast hpos
        have haddR : ((massFn lo len).value : ℝ) =
            ((massFn lo (len / 2)).value : ℝ) +
              ((massFn (lo + len / 2) (len - len / 2)).value : ℝ) := by exact_mod_cast hadd
        have hqL : ((massFn lo len).value : ℝ) *
            (((massFn lo (len / 2)).value / (massFn lo len).value : ℚ) : ℝ) =
              ((massFn lo (len / 2)).value : ℝ) := by
          rw [Rat.cast_div]
          field_simp
        have hqR : ((massFn lo len).value : ℝ) *
            (1 - (((massFn lo (len / 2)).value / (massFn lo len).value : ℚ) : ℝ)) =
              ((massFn (lo + len / 2) (len - len / 2)).value : ℝ) := by nlinarith
        calc
          _ = (((massFn lo len).value : ℝ) *
                (((massFn lo (len / 2)).value / (massFn lo len).value : ℚ) : ℝ)) *
                  (sample massFn h lo (len / 2)).expect f +
              (((massFn lo len).value : ℝ) *
                (1 - (((massFn lo (len / 2)).value / (massFn lo len).value : ℚ) : ℝ))) *
                  (sample massFn h (lo + len / 2) (len - len / 2)).expect f := by ring
          _ = weighted w f lo (len / 2) +
              weighted w f (lo + len / 2) (len - len / 2) := by rw [hqL, hqR, hiL, hiR]
          _ = _ := (weighted_split w f lo len (len / 2) hleft).symm

theorem sample_cost_bound (massFn : ℕ → ℕ → Arithmetic ℚ) (cap M : ℕ)
    (hops : ∀ lo len, lo + len ≤ cap → (massFn lo len).operations ≤ M)
    (h lo len : ℕ) (hcap : lo + len ≤ cap) :
    (sample massFn h lo len).Bound (fun n : ℕ => (n : ℝ)) 1 (fun _ => 0)
      ((h + 1 : ℕ) * (2 * M + 16) : ℕ) := by
  induction h generalizing lo len with
  | zero =>
    intro x
    simp only [sample, Program.cost, Nat.cast_one, add_zero]
    push_cast
    nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  | succ h ih =>
    by_cases hlen : len ≤ 1
    · rw [sample]
      simp only [hlen, ↓reduceIte]
      intro x
      simp only [Program.cost, Nat.cast_one, add_zero]
      push_cast
      nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
    · have hleft : len / 2 ≤ len := Nat.div_le_self _ _
      have hcapL : lo + len / 2 ≤ cap := by omega
      have hcapR : (lo + len / 2) + (len - len / 2) ≤ cap := by omega
      have hm : ((massFn lo len).operations : ℝ) ≤ M := by exact_mod_cast hops lo len hcap
      have hl : ((massFn lo (len / 2)).operations : ℝ) ≤ M := by
        exact_mod_cast hops lo (len / 2) hcapL
      rw [sample]
      simp only [hlen, ↓reduceIte]
      split_ifs with hzero
      · intro x
        change (((massFn lo len).operations + (massFn lo (len / 2)).operations + 12 : ℕ) : ℝ) +
          0 + 0 ≤ ((h + 1 + 1 : ℕ) * (2 * M + 16) : ℕ)
        push_cast
        nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M), (Nat.cast_nonneg h : (0 : ℝ) ≤ h)]
      · let childBudget : ℝ := ((h + 1 : ℕ) * (2 * M + 16) : ℕ)
        have hb := Program.bound_bind
          (IntegerCoin.sample ((massFn lo (len / 2)).value / (massFn lo len).value))
          (fun b => match b with
            | true => sample massFn h lo (len / 2)
            | false => sample massFn h (lo + len / 2) (len - len / 2))
          (fun n : ℕ => (n : ℝ)) 1 (fun _ => childBudget) (fun _ => 0)
          (4 + childBudget)
          (fun x => by rw [IntegerCoin.cost_sample])
          (fun b => by
            cases b
            · exact ih (lo + len / 2) (len - len / 2) hcapR
            · exact ih lo (len / 2) hcapL)
        intro x
        have hx := hb x
        change (((massFn lo len).operations + (massFn lo (len / 2)).operations + 12 : ℕ) : ℝ) +
          _ + 0 ≤ ((h + 1 + 1 : ℕ) * (2 * M + 16) : ℕ)
        dsimp only [childBudget] at hx
        push_cast at hx ⊢
        nlinarith

end SteinerUpperBound.Matching.Padded.Binary

module

public import SteinerUpperBound.Covers.Basic

@[expose] public section

namespace SteinerUpperBound.Covers.ClosedRelation

open scoped Classical BigOperators

variable {U : Type*} [Fintype U]

noncomputable def ball (R : U → U → Prop) (x : U) : ℕ → Finset U
  | 0 => {x}
  | n + 1 => Finset.univ.filter (fun y => ∃ z ∈ ball R x n, R z y)

theorem mem_ball_self (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) (n : ℕ) : x ∈ ball R x n := by
  classical
  induction n with
  | zero => simp [ball]
  | succ n ih => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, ih, hrefl x⟩

theorem ball_subset_succ (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) (n : ℕ) : ball R x n ⊆ ball R x (n + 1) := by
  classical
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, hrefl y⟩

theorem ball_mono (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) : Monotone (ball R x) :=
  monotone_nat_of_le_succ (ball_subset_succ R hrefl x)

theorem neighborhood_subset_ball (R : U → U → Prop)
    (x y : U) (n : ℕ) (hy : y ∈ ball R x n) :
    neighborhood R y ⊆ ball R x (n + 1) := by
  classical
  intro z hz
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, y, hy, (Finset.mem_filter.mp hz).2⟩

/-- Binary growth is used in place of the manuscript's real-exponential growth.
It changes the failure exponent from `-ψ/e` to the stronger `-ψ/2`. -/
theorem exists_slow_growth (R : U → U → Prop) (x : U) (h : ℕ)
    (hh : Fintype.card U < 2 ^ h) :
    ∃ j < h, (ball R x (j + 1)).card ≤ 2 * (ball R x j).card := by
  classical
  by_contra hn
  push_neg at hn
  have hg : ∀ n ≤ h, 2 ^ n ≤ (ball R x n).card := by
    intro n
    induction n with
    | zero => simp [ball]
    | succ n ih =>
      intro hnh
      have hnlt : n < h := by omega
      have hi := ih (by omega)
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; omega
        _ ≤ 2 * (ball R x n).card := Nat.mul_le_mul_left _ hi
        _ ≤ (ball R x (n + 1)).card := (hn n hnlt).le
  have hb : (ball R x h).card ≤ Fintype.card U := Finset.card_le_univ _
  exact (not_le_of_gt hh) ((hg h le_rfl).trans hb)

theorem ball_reciprocal_lower (R : U → U → Prop) (hrefl : ∀ x, R x x)
    (x : U) (h : ℕ) (hh : Fintype.card U < 2 ^ h) :
    (1 / 2 : ℝ) ≤ ∑ y ∈ ball R x h, (degree R y : ℝ)⁻¹ := by
  classical
  obtain ⟨j, hj, hslow⟩ := exists_slow_growth R x h hh
  have hbpos : (0 : ℝ) < (ball R x j).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨x, mem_ball_self R hrefl x j⟩
  have hsmall : (1 / 2 : ℝ) ≤ ∑ y ∈ ball R x j, (degree R y : ℝ)⁻¹ := by
    calc
      (1 / 2 : ℝ) = (ball R x j).card * (2 * (ball R x j).card : ℝ)⁻¹ := by
        field_simp
      _ = ∑ _y ∈ ball R x j, (2 * (ball R x j).card : ℝ)⁻¹ := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro y hy
        apply inv_anti₀ (by exact_mod_cast degree_pos R hrefl y)
        have hd : degree R y ≤ (ball R x (j + 1)).card :=
          Finset.card_le_card (neighborhood_subset_ball R x y j hy)
        exact_mod_cast hd.trans hslow
  exact hsmall.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (ball_mono R hrefl x hj.le) (fun _ _ _ => by positivity))

end SteinerUpperBound.Covers.ClosedRelation

namespace SteinerUpperBound.Covers

theorem ball_distance {V : Type*} (I : Instance V) {r : ℝ} (hr : 0 ≤ r)
    (x : Terminal I) (n : ℕ) :
    ∀ y ∈ ClosedRelation.ball (near I r) x n, I.distance x.val y.val ≤ (n : ℝ) * r := by
  classical
  induction n with
  | zero =>
    intro y hy
    have he : y = x := by simpa [ClosedRelation.ball] using hy
    subst y
    simp [I.distance_self]
  | succ n ih =>
    intro y hy
    obtain ⟨z, hz, hzy⟩ := (Finset.mem_filter.mp hy).2
    have hzdist := ih z hz
    have htriangle := I.distance_triangle x.val z.val y.val
    dsimp [near] at hzy
    push_cast
    nlinarith

end SteinerUpperBound.Covers

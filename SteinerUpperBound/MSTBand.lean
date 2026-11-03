module

public import SteinerUpperBound.MSTRankIntegral

@[expose] public section

namespace SteinerUpperBound.TerminalMST

open MeasureTheory
open scoped Classical Interval

variable {V : Type*} [Fintype V]

noncomputable def clipped (w : Sym2 V → ℝ) (lo hi : ℝ) (e : Sym2 V) : ℝ :=
  min (max (w e - lo) 0) (hi - lo)

theorem clipped_nonneg (w : Sym2 V → ℝ) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    ∀ e, 0 ≤ clipped w lo hi e :=
  fun _ => le_min (le_max_right _ _) (sub_nonneg.mpr hlohi)

theorem clipped_le_width (w : Sym2 V → ℝ) (lo hi : ℝ) :
    ∀ e, clipped w lo hi e ≤ hi - lo :=
  fun _ => min_le_right _ _

theorem clipped_lt (w : Sym2 V → ℝ) (lo hi t : ℝ) (ht : 0 < t) (hthi : t ≤ hi - lo)
    (e : Sym2 V) : clipped w lo hi e < t ↔ w e < lo + t := by
  have hn : ¬hi - lo < t := not_lt.mpr hthi
  simp only [clipped, min_lt_iff, max_lt_iff, hn, or_false, ht, and_true]
  constructor <;> intro h <;> linarith

theorem below_clipped (w : Sym2 V → ℝ) (T : Finset V) (lo hi t : ℝ)
    (ht : 0 < t) (hthi : t ≤ hi - lo) :
    below (clipped w lo hi) T t = below w T (lo + t) := by
  ext x y
  simp only [below_adj, clipped_lt w lo hi t ht hthi]

theorem clipped_value_difference (w : Sym2 V → ℝ) (T : Finset V) (F : SimpleGraph V)
    (hF : Network.TerminalOnly T F) (lo hi : ℝ) (hlohi : lo ≤ hi) :
    value (clipped w lo hi) T - value (zeroed (clipped w lo hi) F) T =
      ∫ a in lo..hi, GraphRank.gain (below w T a) F := by
  have hwidth : 0 ≤ hi - lo := sub_nonneg.mpr hlohi
  have he := value_difference_integral (clipped w lo hi) T F
    (clipped_nonneg w lo hi hlohi) hF (hi - lo) hwidth
    (fun e _ => clipped_le_width w lo hi e)
  calc
    _ = ∫ t in (0 : ℝ)..(hi - lo), GraphRank.gain (below (clipped w lo hi) T t) F := he
    _ = ∫ t in (0 : ℝ)..(hi - lo), GraphRank.gain (below w T (lo + t)) F := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [Set.uIoc_of_le hwidth] at ht
      rw [below_clipped w T lo hi t ht.1 ht.2]
    _ = _ := by
      have h := intervalIntegral.integral_comp_add_left
        (a := 0) (b := hi - lo) (fun a => GraphRank.gain (below w T a) F) lo
      have hhi : lo + (hi - lo) = hi := by ring
      simpa only [add_zero, hhi] using h

end SteinerUpperBound.TerminalMST

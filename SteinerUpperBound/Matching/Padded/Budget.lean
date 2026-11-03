module

public import SteinerUpperBound.Matching.Padded.Execution
public import SteinerUpperBound.Matching.Padded.CollectionCredit

@[expose] public section

namespace SteinerUpperBound.Matching.Padded.Parameters

open SteinerLowerBound
open scoped Classical

variable {V E : Type*} {G : Graph V E} (S : Slots G) [Fintype V] [Fintype E] (P : Parameters S)

theorem copies_le_Nstar : Fintype.card E ≤ P.Nstar := by
  have hs := S.copies_le_slots
  have hp := P.size_le
  omega

theorem rankCard_ge_power : P.Nstar ^ 32 ≤ P.rankCard := by
  have hh : P.Nstar ≤ 2 ^ P.logarithm := (Nstar_lt_pow S P).le
  calc
    P.Nstar ^ 32 ≤ (2 ^ P.logarithm) ^ 32 := by gcongr
    _ = P.rankCard := by simp only [rankCard, rankExponent, ← pow_mul, Nat.mul_comm]

theorem tie_budget (v : V) :
    (Execution.law S P v).prob {x | ¬ Function.Injective x.2} ≤
      1 / (P.Nstar : ℝ) ^ 30 := by
  have hN : (0 : ℝ) < P.Nstar := by exact_mod_cast (show 0 < P.Nstar by have := P.two_le; omega)
  have hQ : (0 : ℝ) < P.rankCard := by exact_mod_cast P.rankCard_pos
  have hp : (Fintype.card E : ℝ) ≤ P.Nstar := by exact_mod_cast copies_le_Nstar S P
  have hpower : (P.Nstar : ℝ) ^ 32 ≤ P.rankCard := by exact_mod_cast rankCard_ge_power S P
  apply (Execution.ties_probability S P v).trans
  apply (div_le_div_iff₀ hQ (pow_pos hN 30)).mpr
  have hsq : (Fintype.card E : ℝ) ^ 2 ≤ (P.Nstar : ℝ) ^ 2 := by gcongr
  calc
    _ ≤ (P.Nstar : ℝ) ^ 2 * (P.Nstar : ℝ) ^ 30 :=
      mul_le_mul_of_nonneg_right hsq (pow_nonneg hN.le _)
    _ = (P.Nstar : ℝ) ^ 32 := by rw [← pow_add]
    _ ≤ _ := by simpa only [one_mul] using hpower

def bucketCoefficient : ℕ :=
  Cache.extensionCoefficient (P.rankExponent + 1) P.sortHeight P.Nstar

theorem bucketCoefficient_bound (v : V) :
    Cache.extensionCoefficient (P.rankExponent + 1) P.sortHeight (S.length v) ≤ bucketCoefficient S P := by
  have hn := (length_lt_Nstar S P v).le
  have hg := Sparse.operationBound_mono hn
  dsimp only [bucketCoefficient, Cache.extensionCoefficient, Sparse.operationBound]
  omega

end SteinerUpperBound.Matching.Padded.Parameters

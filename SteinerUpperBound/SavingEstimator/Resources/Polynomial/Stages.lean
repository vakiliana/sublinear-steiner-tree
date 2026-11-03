module

public import SteinerUpperBound.SavingEstimator.Resources.Polynomial.Prefixes

@[expose] public section

set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

namespace SteinerUpperBound.SavingEstimator.Resources

open EstimatorParameters
open PortGraph.RuntimeAdapter.Averaged
open scoped Classical

theorem pool_le_monomial (kind : CounterKind) (n : ℕ) :
    NsPool n ≤ monomial kind n 1 1 2 := by
  have hh := Nat.mul_le_mul_left (magnitude * t n * ell n ^ 2)
    (Nat.succ_le_of_lt (space_pos kind n))
  calc
    _ ≤ magnitude * t n * ell n ^ 2 := pool_bound n
    _ ≤ (magnitude * t n * ell n ^ 2) * space kind n := by simpa only [Nat.mul_one] using hh
    _ = _ := by unfold monomial; ring

theorem poolProposal_bound (n k : ℕ) (hk : k + 1 ≤ n) :
    (closed n (k + 1)).poolProposals ≤ monomial .ordinary n 1 2 3 := by
  have hc := Nat.mul_le_mul (show k + 1 ≤ n + 1 by omega) (poolClock_bound n)
  have hh := Nat.mul_le_mul (pool_bound n) hc
  change NsPool n * ((k + 1) * poolClock n) ≤ _
  convert hh using 1 <;> norm_num only [monomial, space] <;> ring

theorem reusableWork_bound (n : ℕ) :
    ReusableSample.OracleProgram.workBound n (NsPool n) ≤ monomial .ordinary n 384 2 3 := by
  have hl : 1 ≤ magnitude * t n * ell n ^ 2 :=
    Nat.mul_le_mul (Nat.mul_le_mul magnitude_one (Nat.succ_le_of_lt (t_pos n)))
      (one_le_pow₀ (ell_ge_one n))
  have hp : NsPool n + 1 ≤ 2 * magnitude * t n * ell n ^ 2 := by
    nlinarith only [pool_bound n, hl]
  have he : 1 ≤ magnitude * ell n := Nat.mul_le_mul magnitude_one (ell_ge_one n)
  have hlog : Nat.log2 (NsPool n + 1) + 2 ≤ 3 * magnitude * ell n := by
    nlinarith only [poolCount_log_bound n, he]
  calc
    _ ≤ 64 * (n + 1) * (NsPool n + 1) * (Nat.log2 (NsPool n + 1) + 2) :=
      ReusableSample.OracleProgram.workBound_le n (NsPool n)
    _ ≤ 64 * (n + 1) * (2 * magnitude * t n * ell n ^ 2) * (3 * magnitude * ell n) := by
      gcongr
    _ = _ := by unfold monomial space; ring

theorem deletionBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    deletionBase kind n k ≤ monomial kind n (2 ^ 12) 2 3 := by
  cases kind
  · let A := monomial .ordinary n 1 2 3
    have hp : (closed n (k + 1)).poolProposals ≤ A := poolProposal_bound n k hk
    have hs : NsPool n ≤ A :=
      (pool_le_monomial .ordinary n).trans
        (monomial_mono .ordinary n 1 1 1 2 2 3 (le_refl _) (by omega) (by omega))
    have h1 : 1 ≤ A :=
      (unit_le_monomial .ordinary n).trans
        (monomial_mono .ordinary n 1 1 0 2 0 3 (le_refl _) (by omega) (by omega))
    have hw : ReusableSample.OracleProgram.workBound n (NsPool n) ≤ 384 * A :=
      (reusableWork_bound n).trans_eq (monomial_coefficient .ordinary n 384 2 3)
    have ht1 : 1 ≤ t n := t_pos n
    have hr : (2 * t n + 12) * n + 16 ≤ monomial .ordinary n 30 0 0 := by
      have hm := Nat.mul_le_mul_right n (show 2 * t n + 12 ≤ 14 * t n by omega)
      have hunit := Nat.mul_le_mul_left 16 (unit_le_monomial .ordinary n)
      norm_num only [monomial, space, pow_zero, Nat.mul_one, Nat.one_mul] at hunit ⊢
      nlinarith only [hm, hunit]
    have hr' : (2 * t n + 12) * n + 16 ≤ 30 * A :=
      (hr.trans (monomial_mono .ordinary n 30 30 0 2 0 3 (le_refl _) (by omega) (by omega))).trans_eq
        (monomial_coefficient .ordinary n 30 2 3)
    have hh :
        16 * ((closed n (k + 1)).poolProposals + NsPool n + 1) +
          ReusableSample.OracleProgram.workBound n (NsPool n) + ((2 * t n + 12) * n + 16) ≤
            4096 * A := by
      nlinarith only [hp, hs, h1, hw, hr']
    change 16 * ((closed n (k + 1)).poolProposals + NsPool n + 1) +
      ReusableSample.OracleProgram.workBound n (NsPool n) + (2 * t n + 12) * n + 16 ≤ _
    convert hh using 1 <;> norm_num only [A, monomial] <;> ring
  · exact (pool_le_monomial .positive n).trans
      (monomial_mono .positive n 1 (2 ^ 12) 1 2 2 3 (by norm_num) (by omega) (by omega))

theorem smallBase_bound (kind : CounterKind) (n k : ℕ) (hk : k + 1 ≤ n) :
    smallBase kind n k ≤ monomial kind n (2 ^ 24) 4 28 := by
  let L := LargeCoverProgram.smallLimit (closed n (k + 1))
  have hL : L ≤ 10 * magnitude * t n * ell n ^ 9 := by
    rw [show L = 10 * B n * t n from smallLimit_eq n (k + 1)]
    have hh := Nat.mul_le_mul_left (10 * t n) (cutoff_bound n)
    convert hh using 1 <;> ring
  cases kind
  · let A := monomial .ordinary n 1 4 28
    have htCube : t n ^ 3 ≤ 2 * (n + 1) * t n := by
      have hh := Nat.mul_le_mul_right (t n) (t_sq_le n)
      convert hh using 1 <;> ring
    have hCube : L ^ 3 ≤ 2000 * magnitude ^ 3 * (n + 1) * t n * ell n ^ 27 := by
      calc
        _ ≤ (10 * magnitude * t n * ell n ^ 9) ^ 3 := Nat.pow_le_pow_left hL 3
        _ = 1000 * magnitude ^ 3 * t n ^ 3 * ell n ^ 27 := by ring
        _ ≤ 1000 * magnitude ^ 3 * (2 * (n + 1) * t n) * ell n ^ 27 := by gcongr
        _ = _ := by ring
    have hlog : 1 + Nat.log2 (L + 1) ≤ 11 * magnitude * ell n := by
      simpa only [L, Nat.add_comm] using smallCount_log_bound n (k + 1)
    have hfull : L ^ 3 * (1 + Nat.log2 (L + 1)) ≤ 22000 * A := by
      have hh := Nat.mul_le_mul hCube hlog
      convert hh using 1 <;> norm_num only [A, monomial, space] <;> ring
    have hfirst : n * L ≤ monomial .ordinary n 10 1 9 := by
      calc
        _ ≤ n * (10 * magnitude * t n * ell n ^ 9) := Nat.mul_le_mul_left n hL
        _ ≤ (n + 1) * (10 * magnitude * t n * ell n ^ 9) :=
          Nat.mul_le_mul_right _ (Nat.le_succ n)
        _ = _ := by unfold monomial space; ring
    have hfirst' : n * L ≤ 10 * A :=
      (hfirst.trans (monomial_mono .ordinary n 10 10 1 4 9 28 (le_refl _) (by omega) (by omega))).trans_eq
        (monomial_coefficient .ordinary n 10 4 28)
    have hhead : 16 * (k + 2) ≤ monomial .ordinary n 16 0 0 := by
      have ht1 : 1 ≤ t n := t_pos n
      have hh := Nat.mul_le_mul (show k + 2 ≤ n + 1 by omega) ht1
      have h16 := Nat.mul_le_mul_left 16 hh
      convert h16 using 1 <;> norm_num only [monomial, space] <;> ring
    have hhead' : 16 * (k + 2) ≤ 16 * A :=
      (hhead.trans (monomial_mono .ordinary n 16 16 0 4 0 28 (le_refl _) (by omega) (by omega))).trans_eq
        (monomial_coefficient .ordinary n 16 4 28)
    have hh : 16 * (k + 2) + 128 * (n * L + L ^ 3 * (1 + Nat.log2 (L + 1))) ≤ 2 ^ 24 * A := by
      nlinarith only [hhead', hfirst', hfull]
    change 16 * (k + 2) + 128 * (n * L + L ^ 3 * (1 + Nat.log2 (L + 1))) ≤ _
    exact hh.trans_eq (monomial_coefficient .ordinary n (2 ^ 24) 4 28).symm
  · have hh : L ≤ monomial .positive n 10 1 9 := by
      convert hL using 1 <;> norm_num only [monomial, space] <;> ring
    exact hh.trans (monomial_mono .positive n 10 (2 ^ 24) 1 4 9 28 (by norm_num) (by omega) (by omega))

end SteinerUpperBound.SavingEstimator.Resources

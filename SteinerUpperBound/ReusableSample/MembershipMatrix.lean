module

public import SteinerUpperBound.ReusableSample.Arithmetic

@[expose] public section

namespace SteinerUpperBound.ReusableSample

open SteinerLowerBound
open scoped BigOperators Classical

section Matrix

variable {I : Type*} [DecidableEq I]

def matrixHits (L : Finset I) (row : I → Bool) : Finset I :=
  L.filter fun i => row i = true

/-- Bitmap-only implementation. `rate` is indexed by the integer hit count.
There is no universe, sample value, or universe enumeration in this procedure. -/
def matrixTree (rate : ℕ → Rate) :
    {n : ℕ} → (Fin n → I → Bool) → ℕ → Finset I → Tree n
  | 0, _, _, _ => .leaf
  | n + 1, B, t, L =>
      if t = 0 then rejectAll (n + 1)
      else
        let hit := matrixHits L (B 0)
        .node (rate hit.card)
          (matrixTree rate (fun j => B j.succ) t L)
          (matrixTree rate (fun j => B j.succ) (t - 1) (L \ hit))

def matrixWork :
    {n : ℕ} → (Fin n → I → Bool) → ℕ → Finset I → (Fin n → Bool) → ℕ
  | 0, _, _, _, _ => 0
  | _ + 1, B, t, L, T =>
      if t = 0 then 0
      else L.card + matrixWork (fun j => B j.succ) (if T 0 then t - 1 else t)
        (if T 0 then L \ matrixHits L (B 0) else L) (fun j => T j.succ)

variable [Fintype I] {U : Type*}

theorem matrixWork_le {n : ℕ} (B : Fin n → I → Bool)
    (t : ℕ) (L : Finset I) (T : Fin n → Bool) :
    matrixWork B t L T ≤ n * Fintype.card I := by
  induction n generalizing t L with
  | zero => simp [matrixWork]
  | succ n ih =>
      by_cases ht : t = 0
      · simp [matrixWork, ht]
      · simp only [matrixWork, ht, ↓reduceIte]
        have hh := ih (fun j => B j.succ) (if T 0 then t - 1 else t)
          (if T 0 then L \ matrixHits L (B 0) else L) (fun j => T j.succ)
        have hc := Finset.card_le_univ L
        nlinarith

omit [DecidableEq I] [Fintype I] in
private theorem hits_eq_matrixHits (X : I → Option U) (L : Finset I) (A : Finset U) :
    hits X L A = matrixHits L (fun i => decide (contains A (X i))) := by
  ext i
  simp [hits, matrixHits]

omit [Fintype I] in
theorem liveTree_eq_matrixTree (b H : ℝ) (X : I → Option U) {n : ℕ}
    (R : Fin n → Finset U) (t : ℕ) (L : Finset I) :
    liveTree b H X R t L =
      matrixTree (fun c => logistic b H c)
        (fun j i => decide (contains (R j) (X i))) t L := by
  induction n generalizing t L with
  | zero => rfl
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [liveTree, matrixTree, ht, ↓reduceIte]
      · simp only [liveTree, matrixTree, ht, ↓reduceIte]
        rw [hits_eq_matrixHits]
        rw [ih (fun j => R j.succ) t L]
        rw [ih (fun j => R j.succ) (t - 1)
          (L \ matrixHits L (fun i => decide (contains (R 0) (X i))))]

omit [Fintype I] in
theorem liveWork_eq_matrixWork (X : I → Option U) {n : ℕ}
    (R : Fin n → Finset U) (t : ℕ) (L : Finset I) (T : Fin n → Bool) :
    liveWork X R t L T =
      matrixWork (fun j i => decide (contains (R j) (X i))) t L T := by
  induction n generalizing t L with
  | zero => rfl
  | succ n ih =>
      by_cases ht : t = 0
      · simp only [liveWork, matrixWork, ht, ↓reduceIte]
      · simp only [liveWork, matrixWork, ht, ↓reduceIte]
        rw [hits_eq_matrixHits]
        exact congrArg (L.card + ·) (ih (fun j => R j.succ)
          (if T 0 then t - 1 else t)
          (if T 0 then L \ matrixHits L (fun i => decide (contains (R 0) (X i))) else L)
          (fun j => T j.succ))

end Matrix

noncomputable def membershipMatrix {U : Type*} {Ns n : ℕ}
    (R : Fin n → Finset U) (X : Fin Ns → U) : Fin n → Fin Ns → Bool :=
  fun j i => decide (X i ∈ R j)

noncomputable def matrixMechanism {Ns n : ℕ} (rate : ℕ → Rate)
    (B : Fin n → Fin Ns → Bool) (t : ℕ) : Law (Fin n → Bool) :=
  (matrixTree rate B t Finset.univ).law

theorem mechanism_eq_matrix {U : Type*} (b : ℝ) (Ns t : ℕ) {n : ℕ}
    (R : Fin n → Finset U) (X : Fin Ns → U) :
    mechanism b Ns t R X =
      matrixMechanism (fun c => logistic b (2 * Ns / t) c) (membershipMatrix R X) t := by
  rw [mechanism, liveTree_eq_matrixTree]
  have he : (fun j i => decide (contains (R j) (some (X i)))) = membershipMatrix R X := by
    funext j i
    simp only [contains_some, membershipMatrix]
  rw [he]
  rfl

theorem queryWork_eq_matrixWork {U : Type*} {Ns n : ℕ}
    (R : Fin n → Finset U) (t : ℕ) (X : Fin Ns → U) (T : Fin n → Bool) :
    queryWork R t X T = matrixWork (membershipMatrix R X) t Finset.univ T := by
  rw [queryWork, liveWork_eq_matrixWork]
  have he : (fun j i => decide (contains (R j) (some (X i)))) = membershipMatrix R X := by
    funext j i
    simp only [contains_some, membershipMatrix]
  rw [he]

/-- Extensionality also permits different record types and different universes.
Only the Boolean membership matrix is relevant. -/
theorem mechanism_ext {U V : Type*} (b : ℝ) (Ns t : ℕ) {n : ℕ}
    (R : Fin n → Finset U) (S : Fin n → Finset V)
    (X : Fin Ns → U) (Y : Fin Ns → V)
    (h : ∀ j i, X i ∈ R j ↔ Y i ∈ S j) :
    mechanism b Ns t R X = mechanism b Ns t S Y := by
  have hB : membershipMatrix R X = membershipMatrix S Y := by
    funext j i
    simp only [membershipMatrix, h j i]
  rw [mechanism_eq_matrix, mechanism_eq_matrix, hB]

theorem queryWork_ext {U V : Type*} {Ns n : ℕ}
    (R : Fin n → Finset U) (S : Fin n → Finset V) (t : ℕ)
    (X : Fin Ns → U) (Y : Fin Ns → V) (T : Fin n → Bool)
    (h : ∀ j i, X i ∈ R j ↔ Y i ∈ S j) :
    queryWork R t X T = queryWork S t Y T := by
  have hB : membershipMatrix R X = membershipMatrix S Y := by
    funext j i
    simp only [membershipMatrix, h j i]
  rw [queryWork_eq_matrixWork, queryWork_eq_matrixWork, hB]

noncomputable def rationalMatrixMechanism (Lbar Ns t : ℕ) {n : ℕ}
    (B : Fin n → Fin Ns → Bool) : Law (Fin n → Bool) :=
  matrixMechanism (rationalRate Lbar Ns t) B t

theorem matrixTransition_work_le (Lbar Ns t : ℕ) (L : Finset (Fin Ns))
    (row : Fin Ns → Bool) :
    fastProbabilityWork Lbar Ns t (matrixHits L row).card ≤
      6 * (Nat.log2 (Ns + 1) + 2) + 16 := by
  apply fastProbabilityWork_le
  simpa only [Fintype.card_fin] using Finset.card_le_univ (matrixHits L row)

theorem mechanism_eq_rationalMatrix {U : Type*} (Lbar Ns t : ℕ)
    (hL : 0 < Lbar) (ht : 0 < t) (hdiv : t ∣ Ns) {n : ℕ}
    (R : Fin n → Finset U) (X : Fin Ns → U) :
    mechanism (calibratedBandwidth Lbar) Ns t R X =
      rationalMatrixMechanism Lbar Ns t (membershipMatrix R X) := by
  rw [mechanism_eq_matrix]
  have he : (fun c : ℕ => logistic (calibratedBandwidth Lbar) (2 * Ns / t) c) =
      rationalRate Lbar Ns t :=
    funext fun c => logistic_eq_rationalRate Lbar Ns t c hL ht hdiv
  rw [he]
  rfl

section Uniform

variable {U : Type*} [Fintype U] [Nonempty U]

attribute [local instance] dataFintype transcriptFintype

/-- Uniform samples followed by the rational, bitmap-only procedure.
Its definition does not use a logarithm or an exponential. -/
noncomputable def rationalRun (Lbar Ns t : ℕ) {n : ℕ} (R : Fin n → Finset U) :
    Law (Fin n → Bool) :=
  ((Law.uniform U).iid (Fin Ns)).bind fun X =>
    rationalMatrixMechanism Lbar Ns t (membershipMatrix R X)

theorem rationalRun_eq_run (Lbar Ns t : ℕ) (hL : 0 < Lbar) (ht : 0 < t)
    (hdiv : t ∣ Ns) {n : ℕ} (R : Fin n → Finset U) :
    rationalRun Lbar Ns t R = run (calibratedBandwidth Lbar) Ns t R := by
  unfold rationalRun run
  congr 1
  funext X
  exact (mechanism_eq_rationalMatrix Lbar Ns t hL ht hdiv R X).symm

theorem integer_reusable_sample_rational {n : ℕ} (R : Fin n → Finset U)
    (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (Lbar Mbar : ℕ)
    (hL : logBudget t β ≤ Lbar) (hM : rowBudget n t β ≤ Mbar) :
    1 - β ≤ (rationalRun Lbar (integerSamples t Lbar Mbar) t R).prob
      {T | Specification R t T} ∧
    (∀ T, 0 < (rationalRun Lbar (integerSamples t Lbar Mbar) t R).mass T →
      acceptances T ≤ t) ∧
    (∀ (X : Fin (integerSamples t Lbar Mbar) → U) (T : Fin n → Bool),
      queryWork R t X T ≤ n * integerSamples t Lbar Mbar) := by
  have hL₀ : 0 < Lbar := by
    have hh := (logBudget_ge_one t ht β hβ hβ').trans hL
    exact_mod_cast (show (0 : ℝ) < Lbar by linarith)
  rw [rationalRun_eq_run Lbar _ t hL₀ ht (integerSamples_dvd t Lbar Mbar)]
  exact integer_reusable_sample R t ht β hβ hβ' Lbar Mbar hL hM

theorem integer_reusable_sample_rational_of_doubling {n : ℕ} (R : Fin n → Finset U)
    (t : ℕ) (ht : 0 < t) (β : ℝ) (hβ : 0 < β) (hβ' : β < 1 / 4) (k ℓ : ℕ)
    (hk : 512 * (t : ℝ) ≤ β * (2 : ℝ) ^ k)
    (hℓ : 128 * ((n : ℝ) + 1) * t ≤ β * (2 : ℝ) ^ ℓ) :
    1 - β ≤ (rationalRun (k + 1) (integerSamples t (k + 1) (ℓ + 1)) t R).prob
      {T | Specification R t T} ∧
    (∀ T, 0 < (rationalRun (k + 1) (integerSamples t (k + 1) (ℓ + 1)) t R).mass T →
      acceptances T ≤ t) ∧
    (∀ (X : Fin (integerSamples t (k + 1) (ℓ + 1)) → U) (T : Fin n → Bool),
      queryWork R t X T ≤ n * integerSamples t (k + 1) (ℓ + 1)) :=
  integer_reusable_sample_rational R t ht β hβ hβ' (k + 1) (ℓ + 1)
    (logBudget_le_of_doubling t ht β hβ k hk) (rowBudget_le_of_doubling n t ht β hβ ℓ hℓ)

end Uniform

end SteinerUpperBound.ReusableSample

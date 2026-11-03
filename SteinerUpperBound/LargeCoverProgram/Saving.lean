module

public import SteinerUpperBound.LargeCoverProgram.PointKernel
public import SteinerUpperBound.LargeCoverProgram.PoolLaw
public import SteinerUpperBound.SavingScores.GeneralParameters

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

variable {Q P D : Type} [Fintype P] [Fintype D] {n k B : ℕ}

abbrev RetainedIndex (bits : Q → Bool) (cfg : LocalAccess.SlotConfig Q n (k + 1)) :=
  ↥(Covers.Rejection.retained (fun u => bits (cfg.key (cfg.terminals.get u))))

theorem profile_score_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (part : RetainedIndex bits cfg → P) (hsurj : Function.Surjective part)
    (covered U : Finset P) (G : Matching.Graph P D)
    (matched : Finset (Fin n) → Matching.Rank D → Bool)
    (hsize : ∀ x, (componentAt I bits cfg x.val).card = SavingScores.partSize part (part x))
    (hcovered : ∀ x, part x ∈ covered ↔
      (componentAt I bits cfg x.val).card ≤ B ∧ coveredComponent cfg (componentAt I bits cfg x.val) = true)
    (hU : ∀ x, part x ∈ U ↔
      (componentAt I bits cfg x.val).card ≤ B ∧ coveredComponent cfg (componentAt I bits cfg x.val) = false)
    (hmatched : ∀ x rank, matched (componentAt I bits cfg x.val) rank =
      (G.vertexOracle rank (part x)).value.isSome)
    (x : RetainedIndex bits cfg) (rank : Matching.Rank D) (coin : Bool) :
    pointScore I bits cfg B matched x.val (rank, coin) =
      SavingScores.pointScore part covered U G (x, (rank, coin)) := by
  have hr : bits (cfg.key (cfg.terminals.get x.val)) = true := by
    simpa [Covers.Rejection.retained, CategoricalCoupling.selected] using x.property
  by_cases hs : (componentAt I bits cfg x.val).card ≤ B
  · cases hh : coveredComponent cfg (componentAt I bits cfg x.val)
    · have hnot : part x ∉ covered := by simp [hcovered, hh]
      have hu : part x ∈ U := (hU x).mpr ⟨hs, hh⟩
      simp [pointScore, hr, hs, hh, SavingScores.pointScore, hnot, hu,
        SavingScores.matchedValue, hmatched]
    · have hc : part x ∈ covered := (hcovered x).mpr ⟨hs, hh⟩
      have hs' : SavingScores.partSize part (part x) ≤ B := by rw [← hsize]; exact hs
      simp [pointScore, hr, hs, hs', hh, SavingScores.pointScore, hc, hsize]
  · have hc : part x ∉ covered := fun hx => hs ((hcovered x).mp hx).1
    have hu : part x ∉ U := fun hx => hs ((hU x).mp hx).1
    simp [pointScore, hr, hs, SavingScores.pointScore, hc, hu]

/-- The mean is derived from the genuine component partition and the SAME
physical-copy graph/rank law. No point-mean or saving certificate is assumed. -/
theorem pointMean_eq_scoreMeanFor (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1))
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    [Nonempty (RetainedIndex bits cfg)]
    (part : RetainedIndex bits cfg → P) (hsurj : Function.Surjective part)
    (covered U : Finset P) (G : Matching.Graph P D) (mu : Law (Matching.Rank D))
    (matched : Finset (Fin n) → Matching.Rank D → Bool)
    (hsize : ∀ x, (componentAt I bits cfg x.val).card = SavingScores.partSize part (part x))
    (hcovered : ∀ x, part x ∈ covered ↔
      (componentAt I bits cfg x.val).card ≤ B ∧ coveredComponent cfg (componentAt I bits cfg x.val) = true)
    (hU : ∀ x, part x ∈ U ↔
      (componentAt I bits cfg x.val).card ≤ B ∧ coveredComponent cfg (componentAt I bits cfg x.val) = false)
    (hmatched : ∀ x rank, matched (componentAt I bits cfg x.val) rank =
      (G.vertexOracle rank (part x)).value.isSome) :
    (Mean.pointKernel
      (Covers.Rejection.uniformRetained (fun u => bits (cfg.key (cfg.terminals.get u))) hb)
      (pointKernel I bits cfg mu)).expect (fun z => pointScore I bits cfg B matched z.1 z.2) =
        SavingScores.scoreMeanFor mu part hsurj covered U G := by
  rw [Mean.pointKernel_expect]
  rw [← uniformRetained_map (fun u => bits (cfg.key (cfg.terminals.get u))) hb, Law.expect_map]
  unfold SavingScores.scoreMeanFor SavingScores.sampleLawFor
  simp only [pointKernel, Law.expect_bind, Law.expect_map]
  apply congrArg (Law.uniform (RetainedIndex bits cfg)).expect
  funext x
  have hpos : 0 < (componentAt I bits cfg x.val).card := by
    rw [hsize]
    exact SavingScores.partSize_pos part hsurj _
  have hrate : inverseRate (componentAt I bits cfg x.val).card =
      SavingScores.initiationRate part hsurj (part x) := by
    apply Subtype.ext
    rw [inverseRate_value _ hpos, hsize]
    rfl
  rw [hrate]
  apply congrArg mu.expect
  funext rank
  apply congrArg (CategoricalCoupling.bernoulli (SavingScores.initiationRate part hsurj (part x))).expect
  funext coin
  exact profile_score_eq I bits cfg part hsurj covered U G matched hsize hcovered hU hmatched x rank coin

theorem afterMean_value {Q : Type*} {n k : ℕ} (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (gminus gplus : ℚ) (selected : Selection (Fin n)) (Dflag : Vector Bool n)
    (r : Mean.Result Q k p.meanSamples) (F : Option ℝ → ℝ) :
    (afterMean p gminus gplus selected Dflag r).evaluate w bits (fun o => F o.value.value) =
      F (r.value.map (fun empirical => SavingScores.Z gminus empirical (p.xi : ℝ) selected.count)) := rfl

/-- Deterministic contract of the actual final scalar computation, using
maximal-greedy matching bounds for any global strict-order law. -/
theorem large_score_contract {X R : Type*} [Fintype X] [Nonempty X]
    (mu : Law (Matching.Rank D)) (part : X → P) (hsurj : Function.Surjective part)
    (order : List R) (horder : order.Nodup) (hrows : 0 < order.toFinset.card)
    (E : Finset R) (rows : R → Finset P) (hE : E ⊆ order.toFinset)
    (large covered U : Finset P) (S : Finset R) (s t : ℕ)
    (hparts : (Finset.univ : Finset P) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ order.toFinset) (hs : S.card ≤ s) (hst : s ≤ t)
    (hineligible : ∀ r ∈ order.toFinset, r ∉ E → (rows r).card ≤ 2)
    (eps gminus empirical xi : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlarge : ∀ a ∈ large, SavingScores.smallThreshold eps < SavingScores.partSize part a)
    (hbranch : 50 * (t : ℝ) / eps < Nat.card X)
    (hxi0 : 0 ≤ xi) (hxi : xi ≤ eps / 100) (G : Matching.Graph P D)
    (hreal : SetSystem.Realizes G (SetSystem.mutualGraph U E
      (SetSystem.firstIncident order rows (SavingScores.incidenceBudget order.toFinset.card eps gminus))))
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal1 : gminus ≤ Nat.card X)
    (he : |empirical - SavingScores.scoreMeanFor mu part hsurj covered U G| ≤ xi) :
    0 ≤ SavingScores.Z gminus empirical xi s ∧
      SavingScores.Z gminus empirical xi s ≤ SavingScores.fullSaving E rows ∧
      SavingScores.fullSaving E rows / 2 - eps * Nat.card X ≤
        SavingScores.Z gminus empirical xi s :=
  SavingScores.ordered_large_branch_contractFor mu part hsurj order horder hrows E rows hE
    large covered U S s t hparts hdisj hcover hS hs hst hineligible eps gminus empirical xi
    heps heps1 hlarge hbranch hxi0 hxi G hreal hcal hcal1 he

end SteinerUpperBound.LargeCoverProgram

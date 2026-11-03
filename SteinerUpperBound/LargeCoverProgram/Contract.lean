module

public import SteinerUpperBound.LargeCoverProgram.Partition
public import SteinerUpperBound.LargeCoverProgram.Statistics
public import SteinerUpperBound.PortGraph

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram Covers.OracleProgram
open scoped Classical BigOperators

def GoodSaving (Phi g eps : ℝ) (value : Option ℝ) : Prop :=
  ∃ Z, value = some Z ∧ 0 ≤ Z ∧ Z ≤ Phi ∧ Phi / 2 - eps * g ≤ Z

theorem afterCovered_fields {Q : Type*} {n k : ℕ}
    (w : Sym2 (Fin n) → ℝ) (bits : Q → Bool)
    (p : Parameters) (terminals : Vector (Fin n) (k + 1)) (root : Fin (k + 1))
    (key : Fin n → Q) (a : ℝ) (vo : VOBuilder Q n p.cutoff)
    (gminus gplus : ℚ) (selected : Selection (Fin n)) (c : Cache Q) (D : Vector Bool n) :
    ∀ o, Runs w bits (afterCovered p terminals root key a vo gminus gplus selected c D) o →
      o.value.value = o.value.empirical.map
        (fun empirical => SavingScores.Z gminus empirical (p.xi : ℝ) selected.count) ∧
      o.value.selected = selected ∧ o.value.covered = some D := by
  intro o ho
  cases ho with
  | tick ho =>
      obtain ⟨mean, last, hm, hl, rfl⟩ := Mean.runs_bind_inv w bits _ _ _ ho
      cases hl with
      | tick hl => cases hl; exact ⟨rfl, rfl, rfl⟩

/-- Quantitative capping contract at any genuine incidence budget satisfying
the public numerical loss test. Rank laws may be arbitrary, and physical
parallel copies are unchanged. -/
theorem capped_large_contract {X A R D : Type*} [Fintype X] [Nonempty X]
    [Fintype A] [Fintype D]
    (mu : Law (Matching.Rank D)) (part : X → A) (hsurj : Function.Surjective part)
    (allRows E : Finset R) (rows : R → Finset A) (hE : E ⊆ allRows)
    (large covered U : Finset A) (S : Finset R) (s t b : ℕ)
    (hparts : (Finset.univ : Finset A) ⊆ large ∪ covered ∪ U)
    (hdisj : Disjoint covered U) (hcover : covered ⊆ S.biUnion rows)
    (hS : S ⊆ allRows) (hs : S.card ≤ s) (hst : s ≤ t)
    (hineligible : ∀ r ∈ allRows, r ∉ E → (rows r).card ≤ 2)
    (eps gminus empirical xi : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hlarge : ∀ a ∈ large, SavingScores.smallThreshold eps < SavingScores.partSize part a)
    (hbranch : 50 * (t : ℝ) / eps < Nat.card X)
    (hxi0 : 0 ≤ xi) (hxi : xi ≤ eps / 100) (hb : 1 ≤ b)
    (hloss : (allRows.card : ℝ) / b ≤ eps * gminus / 100)
    (cap : SetSystem.IncidenceCap allRows rows U b)
    (G : Matching.Graph A D) (hreal : SetSystem.Realizes G (SetSystem.mutualGraph U E cap.lists))
    (hcal : (1 - xi) * (Nat.card X : ℝ) ≤ gminus) (hcal1 : gminus ≤ Nat.card X)
    (he : |empirical - SavingScores.scoreMeanFor mu part hsurj covered U G| ≤ xi) :
    0 ≤ SavingScores.Z gminus empirical xi s ∧
      SavingScores.Z gminus empirical xi s ≤ SavingScores.fullSaving E rows ∧
      SavingScores.fullSaving E rows / 2 - eps * Nat.card X ≤
        SavingScores.Z gminus empirical xi s := by
  have hg : (0 : ℝ) < Nat.card X := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_pos
  have hc := SavingScores.capped_Z_contractFor mu part hsurj allRows E rows hE large covered U S s
    hparts hdisj hcover hS hs hineligible b hb cap G hreal gminus empirical xi hxi0
    (by linarith) hcal hcal1 he
  have hl := SavingScores.large_count_loss part large eps heps hlarge
  have hbudget : (allRows.card : ℝ) / b ≤ eps * Nat.card X / 100 := by
    have hh := mul_le_mul_of_nonneg_left hcal1 heps.le
    linarith
  have hs' : (s : ℝ) ≤ t := by exact_mod_cast hst
  have hbranch' := (div_lt_iff₀ heps).mp hbranch
  have hselected : 2 * (s : ℝ) ≤ eps * Nat.card X / 25 := by nlinarith
  have hsampling : 3 * xi * Nat.card X ≤ 3 * eps * Nat.card X / 100 := by
    nlinarith [mul_le_mul_of_nonneg_right hxi hg.le]
  exact ⟨hc.1, hc.2.1, by linarith [hc.2.2]⟩

variable {Q : Type} {n k : ℕ}

noncomputable def copyDecidableEq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (b B : ℕ) :
    DecidableEq (PortGraph.Copy I bits cfg b B) := Classical.decEq _

attribute [local instance] copyDecidableEq

theorem rowCapacity_pos (n : ℕ) (p : Parameters) (gminus : ℚ) :
    1 ≤ rowCapacity n p gminus := by
  unfold rowCapacity
  apply le_min
  · exact (show 1 ≤ (2 : ℕ) by decide).trans (Nat.le_add_left _ _)
  · exact le_max_left _ _

theorem actualPointMean_eq (I : Instance (Fin n)) (bits : Q → Bool)
    (cfg : LocalAccess.SlotConfig Q n (k + 1)) (B : ℕ)
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    [Nonempty (RetainedIndex bits cfg)]
    {D : Type} [Fintype D] (G : Matching.Graph (Part I bits cfg) D) (mu : Law (Matching.Rank D)) :
    expectedPoint I bits cfg B mu (matchedPart I bits cfg G) hb =
      SavingScores.scoreMeanFor mu (partition I bits cfg hT) (partition_surjective I bits cfg hT)
        (coveredClasses I bits cfg B) (PortGraph.residualParts I bits cfg B) G := by
  apply pointMean_eq_scoreMeanFor I bits cfg hb (partition I bits cfg hT)
    (partition_surjective I bits cfg hT) (coveredClasses I bits cfg B)
    (PortGraph.residualParts I bits cfg B) G mu (matchedPart I bits cfg G)
  · intro x
    exact (partition_size I bits cfg hT hnd (partition I bits cfg hT x)).symm
  · intro x
    simp [coveredClasses, partition]
  · intro x
    simp only [PortGraph.residualParts, PortGraph.smallParts, Finset.mem_filter,
      Finset.mem_univ, true_and, (partition I bits cfg hT x).property]
    change ((componentAt I bits cfg x.val).card ≤ B ∧
      Disjoint (componentAt I bits cfg x.val) (PortGraph.removed I cfg)) ↔ _
    exact and_congr_right (fun _ => (coveredComponent_false I bits cfg hT (partition I bits cfg hT x)).symm)
  · exact matchedPart_partition I bits cfg hT G

/-- Saving confidence for the actual large-point/mean/final-Z code. The only
probabilistic refinement premise is a one-call Boolean VO law (with explicit
TV error); all score means and matching approximation bounds are derived.
`hloss` is a numerical test on observed/public data, not a saving certificate. -/
theorem afterCovered_saving_confidence (I : Instance (Fin n)) (bits : Q → Bool)
    (p : Parameters) (cfg : LocalAccess.SlotConfig Q n (k + 1)) (root : Fin (k + 1))
    (hT : cfg.terminals.toList.toFinset = I.terminals) (hnd : cfg.terminals.toList.Nodup)
    (vo : VOBuilder Q n p.cutoff) (gminus gplus : ℚ)
    (selected : Selection (Fin n)) (c : Cache Q) (hc : Cache.Correct bits c)
    (hb : (Covers.Rejection.retained fun u => bits (cfg.key (cfg.terminals.get u))).Nonempty)
    (hlen : selected.centers.length = selected.count) (hcount : selected.count ≤ p.t)
    (hD : cfg.covered = (LocalAccess.coveredResult I.weight (PortGraph.radius cfg) selected.centers).value)
    (heps : 0 < (p.eps : ℝ)) (heps1 : (p.eps : ℝ) ≤ 1) (hxi : 0 < (p.xi : ℝ))
    (hxi' : (p.xi : ℝ) ≤ (p.eps : ℝ) / 100)
    (hB : SavingScores.smallThreshold (p.eps : ℝ) ≤ p.cutoff)
    (hbranch : 50 * (p.t : ℝ) / (p.eps : ℝ) < Nat.card (RetainedIndex bits cfg))
    (hcal : (1 - (p.xi : ℝ)) * Nat.card (RetainedIndex bits cfg) ≤ (gminus : ℝ))
    (hcal1 : (gminus : ℝ) ≤ Nat.card (RetainedIndex bits cfg))
    (hloss : (n : ℝ) / rowCapacity n p gminus ≤ (p.eps : ℝ) * gminus / 100)
    (mu : Law (Matching.Rank (PortGraph.Copy I bits cfg (rowCapacity n p gminus) p.cutoff)))
    (delta beta : ℝ) (hd : 0 ≤ delta)
    (hvo : VOApproxRefinement I bits cfg (rowCapacity n p gminus) p.cutoff
      (vo cfg.covered (rowCapacity n p gminus)) mu
      (matchedPart I bits cfg (PortGraph.liftedGraph I bits cfg (rowCapacity n p gminus) p.cutoff)) delta)
    (hs : 0 < p.meanSamples)
    (hbudget : 1 ≤ beta * ((p.meanSamples : ℝ) * (p.xi : ℝ) ^ 2)) :
    (afterCovered p cfg.terminals root cfg.key cfg.scale vo gminus gplus selected c cfg.covered).probability
      I.weight bits {o | ¬ GoodSaving
        (Covers.Geometry.savingOn I (PortGraph.retained I bits cfg) cfg.scale (PortGraph.radius cfg))
        (Nat.card (RetainedIndex bits cfg)) (p.eps : ℝ) o.value.value} ≤
      Mean.capError (fun u => bits (cfg.key (cfg.terminals.get u)))
        p.meanRowCap p.meanSamples p.meanProposals + p.meanSamples * delta + beta := by
  letI : Nonempty (RetainedIndex bits cfg) := ⟨⟨hb.choose, hb.choose_spec⟩⟩
  let part := partition I bits cfg hT
  let G := PortGraph.liftedGraph I bits cfg (rowCapacity n p gminus) p.cutoff
  let matched := matchedPart I bits cfg G
  let Phi := Covers.Geometry.savingOn I (PortGraph.retained I bits cfg) cfg.scale (PortGraph.radius cfg)
  let m0 := expectedPoint I bits cfg p.cutoff mu matched hb
  have hmean := actualPointMean_eq I bits cfg p.cutoff hT hnd hb G mu
  have hparts := classes_partition I bits cfg p.cutoff
  have hres : residualClasses I bits cfg p.cutoff = PortGraph.residualParts I bits cfg p.cutoff :=
    residualClasses_eq I bits cfg hT p.cutoff
  have hsave (empirical : ℝ) (he : |empirical - m0| ≤ (p.xi : ℝ)) :
      GoodSaving Phi (Nat.card (RetainedIndex bits cfg)) (p.eps : ℝ)
        (some (SavingScores.Z gminus empirical (p.xi : ℝ) selected.count)) := by
    have hlarge : ∀ C ∈ largeClasses I bits cfg p.cutoff,
        SavingScores.smallThreshold (p.eps : ℝ) < SavingScores.partSize part C := by
      intro C hC
      rw [partition_size I bits cfg hT hnd C]
      exact hB.trans_lt (Finset.mem_filter.mp hC).2
    have hgeom := capped_large_contract mu part (partition_surjective I bits cfg hT)
      (Finset.univ : Finset (Fin n)) (PortGraph.eligible I bits cfg) (partRows I bits cfg)
      (Finset.subset_univ _) (largeClasses I bits cfg p.cutoff)
      (coveredClasses I bits cfg p.cutoff) (PortGraph.residualParts I bits cfg p.cutoff)
      selected.centers.toFinset selected.count p.t (rowCapacity n p gminus)
      (by
        intro C hC
        rw [← hres]
        simpa only [Finset.mem_union] using hparts.1 hC)
      (by rw [← hres]; exact hparts.2)
      (by
        intro C hC
        have hh := coveredClasses_cover I bits cfg hT p.cutoff selected hD hC
        simpa only [Finset.mem_biUnion] using hh)
      (Finset.subset_univ _) ((List.toFinset_card_le _).trans hlen.le) hcount
      (fun v _ hv => partRows_ineligible I bits cfg v hv)
      (p.eps : ℝ) (gminus : ℝ) empirical (p.xi : ℝ) heps heps1 hlarge hbranch
      hxi.le hxi' (rowCapacity_pos n p gminus)
      (by simpa only [Finset.card_univ, Fintype.card_fin] using hloss)
      (PortGraph.incidenceCap I bits cfg (rowCapacity n p gminus) p.cutoff)
      G (PortGraph.lifted_realizes I bits cfg (rowCapacity n p gminus) p.cutoff hT)
      hcal hcal1 (by rwa [← hmean])
    refine ⟨_, rfl, hgeom.1, ?_, ?_⟩
    · simpa only [partSaving_eq] using hgeom.2.1
    · simpa only [partSaving_eq] using hgeom.2.2
  have hm := afterCovered_confidence I bits p cfg root hT hnd vo gminus gplus selected c hc hb
    mu matched delta beta hd hvo hs hxi hbudget
  apply LE.le.trans ?_ hm
  unfold Code.probability
  apply Mean.evaluate_mono_runs
  intro o ho
  have hfields := (afterCovered_fields I.weight bits p cfg.terminals root cfg.key cfg.scale
    vo gminus gplus selected c cfg.covered o ho).1
  by_cases hb0 : Mean.BadMean m0 (p.xi : ℝ) o.value.empirical
  · have hb1 : o ∈ {o : Outcome (Answer Q n) |
        Mean.BadMean (expectedPoint I bits cfg p.cutoff mu matched hb) (p.xi : ℝ) o.value.empirical} := hb0
    simp only [hb1, ite_true]
    split_ifs <;> norm_num
  · have hg : GoodSaving Phi (Nat.card (RetainedIndex bits cfg)) (p.eps : ℝ) o.value.value := by
      cases hv : o.value.empirical with
      | none => exact (hb0 (by simp [Mean.BadMean, hv])).elim
      | some empirical =>
          rw [hfields, hv, Option.map_some]
          exact hsave empirical (le_of_not_gt (by simpa [Mean.BadMean, hv] using hb0))
    have hf : ¬ o ∈ {o : Outcome (Answer Q n) |
        ¬ GoodSaving Phi (Nat.card (RetainedIndex bits cfg)) (p.eps : ℝ) o.value.value} :=
      not_not_intro hg
    dsimp only [Phi] at hf
    have hb1 : ¬ o ∈ {o : Outcome (Answer Q n) |
        Mean.BadMean (expectedPoint I bits cfg p.cutoff mu matched hb) (p.xi : ℝ) o.value.empirical} := hb0
    simp only [hf, hb1, ite_false, le_refl]

end SteinerUpperBound.LargeCoverProgram

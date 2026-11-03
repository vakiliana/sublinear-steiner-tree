module

public import SteinerUpperBound.EstimatorFrontend
public import SteinerUpperBound.EstimatorClocks.Resources
public import SteinerUpperBound.LargeCoverProgram.Support

/-!
# Event-free resources of the actual frontend

`SavingResources` asks only for the guarded saving CODE's expected work/positive
accounts and `Causal.Ensures` that a returned `some (z,cache)` has a correct cache.
`none` is allowed. No cover, size, phase, calibration, or accuracy event occurs.

Writing `H=heightBudget n`, the executable public budgets are
`fineWork + H*(Wsave+9) + bandWork + (2*H+7)*H + 13` and
`finePositive + H*Psave + bandPositive`. The saving-loop bound charges its actual
failure branches and proves the correct cache and exact log length on successful
support. Fine cache preservation holds on all positive support, even when its
scalar estimate is inaccurate; the actual BandEstimator resource facade is
event-free. Final repeated-multiply totals and scalar output are charged.

`program_expected` requires injective public labels, both height bounds, truthful
incoming cache, and true retained-root bits at used fine levels. List nodup and
enumeration follow from the vector. Inverse-left and coarse-root truths are not
additionally needed by these resource facades. `program_averaged_resources`
requires these cache/root/saving properties only on positive world support.

`clocked_budgets_polylog` and the fixed-world and mixed-world clocked theorems use
`stage.workBudget+setup`, `stage.disclosureBudget+1`; their common degree is
`max(d+2,126)` with explicit absolute factors. Actual clocked saving setup plus
flattening costs `9+16=25`, supported by the generic `setup` parameter.
-/

@[expose] public section

namespace SteinerUpperBound.EstimatorFrontend.Resources

open SteinerLowerBound QueryProgram EstimatorParameters RuntimeGrids Matching.Padded
open scoped Classical BigOperators

def fineWork (n : ℕ) : ℕ := EstimatorMST.workFactor * (n + 1) * ell n ^ 36
def finePositive (n : ℕ) : ℕ := EstimatorMST.positiveFactor * ell n ^ 27

def workBudget (n savingWork : ℕ) : ℕ :=
  fineWork n + heightBudget n * (savingWork + 9) + BandEstimator.workPolynomial n +
    (2 * heightBudget n + 7) * heightBudget n + 13

def positiveBudget (n savingPositive : ℕ) : ℕ :=
  finePositive n + heightBudget n * savingPositive + BandEstimator.positivePolynomial n

def CacheSafe {Q : Type*} (bits : Q → Bool) (r : Option (ℝ × Cache Q)) : Prop :=
  ∀ zc, r = some zc → Cache.Correct bits zc.2

variable {n k : ℕ}

noncomputable local instance resourcesVertexDecEq : DecidableEq (Fin n) := Classical.decEq _
noncomputable local instance resourcesLabelDecEq : DecidableEq (Fin (k + 1)) := Classical.decEq _

/-- Event-free contracts for the guarded saving CODE, including failed runs.
Only a returned `some` is required to carry a correct outgoing cache. -/
structure SavingResources {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (saving : Saving n k t) (savingWork savingPositive : ℕ) : Prop where
  work : ∀ i c, Cache.Correct bits c →
    (saving i c).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤ savingWork
  positive : ∀ i c, Cache.Correct bits c →
    (saving i c).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ savingPositive
  cache : ∀ i c, Cache.Correct bits c →
    Causal.Ensures I.weight bits (saving i c) (CacheSafe bits)

private theorem ensures_of_support {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q Out) (P : Out → Prop)
    (h : ∀ seed, 0 < (p.compile m).law.mass seed → P ((((p.compile m).tree seed).output bits).value)) :
    Causal.Ensures m bits p P := by
  intro F hF
  unfold Causal.expect
  rw [← Code.compile_expect]
  change (p.compile m).law.expect
    (fun seed => F ((((p.compile m).tree seed).output bits).value)) = 0
  apply le_antisymm
  · exact ((p.compile m).law.expect_mono_support
      (fun seed hs => (hF _ (h seed hs)).le)).trans_eq (Law.expect_const _ 0)
  · have hh := (p.compile m).law.expect_mono_support
      (fun seed hs => (hF _ (h seed hs)).ge)
    simpa only [Law.expect_const] using hh

private theorem bind_resources {M Q Out Result : Type*} (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q Out) (next : Out → Code M Q Result) (P : Out → Prop)
    (hP : Causal.Ensures m bits p P) (W Z Wnext Znext : ℝ)
    (hw : p.evaluate m bits (fun o => (o.work : ℝ)) ≤ W)
    (hz : p.evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ Z)
    (hn : ∀ r, P r →
      (next r).evaluate m bits (fun o => (o.work : ℝ)) ≤ Wnext ∧
      (next r).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ Znext) :
    (p.bind next).evaluate m bits (fun o => (o.work : ℝ)) ≤ W + Wnext ∧
      (p.bind next).evaluate m bits (fun o => (o.positiveReplies : ℝ)) ≤ Z + Znext := by
  have hfW := LargeCoverProgram.Support.expect_mono m bits p P hP
    (fun r => (next r).evaluate m bits (fun o => (o.work : ℝ))) (fun _ => Wnext)
    (fun r hr => (hn r hr).1)
  have hfZ := LargeCoverProgram.Support.expect_mono m bits p P hP
    (fun r => (next r).evaluate m bits (fun o => (o.positiveReplies : ℝ))) (fun _ => Znext)
    (fun r hr => (hn r hr).2)
  simp only [Causal.expect, Code.evaluate_const] at hfW hfZ
  constructor
  · rw [Code.evaluate_work_bind, Code.evaluate_add]
    exact add_le_add hw hfW
  · rw [Code.evaluate_positive_bind, Code.evaluate_add]
    exact add_le_add hz hfZ

def RoundCacheSafe {Q : Type*} (bits : Q → Bool)
    (r : Option (ℝ × ℝ × Cache Q)) : Prop :=
  ∀ z v c, r = some (z, v, c) → Cache.Correct bits c

def StateSafe {Idx Q : Type*} (bits : Q → Bool) (length : ℕ)
    (r : Option (EstimatorLoop.State Idx Q)) : Prop :=
  ∀ s, r = some s → Cache.Correct bits s.cache ∧ s.records.length = length

theorem savingRound_cache {t : Tables} (I : Instance (Fin n))
    (bits : RuntimeWorld.Coordinate t k → Bool) (saving : Saving n k t) (W Z : ℕ)
    (hs : SavingResources I bits saving W Z) (i : Index t)
    (c : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits c) :
    Causal.Ensures I.weight bits (EstimatorFrontend.savingRound t saving i c) (RoundCacheSafe bits) := by
  rw [EstimatorFrontend.savingRound, Code.map]
  apply LargeCoverProgram.Support.ensures_bind I.weight bits _ _ (CacheSafe bits) _ (hs.cache i c hc)
  intro r hr
  apply LargeCoverProgram.Support.ensures_pure
  cases r with
  | none => intro z v c he; cases he
  | some zc =>
    intro z v c he
    have hcache := hr zc rfl
    have hEq : zc.2 = c :=
      congrArg (fun x : ℝ × ℝ × Cache (RuntimeWorld.Coordinate t k) => x.2.2) (Option.some.inj he)
    exact hEq ▸ hcache

theorem savingRound_expected {t : Tables} (I : Instance (Fin n))
    (bits : RuntimeWorld.Coordinate t k → Bool) (saving : Saving n k t) (W Z : ℕ)
    (hs : SavingResources I bits saving W Z) (i : Index t)
    (c : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits c) :
    (EstimatorFrontend.savingRound t saving i c).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤ W ∧
      (EstimatorFrontend.savingRound t saving i c).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤ Z := by
  simpa only [EstimatorFrontend.savingRound, Code.evaluate_map, Outcome.map] using
    And.intro (hs.work i c hc) (hs.positive i c hc)

theorem rounds_cache {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (saving : Saving n k t) (W Z : ℕ) (hs : SavingResources I bits saving W Z)
    (indices : List (Index t)) (s : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (hc : Cache.Correct bits s.cache) :
    Causal.Ensures I.weight bits (EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving) indices s)
      (StateSafe bits (s.records.length + indices.length)) := by
  induction indices generalizing s with
  | nil =>
    apply LargeCoverProgram.Support.ensures_tick
    apply LargeCoverProgram.Support.ensures_pure
    intro out hout
    have he := Option.some.inj hout
    subst out
    exact ⟨hc, by simp⟩
  | cons i l ih =>
    rw [EstimatorLoop.rounds]
    apply LargeCoverProgram.Support.ensures_bind I.weight bits _ _ (RoundCacheSafe bits) _
      (savingRound_cache I bits saving W Z hs i s.cache hc)
    intro r hr
    apply LargeCoverProgram.Support.ensures_tick
    cases r with
    | none =>
      apply LargeCoverProgram.Support.ensures_pure
      intro out hout
      cases hout
    | some zvc =>
      rcases zvc with ⟨z, v, c⟩
      have hc' := hr z v c rfl
      apply LargeCoverProgram.Support.ensures_mono I.weight bits _ _
        (StateSafe bits (s.records.length + (i :: l).length))
        (ih ⟨c, ⟨i, z, v⟩ :: s.records⟩ hc')
      intro r hr out hout
      have h := hr out hout
      refine ⟨h.1, ?_⟩
      have hh := h.2
      simp only [List.length_cons] at hh ⊢
      omega

theorem rounds_expected {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (saving : Saving n k t) (W Z : ℕ) (hs : SavingResources I bits saving W Z)
    (indices : List (Index t)) (s : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (hc : Cache.Correct bits s.cache) :
    (EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving) indices s).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤ ((W + 5) * indices.length + 1 : ℕ) ∧
      (EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving) indices s).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤ (Z * indices.length : ℕ) := by
  induction indices generalizing s with
  | nil =>
    norm_num [EstimatorLoop.rounds, Code.evaluate, Outcome.add, Outcome.pure]
  | cons i l ih =>
    let next : Option (ℝ × ℝ × Cache (RuntimeWorld.Coordinate t k)) →
        Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k)
          (Option (EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))) :=
      fun r => .tick 4 (match r with
        | none => .pure none
        | some (z, v, c) => EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving)
            l ⟨c, ⟨i, z, v⟩ :: s.records⟩)
    have hn (r : Option (ℝ × ℝ × Cache (RuntimeWorld.Coordinate t k))) (hr : RoundCacheSafe bits r) :
        (next r).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
            5 + ((W + 5) * l.length + 1 : ℕ) ∧
          (next r).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ (Z * l.length : ℕ) := by
      cases r with
      | none =>
        simp only [next, Code.evaluate, Outcome.add, Outcome.pure, Nat.add_zero, Nat.cast_zero]
        constructor
        · have hh : (0 : ℝ) ≤ ((W + 5) * l.length + 1 : ℕ) := Nat.cast_nonneg _
          norm_num only [Nat.cast_ofNat]
          linarith
        · exact Nat.cast_nonneg _
      | some zvc =>
        rcases zvc with ⟨z, v, c⟩
        have h := ih ⟨c, ⟨i, z, v⟩ :: s.records⟩ (hr z v c rfl)
        dsimp only [next]
        rw [MSTApproximation.evaluate_tick_work, MSTApproximation.evaluate_tick_positive]
        norm_num only [Nat.cast_ofNat]
        exact ⟨add_le_add le_rfl h.1, h.2⟩
    have hstep := savingRound_expected I bits saving W Z hs i s.cache hc
    have h := bind_resources I.weight bits (EstimatorFrontend.savingRound t saving i s.cache) next
      (RoundCacheSafe bits) (savingRound_cache I bits saving W Z hs i s.cache hc)
      W Z (5 + ((W + 5) * l.length + 1 : ℕ)) ((Z * l.length : ℕ) : ℝ) hstep.1 hstep.2 hn
    have hcode : EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving) (i :: l) s =
        (EstimatorFrontend.savingRound t saving i s.cache).bind next := by
      rw [EstimatorLoop.rounds]
      apply congrArg ((EstimatorFrontend.savingRound t saving i s.cache).bind)
      funext r
      cases r with
      | none => rfl
      | some zvc => rcases zvc with ⟨z, v, c⟩; rfl
    simp only [hcode]
    push_cast at h ⊢
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith [h.1, h.2]

private theorem folded_positive_zero (g : MSTApproximation.Grid)
    (records : List (EstimatorLoop.ScaleRecord (Fin (g.intervals + 1)))) (start : ℝ) :
    (Code.folded (EstimatorFrontend.totalStepResult g) records start).positiveReplies = 0 := by
  induction records generalizing start with
  | nil => rfl
  | cons r l ih =>
    simpa only [Code.folded, EstimatorFrontend.totalStepResult, Outcome.add, Outcome.combine,
      Nat.zero_add] using ih (start + g.scale r.index.val * r.saving)

theorem finish_expected {t : Tables} (m : Sym2 (Fin n) → ℝ)
    (bits : RuntimeWorld.Coordinate t k → Bool) (upper That : ℝ)
    (saved : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k))
    (hheight : t.coarse.intervals + 1 ≤ heightBudget n) (hlen : saved.records.length ≤ heightBudget n) :
    (EstimatorFrontend.finish t upper That saved).evaluate m bits (fun o => (o.work : ℝ)) ≤
        ((2 * heightBudget n + 7) * heightBudget n + 6 : ℕ) ∧
      (EstimatorFrontend.finish t upper That saved).evaluate m bits
        (fun o => (o.positiveReplies : ℝ)) = 0 := by
  have hw : (EstimatorFrontend.summed t.coarse saved.records).work ≤
      (2 * heightBudget n + 7) * heightBudget n :=
    (EstimatorFrontend.totals_work t.coarse saved.records).trans
      (Nat.mul_le_mul (by omega) hlen)
  have hz : (EstimatorFrontend.summed t.coarse saved.records).positiveReplies = 0 :=
    folded_positive_zero t.coarse saved.records 0
  constructor
  · rw [EstimatorFrontend.finish, Code.evaluate_work_bind, EstimatorFrontend.totals_evaluates]
    simp only [Code.evaluate, Outcome.add, Outcome.pure, Nat.add_zero]
    have hwR : ((EstimatorFrontend.summed t.coarse saved.records).work : ℝ) ≤
        ((2 * heightBudget n + 7) * heightBudget n : ℕ) := by exact_mod_cast hw
    push_cast at hwR ⊢
    linarith
  · rw [EstimatorFrontend.finish, Code.evaluate_positive_bind, EstimatorFrontend.totals_evaluates]
    simp only [Code.evaluate, Outcome.add, Outcome.pure, hz, Nat.cast_zero, add_zero]

private theorem labels_native (label : Vector (Fin n) (k + 1)) :
    FiniteMST.labels label.get = @List.toFinset (Fin n) (instDecidableEqFin n) label.toList := by
  calc
    FiniteMST.labels label.get = label.toList.toFinset := by
      simpa only [FiniteMST.labels] using (PublicTerminals.toList_toFinset label).symm
    _ = _ := by ext x; simp only [List.mem_toFinset]

private theorem ensures_true {M Q Out : Type*} (m : M → ℝ) (bits : Q → Bool) (p : Code M Q Out) :
    Causal.Ensures m bits p (fun _ => True) :=
  LargeCoverProgram.Support.ensures_of_runs m bits p _ (fun _ _ => True.intro)

theorem afterSaving_expected {t : Tables} (I : Instance (Fin n))
    (bits : RuntimeWorld.Coordinate t k → Bool) (label : Vector (Fin n) (k + 1))
    (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (upper : ℝ)
    (hheight : t.coarse.intervals + 1 ≤ heightBudget n)
    (r : Option (EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k)))
    (hc : StateSafe bits (t.coarse.intervals + 1) r) :
    (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse upper r).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤
        (BandEstimator.workPolynomial n + (2 * heightBudget n + 7) * heightBudget n + 8 : ℕ) ∧
      (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse upper r).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤ BandEstimator.positivePolynomial n := by
  cases r with
  | none =>
    simp only [EstimatorFrontend.afterSaving, Code.evaluate, Outcome.add, Outcome.pure,
      Nat.add_zero, Nat.zero_add, Nat.cast_zero]
    constructor
    · have hnat : 1 ≤ BandEstimator.workPolynomial n +
          (2 * heightBudget n + 7) * heightBudget n + 8 := by omega
      exact_mod_cast hnat
    · exact Nat.cast_nonneg _
  | some saved =>
    obtain ⟨hcache, hlength⟩ := hc saved rfl
    have hlen : saved.records.length ≤ heightBudget n := hlength.le.trans hheight
    let band := BandEstimator.fromParameters t.coarse label.get
      (fun i => RuntimeWorld.coarseKey t inverse i.val) root label.toList
        (parameters n (k + 1)) saved.cache
    let next : (Option ℝ × Cache (RuntimeWorld.Coordinate t k)) →
        Code (Sym2 (Fin n)) (RuntimeWorld.Coordinate t k) (Option ℝ) :=
      fun z => .tick 1 (match z.1 with
        | none => .pure none
        | some That => EstimatorFrontend.finish t upper That saved)
    have hband := BandEstimator.fromParameters_expected I bits t.coarse label.get hinj
      (fun i => RuntimeWorld.coarseKey t inverse i.val) root label.toList
      (PublicTerminals.toList_nodup label hinj) (labels_native label) hheight saved.cache hcache
    have hn (z : Option ℝ × Cache (RuntimeWorld.Coordinate t k)) (_hz : True) :
        (next z).evaluate I.weight bits (fun o => (o.work : ℝ)) ≤
            ((2 * heightBudget n + 7) * heightBudget n + 8 : ℕ) ∧
          (next z).evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ 0 := by
      cases hv : z.1 with
      | none =>
        simp only [next, hv, Code.evaluate, Outcome.add, Outcome.pure,
          Nat.add_zero, Nat.zero_add, Nat.cast_zero, le_refl, and_true]
        exact_mod_cast (show 2 ≤ (2 * heightBudget n + 7) * heightBudget n + 8 by omega)
      | some That =>
        have hf := finish_expected I.weight bits upper That saved hheight hlen
        dsimp only [next]
        rw [hv, MSTApproximation.evaluate_tick_work, MSTApproximation.evaluate_tick_positive]
        constructor
        · push_cast at hf ⊢
          linarith [hf.1]
        · exact hf.2.le
    have h := bind_resources I.weight bits band next (fun _ => True) (ensures_true I.weight bits band)
      (BandEstimator.workPolynomial n) (BandEstimator.positivePolynomial n)
      (((2 * heightBudget n + 7) * heightBudget n + 8 : ℕ) : ℝ) 0 hband.1 hband.2 hn
    have hcode : EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse upper (some saved) =
        band.bind next := by
      rw [EstimatorFrontend.afterSaving]
      apply congrArg band.bind
      funext z
      cases hv : z.1 <;> simp only [next, hv]
    rw [hcode]
    push_cast at h ⊢
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem afterMST_expected {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t) (W Z : ℕ)
    (hs : SavingResources I bits saving W Z) (hheight : t.coarse.intervals + 1 ≤ heightBudget n)
    (mst : MSTApproximation.IntervalAnswer (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits mst.cache) :
    (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving mst).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤
        (heightBudget n * (W + 9) + BandEstimator.workPolynomial n +
          (2 * heightBudget n + 7) * heightBudget n + 13 : ℕ) ∧
      (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving mst).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤
        (heightBudget n * Z + BandEstimator.positivePolynomial n : ℕ) := by
  let indices := List.finRange (t.coarse.intervals + 1)
  let initial : EstimatorLoop.State (Index t) (RuntimeWorld.Coordinate t k) := ⟨mst.cache, []⟩
  let rounds := EstimatorLoop.rounds (EstimatorFrontend.savingRound t saving) indices initial
  have hround := rounds_expected I bits saving W Z hs indices initial hc
  have hsafe : Causal.Ensures I.weight bits rounds (StateSafe bits (t.coarse.intervals + 1)) := by
    simpa only [indices, initial, List.length_finRange, List.length_nil, zero_add] using
      rounds_cache I bits saving W Z hs indices initial hc
  simp only [indices, List.length_finRange] at hround
  have h := bind_resources I.weight bits rounds
    (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse mst.upper)
    (StateSafe bits (t.coarse.intervals + 1)) hsafe
    ((((W + 5) * (t.coarse.intervals + 1) + 1 : ℕ) : ℝ))
    (((Z * (t.coarse.intervals + 1) : ℕ) : ℝ))
    (((BandEstimator.workPolynomial n + (2 * heightBudget n + 7) * heightBudget n + 8 : ℕ) : ℝ))
    (BandEstimator.positivePolynomial n) hround.1 hround.2
    (afterSaving_expected I bits label hinj root inverse mst.upper hheight)
  have hm := Nat.mul_le_mul_right (W + 9) hheight
  have hz : Z * (t.coarse.intervals + 1) ≤ heightBudget n * Z := by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_left Z hheight
  constructor
  · rw [EstimatorFrontend.afterMST, MSTApproximation.evaluate_tick_work]
    change (((4 * (t.coarse.intervals + 1) + 4 : ℕ) : ℝ)) +
      (rounds.bind (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse mst.upper)).evaluate
        I.weight bits (fun o => (o.work : ℝ)) ≤ _
    have hmR : (((t.coarse.intervals + 1) * (W + 9) : ℕ) : ℝ) ≤
        (heightBudget n * (W + 9) : ℕ) := by exact_mod_cast hm
    push_cast at h hmR ⊢
    nlinarith [h.1]
  · rw [EstimatorFrontend.afterMST, MSTApproximation.evaluate_tick_positive]
    change (rounds.bind (EstimatorFrontend.afterSaving (parameters n (k + 1)) label root t inverse mst.upper)).evaluate
      I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ _
    have hzR : ((Z * (t.coarse.intervals + 1) : ℕ) : ℝ) ≤ (heightBudget n * Z : ℕ) := by exact_mod_cast hz
    push_cast at h hzR ⊢
    linarith [h.2]

/-- No coverage, size, calibration, phase, or estimator-correctness event is needed.
Only fixed-oracle cache consistency and the event-free saving CODE accounts occur. -/
theorem program_expected {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t) (W Z : ℕ)
    (hs : SavingResources I bits saving W Z)
    (hcoarse : t.coarse.intervals + 1 ≤ heightBudget n) (hfine : t.fine.intervals ≤ heightBudget n)
    (hroot : ∀ i < t.fine.intervals, bits (RuntimeWorld.fineKey t inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤ workBudget n W ∧
      (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤ positiveBudget n Z := by
  let fine := EstimatorMST.program n label.get (RuntimeWorld.fineKey t inverse) t.fine label.toList root cache
  have henum : Finset.univ.image label.get = label.toList.toFinset :=
    (PublicTerminals.toList_toFinset label).symm
  have hf : fine.evaluate I.weight bits (fun o => (o.work : ℝ)) ≤ fineWork n ∧
      fine.evaluate I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ finePositive n :=
    EstimatorMST.expected_resources_polylog I bits n label.get hinj (RuntimeWorld.fineKey t inverse)
      t.fine label.toList (PublicTerminals.toList_nodup label hinj) root cache hc henum hroot
      (PublicTerminals.length_le label hinj) hfine
  have hcache : Causal.Ensures I.weight bits fine (fun mst => Cache.Correct bits mst.cache) :=
    ensures_of_support I.weight bits fine _ (fun seed hmass =>
      EstimatorMST.cache_on_support I bits n label.get (RuntimeWorld.fineKey t inverse)
        t.fine label.toList root cache hc henum hroot seed hmass)
  have h := bind_resources I.weight bits fine
    (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving)
    (fun mst => Cache.Correct bits mst.cache) hcache (fineWork n) (finePositive n)
    (((heightBudget n * (W + 9) + BandEstimator.workPolynomial n +
      (2 * heightBudget n + 7) * heightBudget n + 13 : ℕ) : ℝ))
    (((heightBudget n * Z + BandEstimator.positivePolynomial n : ℕ) : ℝ)) hf.1 hf.2
    (afterMST_expected I bits label hinj root inverse saving W Z hs hcoarse)
  rw [EstimatorFrontend.program]
  change (fine.bind (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving)).evaluate
      I.weight bits (fun o => (o.work : ℝ)) ≤ _ ∧
    (fine.bind (EstimatorFrontend.afterMST (parameters n (k + 1)) label root t inverse saving)).evaluate
      I.weight bits (fun o => (o.positiveReplies : ℝ)) ≤ _
  unfold workBudget positiveBudget
  push_cast at h ⊢
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem program_averaged_resources {Ω : Type*} [Fintype Ω] {t : Tables}
    (mu : Law Ω) (oracle : Ω → RuntimeWorld.Coordinate t k → Bool)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (root : Fin (k + 1)) (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t) (W Z : ℕ)
    (hcoarse : t.coarse.intervals + 1 ≤ heightBudget n) (hfine : t.fine.intervals ≤ heightBudget n)
    (hs : ∀ omega, 0 < mu.mass omega → SavingResources I (oracle omega) saving W Z)
    (hroot : ∀ omega, 0 < mu.mass omega → ∀ i < t.fine.intervals,
      oracle omega (RuntimeWorld.fineKey t inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate t k))
    (hc : ∀ omega, 0 < mu.mass omega → Cache.Correct (oracle omega) cache) :
    mu.expect (fun omega =>
      (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate
        I.weight (oracle omega) (fun o => (o.work : ℝ))) ≤ workBudget n W ∧
      mu.expect (fun omega =>
        (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate
          I.weight (oracle omega) (fun o => (o.positiveReplies : ℝ))) ≤ positiveBudget n Z := by
  constructor
  · exact (mu.expect_mono_support (fun omega ho =>
      (program_expected I (oracle omega) label hinj root inverse saving W Z (hs omega ho)
        hcoarse hfine (hroot omega ho) cache (hc omega ho)).1)).trans_eq (Law.expect_const _ _)
  · exact (mu.expect_mono_support (fun omega ho =>
      (program_expected I (oracle omega) label hinj root inverse saving W Z (hs omega ho)
        hcoarse hfine (hroot omega ho) cache (hc omega ho)).2)).trans_eq (Law.expect_const _ _)

def coreFactor : ℕ := 15 * publicFactor + 3
def bandWorkFactor : ℕ := 1000000000000 * coreFactor ^ 14
def bandPositiveFactor : ℕ := coreFactor ^ 3

def baseWorkFactor : ℕ :=
  EstimatorMST.workFactor + bandWorkFactor + 2 * heightFactor ^ 2 + 16 * heightFactor + 13

def basePositiveFactor : ℕ := EstimatorMST.positiveFactor + bandPositiveFactor

def polylogDegree (d : ℕ) : ℕ := max (d + 2) 126

def clockFactor (K : ℕ) : ℕ :=
  EstimatorClocks.amplification * heightFactor * (heightFactor + 1) * (K + 1)

def polylogFactor (K setup : ℕ) : ℕ :=
  baseWorkFactor + basePositiveFactor + clockFactor K + heightFactor * (setup + 1)

private theorem sum_bound (l : List ℕ) (B : ℕ) (h : ∀ x ∈ l, x ≤ B) :
    l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem band_core_polylog (n : ℕ) :
    BandEstimator.core n + 2 ≤ coreFactor * ell n ^ 9 := by
  have hs := sum_bound (coreSizes n) (publicFactor * ell n ^ 9)
    (fun x hx => all_core_polylog n x hx)
  have hlen : (coreSizes n).length = 15 := rfl
  rw [hlen] at hs
  have he : 1 ≤ ell n ^ 9 := Nat.succ_le_of_lt (pow_pos (ell_pos n) 9)
  unfold BandEstimator.core coreFactor
  nlinarith

theorem band_polynomial_polylog (n : ℕ) :
    BandEstimator.workPolynomial n ≤ bandWorkFactor * (n + 1) * ell n ^ 126 ∧
      BandEstimator.positivePolynomial n ≤ bandPositiveFactor * ell n ^ 27 := by
  have hc := band_core_polylog n
  constructor
  · unfold BandEstimator.workPolynomial
    calc
      _ ≤ 1000000000000 * (n + 1) * (coreFactor * ell n ^ 9) ^ 14 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 14)
      _ = _ := by unfold bandWorkFactor; ring
  · unfold BandEstimator.positivePolynomial
    calc
      _ ≤ (coreFactor * ell n ^ 9) ^ 3 := Nat.pow_le_pow_left hc 3
      _ = _ := by unfold bandPositiveFactor; ring

theorem budget_base_polylog (n W Z : ℕ) :
    workBudget n W ≤ heightBudget n * W + baseWorkFactor * (n + 1) * ell n ^ 126 ∧
      positiveBudget n Z ≤ heightBudget n * Z + basePositiveFactor * ell n ^ 27 := by
  let X := (n + 1) * ell n ^ 126
  have hX : 1 ≤ X := Nat.succ_le_of_lt (by dsimp [X]; exact mul_pos (by omega) (pow_pos (ell_pos n) 126))
  have hE (a : ℕ) (ha : a ≤ 126) : ell n ^ a ≤ X := by
    calc
      ell n ^ a ≤ ell n ^ 126 := ell_power_le n a 126 ha
      _ = 1 * ell n ^ 126 := by omega
      _ ≤ X := Nat.mul_le_mul_right _ (by omega)
  have hH : heightBudget n ≤ heightFactor * X := by
    simpa only [heightBudget, pow_one] using Nat.mul_le_mul_left heightFactor (hE 1 (by omega))
  have hH2 : heightBudget n ^ 2 ≤ heightFactor ^ 2 * X := by
    simpa only [heightBudget, mul_pow] using Nat.mul_le_mul_left (heightFactor ^ 2) (hE 2 (by omega))
  have hf : fineWork n ≤ EstimatorMST.workFactor * X := by
    calc
      _ ≤ EstimatorMST.workFactor * (n + 1) * ell n ^ 126 :=
        Nat.mul_le_mul_left _ (ell_power_le n 36 126 (by omega))
      _ = _ := by dsimp [X]; ring
  have hb := band_polynomial_polylog n
  have hbW : BandEstimator.workPolynomial n ≤ bandWorkFactor * X := by
    simpa only [X, Nat.mul_assoc] using hb.1
  have hbase : fineWork n + BandEstimator.workPolynomial n + 16 * heightBudget n +
      2 * heightBudget n ^ 2 + 13 ≤ baseWorkFactor * X := by
    unfold baseWorkFactor
    nlinarith
  constructor
  · calc
      workBudget n W = heightBudget n * W +
          (fineWork n + BandEstimator.workPolynomial n + 16 * heightBudget n +
            2 * heightBudget n ^ 2 + 13) := by unfold workBudget; ring
      _ ≤ heightBudget n * W + baseWorkFactor * X := Nat.add_le_add_left hbase _
      _ = _ := by dsimp [X]; ring
  · calc
      positiveBudget n Z = heightBudget n * Z + (finePositive n + BandEstimator.positivePolynomial n) := by
        unfold positiveBudget
        ring
      _ ≤ heightBudget n * Z + (finePositive n + bandPositiveFactor * ell n ^ 27) :=
        Nat.add_le_add_left (Nat.add_le_add_left hb.2 _) _
      _ = _ := by unfold finePositive basePositiveFactor; ring

private theorem amplified_weighted (n K d scale account extra : ℕ) (hs : 1 ≤ scale)
    (ha : account ≤ K * scale * t n * ell n ^ d) :
    heightBudget n * (EstimatorClocks.amplification * (heightBudget n + 1) * (account + 1) + extra) ≤
      clockFactor K * scale * t n * ell n ^ (d + 2) + heightFactor * extra * ell n := by
  have hp : 1 ≤ scale * t n * ell n ^ d := Nat.succ_le_of_lt
    (mul_pos (mul_pos (by omega) (t_pos n)) (pow_pos (ell_pos n) d))
  have ha1 : account + 1 ≤ (K + 1) * scale * t n * ell n ^ d := by nlinarith
  have hH : heightBudget n + 1 ≤ (heightFactor + 1) * ell n := by
    have he := ell_ge_one n
    unfold heightBudget
    nlinarith
  have hHH : heightBudget n * (heightBudget n + 1) ≤ heightFactor * (heightFactor + 1) * ell n ^ 2 := by
    calc
      _ ≤ (heightFactor * ell n) * ((heightFactor + 1) * ell n) := Nat.mul_le_mul le_rfl hH
      _ = _ := by ring
  calc
    _ = EstimatorClocks.amplification * (heightBudget n * (heightBudget n + 1)) * (account + 1) +
        heightBudget n * extra := by ring
    _ ≤ EstimatorClocks.amplification * (heightFactor * (heightFactor + 1) * ell n ^ 2) *
        ((K + 1) * scale * t n * ell n ^ d) + heightBudget n * extra :=
      Nat.add_le_add_right (Nat.mul_le_mul (Nat.mul_le_mul_left _ hHH) ha1) _
    _ = _ := by unfold clockFactor heightBudget; rw [pow_add]; ring

private theorem scaled_power (n scale a b : ℕ) (hs : 1 ≤ scale) (hab : a ≤ b) :
    ell n ^ a ≤ scale * t n * ell n ^ b := by
  calc
    ell n ^ a ≤ ell n ^ b := ell_power_le n a b hab
    _ = (1 * 1) * ell n ^ b := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul hs (show 1 ≤ t n from t_pos n))

/-- `setup` counts the actual per-stage selector/flattening overhead. For the
checked `SavingEstimator.Clocked.fromParameters`, it is `9+16=25`. -/
theorem clocked_budgets_polylog (n K d AW AP setup : ℕ)
    (hw : AW ≤ K * (n + 1) * t n * ell n ^ d) (hp : AP ≤ K * t n * ell n ^ d) :
    workBudget n ((EstimatorClocks.stage n AW AP).workBudget + setup) ≤
        polylogFactor K setup * (n + 1) * t n * ell n ^ polylogDegree d ∧
      positiveBudget n ((EstimatorClocks.stage n AW AP).disclosureBudget + 1) ≤
        polylogFactor K setup * t n * ell n ^ polylogDegree d := by
  let X := (n + 1) * t n * ell n ^ polylogDegree d
  let Y := t n * ell n ^ polylogDegree d
  have hbase := budget_base_polylog n
    ((EstimatorClocks.stage n AW AP).workBudget + setup)
    ((EstimatorClocks.stage n AW AP).disclosureBudget + 1)
  have hdeg : d + 2 ≤ polylogDegree d := Nat.le_max_left _ _
  have h126 : 126 ≤ polylogDegree d := Nat.le_max_right _ _
  have h1 : 1 ≤ polylogDegree d := by omega
  have hWX := amplified_weighted n K d (n + 1) AW setup (by omega) hw
  have hPY := amplified_weighted n K d 1 AP 1 (by omega) (by simpa only [mul_one] using hp)
  have hW : heightBudget n * ((EstimatorClocks.stage n AW AP).workBudget + setup) ≤
      clockFactor K * X + heightFactor * setup * X := by
    calc
      _ ≤ clockFactor K * (n + 1) * t n * ell n ^ (d + 2) + heightFactor * setup * ell n := hWX
      _ ≤ clockFactor K * (n + 1) * t n * ell n ^ polylogDegree d + heightFactor * setup * X :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (ell_power_le n _ _ hdeg))
          (Nat.mul_le_mul_left _ (by
            simpa only [pow_one] using scaled_power n (n + 1) 1 (polylogDegree d) (by omega) h1))
      _ = _ := by dsimp [X]; ring
  have hP : heightBudget n * ((EstimatorClocks.stage n AW AP).disclosureBudget + 1) ≤
      clockFactor K * Y + heightFactor * Y := by
    calc
      _ ≤ clockFactor K * t n * ell n ^ (d + 2) + heightFactor * ell n := by
        simpa only [EstimatorClocks.stage, EstimatorClocks.byHeight, mul_one, one_mul] using hPY
      _ ≤ clockFactor K * t n * ell n ^ polylogDegree d + heightFactor * Y :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (ell_power_le n _ _ hdeg))
          (Nat.mul_le_mul_left _ (by
            simpa only [pow_one, one_mul] using scaled_power n 1 1 (polylogDegree d) (by omega) h1))
      _ = _ := by dsimp [Y]; ring
  have hbW : baseWorkFactor * (n + 1) * ell n ^ 126 ≤ baseWorkFactor * X := by
    calc
      _ = baseWorkFactor * (n + 1) * 1 * ell n ^ 126 := by ring
      _ ≤ baseWorkFactor * (n + 1) * t n * ell n ^ polylogDegree d :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (show 1 ≤ t n from t_pos n))
          (ell_power_le n _ _ h126)
      _ = _ := by dsimp [X]; ring
  have hbP : basePositiveFactor * ell n ^ 27 ≤ basePositiveFactor * Y :=
    Nat.mul_le_mul_left _ (by
      simpa only [one_mul] using scaled_power n 1 27 (polylogDegree d) (by omega) (by omega))
  constructor
  · calc
      _ ≤ heightBudget n * ((EstimatorClocks.stage n AW AP).workBudget + setup) +
          baseWorkFactor * (n + 1) * ell n ^ 126 := hbase.1
      _ ≤ (clockFactor K * X + heightFactor * setup * X) + baseWorkFactor * X := Nat.add_le_add hW hbW
      _ ≤ polylogFactor K setup * X := by unfold polylogFactor; nlinarith
      _ = _ := by dsimp [X]; ring
  · calc
      _ ≤ heightBudget n * ((EstimatorClocks.stage n AW AP).disclosureBudget + 1) +
          basePositiveFactor * ell n ^ 27 := hbase.2
      _ ≤ (clockFactor K * Y + heightFactor * Y) + basePositiveFactor * Y := Nat.add_le_add hP hbP
      _ ≤ polylogFactor K setup * Y := by
        unfold polylogFactor
        nlinarith [Nat.zero_le (baseWorkFactor * Y), Nat.zero_le (heightFactor * setup * Y)]
      _ = _ := by dsimp [Y]; ring

theorem program_expected_clocked {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t) (K d AW AP setup : ℕ)
    (hs : SavingResources I bits saving ((EstimatorClocks.stage n AW AP).workBudget + setup)
      ((EstimatorClocks.stage n AW AP).disclosureBudget + 1))
    (hw : AW ≤ K * (n + 1) * EstimatorParameters.t n * ell n ^ d)
    (hp : AP ≤ K * EstimatorParameters.t n * ell n ^ d)
    (hcoarse : t.coarse.intervals + 1 ≤ heightBudget n) (hfine : t.fine.intervals ≤ heightBudget n)
    (hroot : ∀ i < t.fine.intervals, bits (RuntimeWorld.fineKey t inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤
        (polylogFactor K setup * (n + 1) * EstimatorParameters.t n * ell n ^ polylogDegree d : ℕ) ∧
      (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤
        (polylogFactor K setup * EstimatorParameters.t n * ell n ^ polylogDegree d : ℕ) := by
  have h := program_expected I bits label hinj root inverse saving _ _ hs hcoarse hfine hroot cache hc
  have hb := clocked_budgets_polylog n K d AW AP setup hw hp
  exact ⟨h.1.trans (by exact_mod_cast hb.1), h.2.trans (by exact_mod_cast hb.2)⟩

theorem withParameters_expected {t : Tables} (I : Instance (Fin n)) (bits : RuntimeWorld.Coordinate t k → Bool)
    (p : PublicParameters) (hp : p = parameters n (k + 1))
    (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get) (root : Fin (k + 1))
    (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t) (W Z : ℕ)
    (hs : SavingResources I bits saving W Z)
    (hcoarse : t.coarse.intervals + 1 ≤ heightBudget n) (hfine : t.fine.intervals ≤ heightBudget n)
    (hroot : ∀ i < t.fine.intervals, bits (RuntimeWorld.fineKey t inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate t k)) (hc : Cache.Correct bits cache) :
    (EstimatorFrontend.program p label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.work : ℝ)) ≤ workBudget n W ∧
      (EstimatorFrontend.program p label root t inverse saving cache).evaluate I.weight bits
        (fun o => (o.positiveReplies : ℝ)) ≤ positiveBudget n Z := by
  subst p
  exact program_expected I bits label hinj root inverse saving W Z hs hcoarse hfine hroot cache hc

theorem program_averaged_clocked {Ω : Type*} [Fintype Ω] {t : Tables}
    (mu : Law Ω) (oracle : Ω → RuntimeWorld.Coordinate t k → Bool)
    (I : Instance (Fin n)) (label : Vector (Fin n) (k + 1)) (hinj : Function.Injective label.get)
    (root : Fin (k + 1)) (inverse : Vector (Fin (k + 1)) n) (saving : Saving n k t)
    (K d AW AP setup : ℕ)
    (hcoarse : t.coarse.intervals + 1 ≤ heightBudget n) (hfine : t.fine.intervals ≤ heightBudget n)
    (hs : ∀ omega, 0 < mu.mass omega →
      SavingResources I (oracle omega) saving ((EstimatorClocks.stage n AW AP).workBudget + setup)
        ((EstimatorClocks.stage n AW AP).disclosureBudget + 1))
    (hw : AW ≤ K * (n + 1) * EstimatorParameters.t n * ell n ^ d)
    (hp : AP ≤ K * EstimatorParameters.t n * ell n ^ d)
    (hroot : ∀ omega, 0 < mu.mass omega → ∀ i < t.fine.intervals,
      oracle omega (RuntimeWorld.fineKey t inverse i (label.get root)) = true)
    (cache : Cache (RuntimeWorld.Coordinate t k))
    (hc : ∀ omega, 0 < mu.mass omega → Cache.Correct (oracle omega) cache) :
    mu.expect (fun omega =>
      (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate
        I.weight (oracle omega) (fun o => (o.work : ℝ))) ≤
        (polylogFactor K setup * (n + 1) * EstimatorParameters.t n * ell n ^ polylogDegree d : ℕ) ∧
      mu.expect (fun omega =>
        (EstimatorFrontend.program (parameters n (k + 1)) label root t inverse saving cache).evaluate
          I.weight (oracle omega) (fun o => (o.positiveReplies : ℝ))) ≤
        (polylogFactor K setup * EstimatorParameters.t n * ell n ^ polylogDegree d : ℕ) := by
  have h := program_averaged_resources mu oracle I label hinj root inverse saving _ _
    hcoarse hfine hs hroot cache hc
  have hb := clocked_budgets_polylog n K d AW AP setup hw hp
  exact ⟨h.1.trans (by exact_mod_cast hb.1), h.2.trans (by exact_mod_cast hb.2)⟩

end SteinerUpperBound.EstimatorFrontend.Resources

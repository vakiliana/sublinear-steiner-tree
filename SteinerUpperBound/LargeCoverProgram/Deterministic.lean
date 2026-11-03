module

public import SteinerUpperBound.LocalAccess.Hits
public import SteinerUpperBound.Covers.OracleProgramMean
public import SteinerUpperBound.SmallCoverProgram
public import SteinerUpperBound.ReusableSample
public import SteinerUpperBound.SavingScores

@[expose] public section

namespace SteinerUpperBound.LargeCoverProgram

open SteinerLowerBound QueryProgram
open scoped Classical BigOperators

variable {M Q R S V : Type*}

/-- Fixed-oracle deterministic code; retained replies may still be resolved. -/
def Deterministic : Code M Q R → Prop
  | .pure _ => True
  | .metric _ next => ∀ x, Deterministic (next x)
  | .retained _ next => ∀ x, Deterministic (next x)
  | .tick _ next => Deterministic next
  | _ => False

theorem deterministic_bind (p : Code M Q R) (k : R → Code M Q S)
    (hp : Deterministic p) (hk : ∀ r, Deterministic (k r)) :
    Deterministic (p.bind k) := by
  induction p with
  | pure r => exact hk r
  | metric q next ih => exact fun x => ih x (hp x)
  | retained q next ih => exact fun x => ih x (hp x)
  | tick n next ih => exact ih hp
  | uniform => exact hp.elim
  | coin => exact hp.elim

theorem deterministic_map (p : Code M Q R) (f : R → S) (hp : Deterministic p) :
    Deterministic (p.map f) :=
  deterministic_bind p (fun r => .pure (f r)) hp (fun _ => trivial)

theorem deterministic_foldList {A : Type*} (body : S → A → Code M Q S)
    (hbody : ∀ s a, Deterministic (body s a)) (l : List A) (s : S) :
    Deterministic (Code.foldList body l s) := by
  induction l generalizing s with
  | nil => trivial
  | cons a l ih => exact deterministic_bind _ _ (hbody s a) ih

theorem deterministic_of_metricOnly (p : Code M Q R)
    (hp : SmallCoverProgram.MetricOnly p) : Deterministic p := by
  induction p with
  | pure => trivial
  | metric q next ih => exact fun x => ih x (hp x)
  | tick n next ih => exact ih hp
  | retained => exact hp.elim
  | uniform => exact hp.elim
  | coin => exact hp.elim

theorem deterministic_run_evaluates (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (hp : Deterministic p) (o : Outcome R)
    (ho : Covers.OracleProgram.Runs m bits p o) : Code.Evaluates m bits p o := by
  induction p generalizing o with
  | pure r => cases ho; exact Code.evaluates_pure _ _ _
  | metric q next ih =>
      cases ho with
      | metric ho => intro F; exact ih (m q) (hp (m q)) _ ho _
  | retained q next ih =>
      cases ho with
      | retained ho => intro F; exact ih (bits q) (hp (bits q)) _ ho _
  | tick n next ih =>
      cases ho with
      | tick ho => intro F; exact ih hp _ ho _
  | uniform => exact hp.elim
  | coin => exact hp.elim

theorem deterministic_run_eq (m : M → ℝ) (bits : Q → Bool)
    (p : Code M Q R) (hp : Deterministic p) (r : Outcome R)
    (hr : Code.Evaluates m bits p r) (o : Outcome R)
    (ho : Covers.OracleProgram.Runs m bits p o) : o = r := by
  have he := deterministic_run_evaluates m bits p hp o ho
  let F : Outcome R → ℝ := fun z => if z = r then 1 else 0
  have hh : F o = F r := (he F).symm.trans (hr F)
  by_contra hn
  simp [F, hn] at hh

theorem resolve_deterministic (q : Q) (c : Cache Q) :
    Deterministic (Cache.resolve q c : Code M Q _) := by
  cases h : c q <;> simp [Cache.resolve, h, Deterministic]

theorem member_deterministic (x : V) (l : List V) :
    Deterministic (ComponentExplore.member x l : Code M Q _) := by
  induction l with
  | nil => trivial
  | cons y l ih => simp only [ComponentExplore.member, Deterministic]; split_ifs <;> trivial

theorem pending_deterministic (found done l : List V) :
    Deterministic (ComponentExplore.pendingProgram found done l : Code M Q _) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
      apply deterministic_bind _ _ (member_deterministic x found)
      intro f
      dsimp [Deterministic]
      cases f
      · exact ih
      · apply deterministic_bind _ _ (member_deterministic x done)
        intro d
        cases d <;> trivial

theorem step_deterministic (key : V → Q) (a : ℝ) (B : ℕ) (x : V)
    (s : ComponentExplore.Memory V Q) (y : V) :
    Deterministic (ComponentExplore.stepProgram key a B x s y) := by
  unfold ComponentExplore.stepProgram
  dsimp [Deterministic]
  split_ifs
  · trivial
  · apply deterministic_bind _ _ (member_deterministic _ _)
    intro seen
    cases seen
    · intro d
      dsimp [Deterministic]
      split_ifs
      · exact deterministic_bind _ _ (resolve_deterministic _ _) (fun _ => trivial)
      · trivial
    · trivial

theorem explore_deterministic [Fintype V] (key : V → Q) (a : ℝ) (B : ℕ)
    (terminals : List V) (root : V) (c : Cache Q) :
    Deterministic (ComponentExplore.program key a B terminals root c) := by
  suffices ∀ fuel s, Deterministic (ComponentExplore.loopProgram key a B terminals fuel s) from
    this _ _
  intro fuel
  induction fuel with
  | zero =>
      intro s
      dsimp [ComponentExplore.loopProgram, Deterministic]
      split_ifs
      · trivial
      · exact deterministic_bind _ _ (pending_deterministic _ _ _) (fun _ => trivial)
  | succ fuel ih =>
      intro s
      dsimp [ComponentExplore.loopProgram, Deterministic]
      split_ifs
      · trivial
      · apply deterministic_bind _ _ (pending_deterministic _ _ _)
        intro p
        cases p with
        | none => trivial
        | some x =>
            exact deterministic_bind _ _
              (deterministic_foldList _ (step_deterministic key a B x) _ _) ih

theorem hits_deterministic {n : ℕ} (D : Vector Bool n) (l : List (Fin n)) :
    Deterministic (LocalAccess.hitsProgram (Q := Q) D l) := by
  induction l with
  | nil => trivial
  | cons x l ih =>
      dsimp [LocalAccess.hitsProgram, Deterministic]
      cases D.get x <;> trivial

theorem nth_deterministic (l : List V) (i : ℕ) :
    Deterministic (LocalAccess.nthProgram l i : Code M Q _) := by
  induction l generalizing i with
  | nil => trivial
  | cons x l ih =>
      cases i with
      | zero => trivial
      | succ i => exact ih i

theorem tabulate_deterministic {A : Type*} {n : ℕ} (body : Fin n → Code M Q A)
    (hbody : ∀ i, Deterministic (body i)) (init : Vector A n) :
    Deterministic (SmallCoverProgram.tabulate body init) := by
  apply deterministic_foldList
  intro v i
  exact deterministic_bind _ _ (hbody i) (fun _ => trivial)

theorem pack_deterministic (n : ℕ) (l : List V) :
    Deterministic (LocalAccess.packProgram n l : Code M Q _) := by
  apply deterministic_bind _ _ (by trivial)
  intro init
  exact tabulate_deterministic _ (fun i => nth_deterministic l i.val) init

theorem canonical_deterministic (wanted order : List V) :
    Deterministic (LocalAccess.canonicalProgram wanted order : Code M Q _) := by
  induction order with
  | nil => trivial
  | cons x l ih =>
      apply deterministic_bind _ _ (member_deterministic _ _)
      intro h
      cases h
      · exact ih
      · exact deterministic_bind _ _ ih (fun _ => trivial)

theorem near_deterministic (r : ℝ) (v : V) (points : List V) :
    Deterministic (LocalAccess.nearProgram (Q := Q) r v points) := by
  induction points with
  | nil => trivial
  | cons x l ih =>
      intro d
      dsimp [Deterministic]
      split_ifs <;> trivial

theorem centers_deterministic (r : ℝ) (points vertices : List V) (d : ℕ) :
    Deterministic (LocalAccess.centersProgram (Q := Q) r points d vertices) := by
  induction vertices generalizing d with
  | nil => cases d <;> trivial
  | cons v l ih =>
      cases d with
      | zero => trivial
      | succ d =>
          apply deterministic_bind _ _ (near_deterministic _ _ _)
          intro h
          cases h
          · exact ih _
          · exact deterministic_bind _ _ (ih _) (fun _ => trivial)

theorem frame_deterministic (r : ℝ) (d B : ℕ) (vertices terminals points : List V) :
    Deterministic (LocalAccess.frameProgram (Q := Q) r d B vertices terminals points) := by
  apply deterministic_bind _ _ (canonical_deterministic _ _)
  intro C
  apply deterministic_bind _ _ (pack_deterministic _ _)
  intro _
  apply deterministic_bind
  · unfold LocalAccess.prepareProgram
    exact deterministic_bind _ _ (centers_deterministic _ _ _ _) (fun _ =>
      deterministic_bind _ _ (pack_deterministic _ _) (fun _ => trivial))
  · exact fun _ => trivial

theorem locate_deterministic [Fintype V] (key : V → Q) (a : ℝ) (d B : ℕ)
    (vertices terminals : List V) (root : V) (c : Cache Q) :
    Deterministic (LocalAccess.locateProgram key a d B vertices terminals root c) := by
  apply deterministic_bind _ _ (explore_deterministic _ _ _ _ _ _)
  intro e
  dsimp [Deterministic]
  cases e.complete
  · trivial
  · exact deterministic_bind _ _ (frame_deterministic _ _ _ _ _ _) (fun _ => trivial)

theorem covered_deterministic {n : ℕ} (r : ℝ) (centers : List (Fin n)) :
    Deterministic (LocalAccess.coveredProgram (Q := Q) r centers) := by
  apply deterministic_bind _ _ (by trivial)
  intro init
  exact tabulate_deterministic _ (fun v => near_deterministic r v centers) init

end SteinerUpperBound.LargeCoverProgram

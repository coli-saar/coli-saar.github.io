-- Part 1) Provided Code

import Mathlib
import Mathlib.Data.Finset.Basic
import Init.Data.List.Find
import Init.Data.List.Lemmas

class Truthy (α : Type) where
  isTrue : α → Prop

instance : Truthy Bool where
  isTrue b := b = true

instance : Truthy (Option Bool) where
  isTrue o := o = some true

abbrev Obj := Nat

structure StaticState where
  objects : List Obj
  ishomebase_p : Obj → Bool
  safe_p : Obj → Bool
  loc_t : Obj → Bool
  paper_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_p : Obj → α
  satisfied_p : Obj → α
  wantspaper_p : Obj → α
  unpacked_p : Obj → α
  carrying_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidIshomebaseParam (s : StaticState) : Prop :=
  ∀ var_loc, s.ishomebase_p var_loc = true → s.loc_t var_loc = true

def ValidSafeParam (s : StaticState) : Prop :=
  ∀ var_loc, s.safe_p var_loc = true → s.loc_t var_loc = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.loc_t x = true → x ∈ s.objects) ∧
  (∀ x, s.paper_t x = true → x ∈ s.objects) ∧
  (∀ x, s.loc_t x = true → s.paper_t x = false)

def UniqueHomeBase (s : StaticState) : Prop :=
  ∃! loc, s.ishomebase_p loc = true

def HomeBaseIsSafe (s : StaticState) : Prop :=
  ∀ loc, s.ishomebase_p loc = true → s.safe_p loc = true

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects → (s.loc_t x = true ∨ s.paper_t x = true)

def WellFormedStatic (s : StaticState) : Prop := 
  ObjectsUnique s ∧
  ValidIshomebaseParam s ∧
  ValidSafeParam s ∧
  ValidTypeHierarchy s ∧
  UniqueHomeBase s ∧
  HomeBaseIsSafe s ∧
  TypeCoverage s

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_loc, Truthy.isTrue (d.at_p var_loc) → s.loc_t var_loc = true

def ValidSatisfiedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_loc, Truthy.isTrue (d.satisfied_p var_loc) → s.loc_t var_loc = true

def ValidWantspaperParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_loc, Truthy.isTrue (d.wantspaper_p var_loc) → s.loc_t var_loc = true

def ValidUnpackedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_paper, Truthy.isTrue (d.unpacked_p var_paper) → s.paper_t var_paper = true

def ValidCarryingParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_paper, Truthy.isTrue (d.carrying_p var_paper) → s.paper_t var_paper = true

def AtMostOneAt {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ loc1 loc2, Truthy.isTrue (d.at_p loc1) → Truthy.isTrue (d.at_p loc2) → loc1 = loc2

def PaperStatusExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ paper, ¬ (Truthy.isTrue (d.unpacked_p paper) ∧ Truthy.isTrue (d.carrying_p paper))

def SatisfiedWantsPaperExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ loc, ¬ (Truthy.isTrue (d.satisfied_p loc) ∧ Truthy.isTrue (d.wantspaper_p loc))

def ExistsOneAt (s : State) : Prop :=
  ∃ loc, s.dynamic.at_p loc = true

def WellFormed (s : State) : Prop := 
  WellFormedStatic s.statics ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidSatisfiedParam s.statics s.dynamic ∧
  ValidWantspaperParam s.statics s.dynamic ∧
  ValidUnpackedParam s.statics s.dynamic ∧
  ValidCarryingParam s.statics s.dynamic ∧
  AtMostOneAt s.statics s.dynamic ∧
  PaperStatusExclusive s.statics s.dynamic ∧
  SatisfiedWantsPaperExclusive s.statics s.dynamic ∧
  ExistsOneAt s

def InitAtIsHomeBase (s : State) : Prop :=
  ∀ loc, s.dynamic.at_p loc = true ↔ s.statics.ishomebase_p loc = true

def InitWantsPaperExcludesHomeBase (s : State) : Prop :=
  ∀ loc, s.dynamic.wantspaper_p loc = true → s.statics.ishomebase_p loc = false

def InitAllPapersUnpacked (s : State) : Prop :=
  ∀ paper, s.statics.paper_t paper = true → s.dynamic.unpacked_p paper = true

def InitNobodyCarrying (s : State) : Prop :=
  ∀ paper, s.dynamic.carrying_p paper = false

def InitNoneSatisfied (s : State) : Prop :=
  ∀ loc, s.dynamic.satisfied_p loc = false

def EnoughPapersForTargets (s : State) : Prop :=
  (s.statics.objects.filter s.statics.paper_t).length ≥
  (s.statics.objects.filter s.dynamic.wantspaper_p).length

def InitSafeIsHomeOrWantsPaper (s : State) : Prop :=
  ∀ loc, s.statics.safe_p loc = true ↔
    (s.statics.ishomebase_p loc = true ∨ s.dynamic.wantspaper_p loc = true)

def WellFormedInit (s : State) : Prop := 
  WellFormed s ∧
  InitAtIsHomeBase s ∧
  InitWantsPaperExcludesHomeBase s ∧
  InitAllPapersUnpacked s ∧
  InitNobodyCarrying s ∧
  InitNoneSatisfied s ∧
  EnoughPapersForTargets s ∧
  InitSafeIsHomeOrWantsPaper s

def GoalIgnoreAt (initial : State) (g : Goal) : Prop :=
  ∀ loc, g.dynamic.at_p loc = none

def GoalIgnoreWantsPaper (initial : State) (g : Goal) : Prop :=
  ∀ loc, g.dynamic.wantspaper_p loc = none

def GoalIgnoreUnpacked (initial : State) (g : Goal) : Prop :=
  ∀ paper, g.dynamic.unpacked_p paper = none

def GoalIgnoreCarrying (initial : State) (g : Goal) : Prop :=
  ∀ paper, g.dynamic.carrying_p paper = none

def GoalSatisfiedOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ loc, g.dynamic.satisfied_p loc ≠ some false

def GoalHasSatisfiedTarget (initial : State) (g : Goal) : Prop :=
  ∃ loc, g.dynamic.satisfied_p loc = some true

def GoalSatisfiedMatchesWantsPaper (initial : State) (g : Goal) : Prop :=
  ∀ loc, g.dynamic.satisfied_p loc = some true ↔ initial.dynamic.wantspaper_p loc = true

def WellFormedGoal (initial : State) (g : Goal) : Prop := 
  WellFormedStatic initial.statics ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidSatisfiedParam initial.statics g.dynamic ∧
  ValidWantspaperParam initial.statics g.dynamic ∧
  ValidUnpackedParam initial.statics g.dynamic ∧
  ValidCarryingParam initial.statics g.dynamic ∧
  AtMostOneAt initial.statics g.dynamic ∧
  PaperStatusExclusive initial.statics g.dynamic ∧
  SatisfiedWantsPaperExclusive initial.statics g.dynamic ∧
  GoalIgnoreAt initial g ∧
  GoalIgnoreWantsPaper initial g ∧
  GoalIgnoreUnpacked initial g ∧
  GoalIgnoreCarrying initial g ∧
  GoalSatisfiedOnlyPositive initial g ∧
  GoalHasSatisfiedTarget initial g ∧
  GoalSatisfiedMatchesWantsPaper initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_loc,
    match g.dynamic.at_p var_loc with
    | none => True
    | some b => s.dynamic.at_p var_loc = b) ∧
  (∀ var_loc,
    match g.dynamic.satisfied_p var_loc with
    | none => True
    | some b => s.dynamic.satisfied_p var_loc = b) ∧
  (∀ var_loc,
    match g.dynamic.wantspaper_p var_loc with
    | none => True
    | some b => s.dynamic.wantspaper_p var_loc = b) ∧
  (∀ var_paper,
    match g.dynamic.unpacked_p var_paper with
    | none => True
    | some b => s.dynamic.unpacked_p var_paper = b) ∧
  (∀ var_paper,
    match g.dynamic.carrying_p var_paper with
    | none => True
    | some b => s.dynamic.carrying_p var_paper = b)

def pick_upPre (var_paper : Obj) (var_loc : Obj) (s : State) : Prop :=
  s.statics.paper_t var_paper = true ∧
  s.statics.loc_t var_loc = true ∧
  s.dynamic.at_p var_loc = true ∧
  s.statics.ishomebase_p var_loc = true ∧
  s.dynamic.unpacked_p var_paper = true

def movePre (var_from : Obj) (var_to : Obj) (s : State) : Prop :=
  s.statics.loc_t var_from = true ∧
  s.statics.loc_t var_to = true ∧
  s.dynamic.at_p var_from = true ∧
  s.statics.safe_p var_from = true

def deliverPre (var_paper : Obj) (var_loc : Obj) (s : State) : Prop :=
  s.statics.paper_t var_paper = true ∧
  s.statics.loc_t var_loc = true ∧
  s.dynamic.at_p var_loc = true ∧
  s.dynamic.carrying_p var_paper = true

def pick_up (var_paper : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    unpacked_p :=
      fun var_paper' =>
        if var_paper' = var_paper then
          false
        else
          s.dynamic.unpacked_p var_paper',
    carrying_p :=
      fun var_paper' =>
        if var_paper' = var_paper then
          true
        else
          s.dynamic.carrying_p var_paper'
  }
}

def move (var_from : Obj) (var_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_to' =>
        if var_to' = var_to then
          true
        else if var_to' = var_from then
          false
        else
          s.dynamic.at_p var_to'
  }
}

def deliver (var_paper : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    satisfied_p :=
      fun var_loc' =>
        if var_loc' = var_loc then
          true
        else
          s.dynamic.satisfied_p var_loc',
    wantspaper_p :=
      fun var_loc' =>
        if var_loc' = var_loc then
          false
        else
          s.dynamic.wantspaper_p var_loc',
    carrying_p :=
      fun var_paper' =>
        if var_paper' = var_paper then
          false
        else
          s.dynamic.carrying_p var_paper'
  }
}

inductive PlanAction where
  | pick_up (var_paper : Obj) (var_loc : Obj)
  | move    (var_from : Obj) (var_to : Obj)
  | deliver (var_paper : Obj) (var_loc : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .pick_up var_paper var_loc, s => pick_upPre var_paper var_loc s
  | .move    var_from var_to  , s => movePre var_from var_to s
  | .deliver var_paper var_loc, s => deliverPre var_paper var_loc s

def actionApply : PlanAction → State → State
  | .pick_up var_paper var_loc, s => pick_up var_paper var_loc s
  | .move    var_from var_to  , s => move var_from var_to s
  | .deliver var_paper var_loc, s => deliver var_paper var_loc s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Find the unique home base. The fallback is unreachable for well-formed instances.
def newspaperHome (s : State) : Obj :=
  match s.statics.objects.find? (fun loc => s.statics.ishomebase_p loc) with
  | some loc => loc
  | none => 0

-- Actions required to satisfy one target and return to the home base.
def newspaperDeliveryTrip
    (home paper target : Obj) : List PlanAction :=
  [
    PlanAction.pick_up paper home,
    PlanAction.move home target,
    PlanAction.deliver paper target,
    PlanAction.move target home
  ]

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  let home := newspaperHome s
  let papers :=
    s.statics.objects.filter s.statics.paper_t
  let targets :=
    s.statics.objects.filter s.dynamic.wantspaper_p
  (papers.zip targets).flatMap fun paperTarget =>
    newspaperDeliveryTrip home paperTarget.1 paperTarget.2

-- Part 3) Provided Lemmas

lemma runPlan_append (as bs : List PlanAction) (s : State) :
    runPlan (as ++ bs) s = runPlan bs (runPlan as s) := by
  induction as generalizing s with
  | nil => simp [runPlan]
  | cons a as ih => simp [runPlan, ih]

lemma validPlan_append (as bs : List PlanAction) (s : State) :
    ValidPlan (as ++ bs) s ↔ ValidPlan as s ∧ ValidPlan bs (runPlan as s) := by
  induction as generalizing s with
  | nil => simp [ValidPlan, runPlan]
  | cons a as ih => simp [ValidPlan, runPlan, ih, and_assoc]

lemma pick_up_statics (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).statics = s.statics := rfl

lemma move_statics (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).statics = s.statics := rfl

lemma deliver_statics (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | pick_up var_paper var_loc => exact pick_up_statics var_paper var_loc s
      | move var_from var_to      => exact move_statics var_from var_to s
      | deliver var_paper var_loc => exact deliver_statics var_paper var_loc s

-- pick_up only touches carrying_p, unpacked_p
lemma pick_up_unpacked_p_ne (var_paper var_loc : Obj) (s : State) {var_paper' : Obj} (h1 : var_paper' ≠ var_paper) :
    (pick_up var_paper var_loc s).dynamic.unpacked_p var_paper' = s.dynamic.unpacked_p var_paper' := by
  unfold pick_up
  simp [h1]

lemma pick_up_carrying_p_ne (var_paper var_loc : Obj) (s : State) {var_paper' : Obj} (h1 : var_paper' ≠ var_paper) :
    (pick_up var_paper var_loc s).dynamic.carrying_p var_paper' = s.dynamic.carrying_p var_paper' := by
  unfold pick_up
  simp [h1]

-- pick_up never touches at_p
lemma pick_up_at_p (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).dynamic.at_p = s.dynamic.at_p := rfl

-- pick_up never touches satisfied_p
lemma pick_up_satisfied_p (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).dynamic.satisfied_p = s.dynamic.satisfied_p := rfl

-- pick_up never touches wantspaper_p
lemma pick_up_wantspaper_p (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).dynamic.wantspaper_p = s.dynamic.wantspaper_p := rfl

-- move only touches at_p
lemma move_at_p_ne (var_from var_to : Obj) (s : State) {var_to' : Obj} (h1 : var_to' ≠ var_to) (h2 : var_to' ≠ var_from) :
    (move var_from var_to s).dynamic.at_p var_to' = s.dynamic.at_p var_to' := by
  unfold move
  simp [h1, h2]

-- move never touches satisfied_p
lemma move_satisfied_p (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).dynamic.satisfied_p = s.dynamic.satisfied_p := rfl

-- move never touches wantspaper_p
lemma move_wantspaper_p (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).dynamic.wantspaper_p = s.dynamic.wantspaper_p := rfl

-- move never touches unpacked_p
lemma move_unpacked_p (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).dynamic.unpacked_p = s.dynamic.unpacked_p := rfl

-- move never touches carrying_p
lemma move_carrying_p (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).dynamic.carrying_p = s.dynamic.carrying_p := rfl

-- deliver only touches satisfied_p, carrying_p, wantspaper_p
lemma deliver_satisfied_p_ne (var_paper var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (deliver var_paper var_loc s).dynamic.satisfied_p var_loc' = s.dynamic.satisfied_p var_loc' := by
  unfold deliver
  simp [h1]

lemma deliver_wantspaper_p_ne (var_paper var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (deliver var_paper var_loc s).dynamic.wantspaper_p var_loc' = s.dynamic.wantspaper_p var_loc' := by
  unfold deliver
  simp [h1]

lemma deliver_carrying_p_ne (var_paper var_loc : Obj) (s : State) {var_paper' : Obj} (h1 : var_paper' ≠ var_paper) :
    (deliver var_paper var_loc s).dynamic.carrying_p var_paper' = s.dynamic.carrying_p var_paper' := by
  unfold deliver
  simp [h1]

-- deliver never touches at_p
lemma deliver_at_p (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).dynamic.at_p = s.dynamic.at_p := rfl

-- deliver never touches unpacked_p
lemma deliver_unpacked_p (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).dynamic.unpacked_p = s.dynamic.unpacked_p := rfl

lemma pick_up_unpacked_p_eq1 (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).dynamic.unpacked_p var_paper = false := by
  unfold pick_up
  simp

lemma pick_up_carrying_p_eq1 (var_paper var_loc : Obj) (s : State) :
    (pick_up var_paper var_loc s).dynamic.carrying_p var_paper = true := by
  unfold pick_up
  simp

lemma move_at_p_eq1 (var_from var_to : Obj) (s : State) :
    (move var_from var_to s).dynamic.at_p var_to = true := by
  unfold move
  simp

lemma move_at_p_eq2 (var_from var_to : Obj) (s : State) (h1 : var_from ≠ var_to) :
    (move var_from var_to s).dynamic.at_p var_from = false := by
  unfold move
  simp [h1]

lemma deliver_satisfied_p_eq1 (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).dynamic.satisfied_p var_loc = true := by
  unfold deliver
  simp

lemma deliver_wantspaper_p_eq1 (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).dynamic.wantspaper_p var_loc = false := by
  unfold deliver
  simp

lemma deliver_carrying_p_eq1 (var_paper var_loc : Obj) (s : State) :
    (deliver var_paper var_loc s).dynamic.carrying_p var_paper = false := by
  unfold deliver
  simp

lemma truthy_false_impossible
    (h : Truthy.isTrue (false : Bool)) : False := by
  change false = true at h
  simp at h

lemma pick_up_preserves_wf
    (var_paper var_loc : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pick_upPre var_paper var_loc s) :
    WellFormed (pick_up var_paper var_loc s) := by
  unfold WellFormed at hwf ⊢
  unfold pick_upPre at hpre
  rcases hwf with
    ⟨hstatic, hat, hsat, hwants, hunpacked, hcarrying,
      hatMost, hpaperExclusive, hsatWantsExclusive, hexists⟩
  rcases hpre with
    ⟨hpaperTy, _hlocTy, _hatLoc, _hhome, _hunpackedTarget⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pick_up] using hstatic
  · simpa [ValidAtParam, pick_up] using hat
  · simpa [ValidSatisfiedParam, pick_up] using hsat
  · simpa [ValidWantspaperParam, pick_up] using hwants
  · intro paper hp
    by_cases h : paper = var_paper
    · subst paper
      exfalso
      apply truthy_false_impossible
      simpa only [pick_up_unpacked_p_eq1] using hp
    · exact hunpacked paper (by
        simpa [pick_up, h] using hp)
  · intro paper hp
    by_cases h : paper = var_paper
    · subst paper
      exact hpaperTy
    · exact hcarrying paper (by
        simpa [pick_up, h] using hp)
  · simpa [AtMostOneAt, pick_up] using hatMost
  · intro paper hp
    rcases hp with ⟨hu, hc⟩
    by_cases h : paper = var_paper
    · subst paper
      apply truthy_false_impossible
      simpa only [pick_up_unpacked_p_eq1] using hu
    · exact hpaperExclusive paper ⟨
        by simpa [pick_up, h] using hu,
        by simpa [pick_up, h] using hc
      ⟩
  · simpa [SatisfiedWantsPaperExclusive, pick_up] using
      hsatWantsExclusive
  · simpa [ExistsOneAt, pick_up] using hexists

lemma move_preserves_wf
    (var_from var_to : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hpre : movePre var_from var_to s) :
    WellFormed (move var_from var_to s) := by
  unfold WellFormed at hwf ⊢
  unfold movePre at hpre
  rcases hwf with
    ⟨hstatic, hat, hsat, hwants, hunpacked, hcarrying,
      hatMost, hpaperExclusive, hsatWantsExclusive, _hexists⟩
  rcases hpre with
    ⟨_hfromTy, htoTy, hatFrom, _hsafeFrom⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [move] using hstatic
  · intro loc hloc
    by_cases hto : loc = var_to
    · subst loc
      exact htoTy
    · by_cases hfrom : loc = var_from
      · subst loc
        exfalso
        apply truthy_false_impossible
        simpa only [move_at_p_eq2 var_from var_to s hto] using hloc
      · exact hat loc (by
          simpa [move, hto, hfrom] using hloc)
  · simpa [ValidSatisfiedParam, move] using hsat
  · simpa [ValidWantspaperParam, move] using hwants
  · simpa [ValidUnpackedParam, move] using hunpacked
  · simpa [ValidCarryingParam, move] using hcarrying
  · intro loc₁ loc₂ hloc₁ hloc₂
    have onlyAtDestination :
        ∀ loc,
          (move var_from var_to s).dynamic.at_p loc = true →
          loc = var_to := by
      intro loc hloc
      by_cases hto : loc = var_to
      · exact hto
      · by_cases hfrom : loc = var_from
        · subst loc
          simp [move, hto] at hloc
        · have hold : s.dynamic.at_p loc = true := by
            simpa [move, hto, hfrom] using hloc
          have heq : loc = var_from :=
            hatMost loc var_from hold hatFrom
          exact False.elim (hfrom heq)
    exact
      (onlyAtDestination loc₁ hloc₁).trans
        (onlyAtDestination loc₂ hloc₂).symm
  · simpa [PaperStatusExclusive, move] using hpaperExclusive
  · simpa [SatisfiedWantsPaperExclusive, move] using
      hsatWantsExclusive
  · exact ⟨var_to, move_at_p_eq1 var_from var_to s⟩

lemma deliver_preserves_wf
    (var_paper var_loc : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hpre : deliverPre var_paper var_loc s) :
    WellFormed (deliver var_paper var_loc s) := by
  unfold WellFormed at hwf ⊢
  unfold deliverPre at hpre
  rcases hwf with
    ⟨hstatic, hat, hsat, hwants, hunpacked, hcarrying,
      hatMost, hpaperExclusive, hsatWantsExclusive, hexists⟩
  rcases hpre with
    ⟨_hpaperTy, hlocTy, _hatLoc, _hcarryingTarget⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [deliver] using hstatic
  · simpa [ValidAtParam, deliver] using hat
  · intro loc hloc
    by_cases h : loc = var_loc
    · subst loc
      exact hlocTy
    · exact hsat loc (by
        simpa [deliver, h] using hloc)
  · intro loc hloc
    by_cases h : loc = var_loc
    · subst loc
      exfalso
      apply truthy_false_impossible
      simpa only [deliver_wantspaper_p_eq1] using hloc
    · exact hwants loc (by
        simpa [deliver, h] using hloc)
  · simpa [ValidUnpackedParam, deliver] using hunpacked
  · intro paper hp
    by_cases h : paper = var_paper
    · subst paper
      exfalso
      apply truthy_false_impossible
      simpa only [deliver_carrying_p_eq1] using hp
    · exact hcarrying paper (by
        simpa [deliver, h] using hp)
  · simpa [AtMostOneAt, deliver] using hatMost
  · intro paper hp
    rcases hp with ⟨hu, hc⟩
    by_cases h : paper = var_paper
    · subst paper
      apply truthy_false_impossible
      simpa only [deliver_carrying_p_eq1] using hc
    · exact hpaperExclusive paper ⟨
        by simpa [deliver] using hu,
        by simpa [deliver, h] using hc
      ⟩
  · intro loc hp
    rcases hp with ⟨hs, hw⟩
    by_cases h : loc = var_loc
    · subst loc
      apply truthy_false_impossible
      simpa only [deliver_wantspaper_p_eq1] using hw
    · exact hsatWantsExclusive loc ⟨
        by simpa [deliver, h] using hs,
        by simpa [deliver, h] using hw
      ⟩
  · simpa [ExistsOneAt, deliver] using hexists

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | pick_up var_paper var_loc =>
      exact pick_up_preserves_wf var_paper var_loc s hwf hpre
  | move var_from var_to =>
      exact move_preserves_wf var_from var_to s hwf hpre
  | deliver var_paper var_loc =>
      exact deliver_preserves_wf var_paper var_loc s hwf hpre

lemma validPlan_preserves_wf
    {plan : List PlanAction}
    {s : State}
    (hplan : ValidPlan plan s)
    (hwf : WellFormed s) :
    WellFormed (runPlan plan s) := by
  induction plan generalizing s with
  | nil =>
      simpa [runPlan]
  | cons a as ih =>
      simp only [ValidPlan] at hplan
      rcases hplan with ⟨ha, has⟩
      have hwf' :=
        action_preserves_wf (s := s) hwf ha
      exact ih has hwf'

-- Part 4) Generated Proof

-- All additional theorems and lemmas that are needed

lemma list_find?_some_true_of_exists
    {α : Type}
    (xs : List α)
    (p : α → Bool)
    (h : ∃ x, x ∈ xs ∧ p x = true) :
    ∃ x, xs.find? p = some x ∧ p x = true := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · exact ⟨a, by simp [List.find?, ha], ha⟩
      · have htail : ∃ x, x ∈ xs ∧ p x = true := by
          rcases h with ⟨x, hx, hpx⟩
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact False.elim (ha hpx)
          · exact ⟨x, hx, hpx⟩
        rcases ih htail with ⟨x, hfind, hpx⟩
        exact ⟨x, by simp [List.find?, ha, hfind], hpx⟩

lemma newspaperHome_is_homebase
    (s : State)
    (hstatic : WellFormedStatic s.statics) :
    s.statics.ishomebase_p (newspaperHome s) = true := by
  unfold WellFormedStatic at hstatic
  rcases hstatic with
    ⟨_, hvalidHome, _, htypes, hunique, _, _⟩
  unfold UniqueHomeBase at hunique
  rcases hunique with ⟨home, hhome, _⟩

  have hhomeLoc : s.statics.loc_t home = true :=
    hvalidHome home hhome
  have hhomeMem : home ∈ s.statics.objects :=
    htypes.1 home hhomeLoc

  obtain ⟨found, hfind, hfound⟩ :=
    list_find?_some_true_of_exists
      s.statics.objects
      s.statics.ishomebase_p
      ⟨home, hhomeMem, hhome⟩

  simpa [newspaperHome, hfind] using hfound

def newspaperDeliveryPlan
    (home : Obj)
    (papers targets : List Obj) : List PlanAction :=
  (papers.zip targets).flatMap fun paperTarget =>
    newspaperDeliveryTrip home paperTarget.1 paperTarget.2

lemma newspaperDeliveryPlan_cons
    (home paper target : Obj)
    (papers targets : List Obj) :
    newspaperDeliveryPlan home (paper :: papers) (target :: targets) =
      newspaperDeliveryTrip home paper target ++
        newspaperDeliveryPlan home papers targets := by
  rfl

lemma newspaperDeliveryTrip_valid
    (home paper target : Obj)
    (s : State)
    (hpaper : s.statics.paper_t paper = true)
    (hhomeLoc : s.statics.loc_t home = true)
    (htargetLoc : s.statics.loc_t target = true)
    (hatHome : s.dynamic.at_p home = true)
    (hhomeBase : s.statics.ishomebase_p home = true)
    (hunpacked : s.dynamic.unpacked_p paper = true)
    (hhomeSafe : s.statics.safe_p home = true)
    (htargetSafe : s.statics.safe_p target = true) :
    ValidPlan (newspaperDeliveryTrip home paper target) s := by
  simp [newspaperDeliveryTrip, ValidPlan, actionPre, actionApply,
    pick_upPre, movePre, deliverPre, pick_up, move, deliver,
    hpaper, hhomeLoc, htargetLoc, hatHome, hhomeBase,
    hunpacked, hhomeSafe, htargetSafe]

lemma newspaperDeliveryTrip_at_home
    (home paper target : Obj)
    (s : State) :
    (runPlan (newspaperDeliveryTrip home paper target) s).dynamic.at_p home =
      true := by
  simp [newspaperDeliveryTrip, runPlan, actionApply, pick_up, move, deliver]

lemma newspaperDeliveryTrip_satisfies_target
    (home paper target : Obj)
    (s : State) :
    (runPlan (newspaperDeliveryTrip home paper target) s).dynamic.satisfied_p
        target = true := by
  simp [newspaperDeliveryTrip, runPlan, actionApply, pick_up, move, deliver]

lemma newspaperDeliveryTrip_satisfied_p_ne
    (home paper target : Obj)
    (s : State)
    {loc : Obj}
    (h : loc ≠ target) :
    (runPlan (newspaperDeliveryTrip home paper target) s).dynamic.satisfied_p
        loc = s.dynamic.satisfied_p loc := by
  simp [newspaperDeliveryTrip, runPlan, actionApply, pick_up, move, deliver, h]

lemma newspaperDeliveryTrip_unpacked_p_ne
    (home paper target : Obj)
    (s : State)
    {otherPaper : Obj}
    (h : otherPaper ≠ paper) :
    (runPlan (newspaperDeliveryTrip home paper target) s).dynamic.unpacked_p
        otherPaper = s.dynamic.unpacked_p otherPaper := by
  simp [newspaperDeliveryTrip, runPlan, actionApply, pick_up, move, deliver, h]

lemma newspaperDeliveryPlan_correct_aux
    (home : Obj)
    (papers targets : List Obj)
    (s : State)
    (hhomeLoc : s.statics.loc_t home = true)
    (hhomeBase : s.statics.ishomebase_p home = true)
    (hhomeSafe : s.statics.safe_p home = true)
    (hatHome : s.dynamic.at_p home = true)
    (hpapersNodup : papers.Nodup)
    (htargetsNodup : targets.Nodup)
    (hlength : targets.length ≤ papers.length)
    (hpapersType :
      ∀ paper, paper ∈ papers → s.statics.paper_t paper = true)
    (hpapersUnpacked :
      ∀ paper, paper ∈ papers → s.dynamic.unpacked_p paper = true)
    (htargetsType :
      ∀ target, target ∈ targets → s.statics.loc_t target = true)
    (htargetsSafe :
      ∀ target, target ∈ targets → s.statics.safe_p target = true) :
    ValidPlan (newspaperDeliveryPlan home papers targets) s ∧
    (∀ target, target ∈ targets →
      (runPlan (newspaperDeliveryPlan home papers targets) s).dynamic.satisfied_p
        target = true) ∧
    (∀ loc, loc ∉ targets →
      (runPlan (newspaperDeliveryPlan home papers targets) s).dynamic.satisfied_p
        loc = s.dynamic.satisfied_p loc) := by
  induction papers generalizing targets s with
  | nil =>
      cases targets with
      | nil =>
          simp [newspaperDeliveryPlan, ValidPlan, runPlan]
      | cons target targets =>
          simp at hlength
  | cons paper papers ih =>
      cases targets with
      | nil =>
          simp [newspaperDeliveryPlan, ValidPlan, runPlan]
      | cons target targets =>
          have hpNodupParts := List.nodup_cons.mp hpapersNodup
          have htNodupParts := List.nodup_cons.mp htargetsNodup
          have hpaperNotMem : paper ∉ papers := hpNodupParts.1
          have hpapersNodup' : papers.Nodup := hpNodupParts.2
          have htargetNotMem : target ∉ targets := htNodupParts.1
          have htargetsNodup' : targets.Nodup := htNodupParts.2

          have hlengthSucc :
              Nat.succ targets.length ≤ Nat.succ papers.length := by
            simpa only [List.length_cons] using hlength
          have hlength' : targets.length ≤ papers.length :=
            Nat.le_of_succ_le_succ hlengthSucc

          have hpaperType : s.statics.paper_t paper = true :=
            hpapersType paper (by simp)
          have hpaperUnpacked : s.dynamic.unpacked_p paper = true :=
            hpapersUnpacked paper (by simp)
          have htargetType : s.statics.loc_t target = true :=
            htargetsType target (by simp)
          have htargetSafe : s.statics.safe_p target = true :=
            htargetsSafe target (by simp)

          have htrip :
              ValidPlan (newspaperDeliveryTrip home paper target) s :=
            newspaperDeliveryTrip_valid
              home paper target s
              hpaperType hhomeLoc htargetType hatHome hhomeBase
              hpaperUnpacked hhomeSafe htargetSafe

          let s' :=
            runPlan (newspaperDeliveryTrip home paper target) s

          have hhomeLoc' : s'.statics.loc_t home = true := by
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.loc_t
                  home = true
            rw [runPlan_statics]
            exact hhomeLoc

          have hhomeBase' : s'.statics.ishomebase_p home = true := by
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.ishomebase_p
                  home = true
            rw [runPlan_statics]
            exact hhomeBase

          have hhomeSafe' : s'.statics.safe_p home = true := by
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.safe_p
                  home = true
            rw [runPlan_statics]
            exact hhomeSafe

          have hatHome' : s'.dynamic.at_p home = true := by
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).dynamic.at_p
                  home = true
            exact newspaperDeliveryTrip_at_home home paper target s

          have hpapersType' :
              ∀ otherPaper, otherPaper ∈ papers →
                s'.statics.paper_t otherPaper = true := by
            intro otherPaper hmem
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.paper_t
                  otherPaper = true
            rw [runPlan_statics]
            exact hpapersType otherPaper (by simp [hmem])

          have hpapersUnpacked' :
              ∀ otherPaper, otherPaper ∈ papers →
                s'.dynamic.unpacked_p otherPaper = true := by
            intro otherPaper hmem
            have hne : otherPaper ≠ paper := by
              intro heq
              subst otherPaper
              exact hpaperNotMem hmem
            calc
              s'.dynamic.unpacked_p otherPaper =
                  s.dynamic.unpacked_p otherPaper := by
                    change
                      (runPlan
                        (newspaperDeliveryTrip home paper target)
                        s).dynamic.unpacked_p otherPaper =
                          s.dynamic.unpacked_p otherPaper
                    exact newspaperDeliveryTrip_unpacked_p_ne
                      home paper target s hne
              _ = true :=
                hpapersUnpacked otherPaper (by simp [hmem])

          have htargetsType' :
              ∀ otherTarget, otherTarget ∈ targets →
                s'.statics.loc_t otherTarget = true := by
            intro otherTarget hmem
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.loc_t
                  otherTarget = true
            rw [runPlan_statics]
            exact htargetsType otherTarget (by simp [hmem])

          have htargetsSafe' :
              ∀ otherTarget, otherTarget ∈ targets →
                s'.statics.safe_p otherTarget = true := by
            intro otherTarget hmem
            change
              (runPlan
                (newspaperDeliveryTrip home paper target) s).statics.safe_p
                  otherTarget = true
            rw [runPlan_statics]
            exact htargetsSafe otherTarget (by simp [hmem])

          have htail :=
            ih
              (targets := targets)
              (s := s')
              hhomeLoc'
              hhomeBase'
              hhomeSafe'
              hatHome'
              hpapersNodup'
              htargetsNodup'
              hlength'
              hpapersType'
              hpapersUnpacked'
              htargetsType'
              htargetsSafe'

          rcases htail with
            ⟨hvalidTail, hsatisfiedTail, hframeTail⟩

          rw [newspaperDeliveryPlan_cons]
          rw [validPlan_append, runPlan_append]

          refine ⟨⟨htrip, ?_⟩, ?_, ?_⟩
          · exact hvalidTail
          · intro loc hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with heq | hmem
            · subst loc
              calc
                (runPlan
                    (newspaperDeliveryPlan home papers targets)
                    (runPlan
                      (newspaperDeliveryTrip home paper target)
                      s)).dynamic.satisfied_p target =
                    s'.dynamic.satisfied_p target := by
                      exact hframeTail target htargetNotMem
                _ = true := by
                  change
                    (runPlan
                      (newspaperDeliveryTrip home paper target)
                      s).dynamic.satisfied_p target = true
                  exact newspaperDeliveryTrip_satisfies_target
                    home paper target s
            · exact hsatisfiedTail loc hmem
          · intro loc hnotMem
            have hlocNe : loc ≠ target := by
              intro heq
              apply hnotMem
              simp [heq]
            have hlocNotTail : loc ∉ targets := by
              intro hmem
              apply hnotMem
              simp [hmem]
            calc
              (runPlan
                  (newspaperDeliveryPlan home papers targets)
                  (runPlan
                    (newspaperDeliveryTrip home paper target)
                    s)).dynamic.satisfied_p loc =
                  s'.dynamic.satisfied_p loc :=
                    hframeTail loc hlocNotTail
              _ = s.dynamic.satisfied_p loc := by
                change
                  (runPlan
                    (newspaperDeliveryTrip home paper target)
                    s).dynamic.satisfied_p loc =
                      s.dynamic.satisfied_p loc
                exact newspaperDeliveryTrip_satisfied_p_ne
                  home paper target s hlocNe


-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  let home : Obj := newspaperHome s
  let papers : List Obj :=
    s.statics.objects.filter s.statics.paper_t
  let targets : List Obj :=
    s.statics.objects.filter s.dynamic.wantspaper_p

  have hhomeBase : s.statics.ishomebase_p home = true := by
    simpa [home] using newspaperHome_is_homebase s hstatic

  unfold WellFormedStatic at hstatic
  rcases hstatic with
    ⟨hobjectsUnique, hvalidHome, _, htypes, _, hhomeSafeStatic, _⟩

  have hobjectsNodup : s.statics.objects.Nodup := by
    simpa [ObjectsUnique] using hobjectsUnique

  have htypeFacts :
      (∀ x, s.statics.loc_t x = true → x ∈ s.statics.objects) ∧
      (∀ x, s.statics.paper_t x = true → x ∈ s.statics.objects) ∧
      (∀ x, s.statics.loc_t x = true →
        s.statics.paper_t x = false) := by
    simpa [ValidTypeHierarchy] using htypes

  have hhomeLoc : s.statics.loc_t home = true :=
    hvalidHome home hhomeBase

  have hhomeSafe : s.statics.safe_p home = true :=
    hhomeSafeStatic home hhomeBase

  unfold WellFormedInit at hinit
  rcases hinit with
    ⟨hwf, hinitAt, _, hallUnpacked, _, _, henough,
      hsafeCharacterization⟩

  unfold WellFormed at hwf
  rcases hwf with
    ⟨_, _, _, hvalidWants, _, _, _, _, _, _⟩

  have hinitAt' :
      ∀ loc, s.dynamic.at_p loc = true ↔
        s.statics.ishomebase_p loc = true := by
    exact hinitAt

  have hallUnpacked' :
      ∀ paper, s.statics.paper_t paper = true →
        s.dynamic.unpacked_p paper = true := by
    exact hallUnpacked

  have hsafeCharacterization' :
      ∀ loc, s.statics.safe_p loc = true ↔
        (s.statics.ishomebase_p loc = true ∨
          s.dynamic.wantspaper_p loc = true) := by
    exact hsafeCharacterization

  have hvalidWants' :
      ∀ loc, s.dynamic.wantspaper_p loc = true →
        s.statics.loc_t loc = true := by
    intro loc h
    apply hvalidWants loc
    change s.dynamic.wantspaper_p loc = true
    exact h

  have hatHome : s.dynamic.at_p home = true :=
    (hinitAt' home).2 hhomeBase

  have hpapersNodup : papers.Nodup := by
    dsimp [papers]
    exact hobjectsNodup.filter _

  have htargetsNodup : targets.Nodup := by
    dsimp [targets]
    exact hobjectsNodup.filter _

  have hlength : targets.length ≤ papers.length := by
    simpa [EnoughPapersForTargets, papers, targets] using henough

  have hpapersType :
      ∀ paper, paper ∈ papers →
        s.statics.paper_t paper = true := by
    intro paper hmem
    have hmem' :
        paper ∈ s.statics.objects.filter s.statics.paper_t := by
      simpa [papers] using hmem
    exact (List.mem_filter.mp hmem').2

  have hpapersUnpacked :
      ∀ paper, paper ∈ papers →
        s.dynamic.unpacked_p paper = true := by
    intro paper hmem
    exact hallUnpacked' paper (hpapersType paper hmem)

  have htargetsWantPaper :
      ∀ target, target ∈ targets →
        s.dynamic.wantspaper_p target = true := by
    intro target hmem
    have hmem' :
        target ∈
          s.statics.objects.filter s.dynamic.wantspaper_p := by
      simpa [targets] using hmem
    exact (List.mem_filter.mp hmem').2

  have htargetsType :
      ∀ target, target ∈ targets →
        s.statics.loc_t target = true := by
    intro target hmem
    exact hvalidWants' target (htargetsWantPaper target hmem)

  have htargetsSafe :
      ∀ target, target ∈ targets →
        s.statics.safe_p target = true := by
    intro target hmem
    exact
      (hsafeCharacterization' target).2
        (Or.inr (htargetsWantPaper target hmem))

  have hplanResult :=
    newspaperDeliveryPlan_correct_aux
      home papers targets s
      hhomeLoc
      hhomeBase
      hhomeSafe
      hatHome
      hpapersNodup
      htargetsNodup
      hlength
      hpapersType
      hpapersUnpacked
      htargetsType
      htargetsSafe

  rcases hplanResult with
    ⟨hvalidPlan, hsatisfiedTargets, _⟩

  have hsolve :
      solve s g = newspaperDeliveryPlan home papers targets := by
    rfl

  rw [hsolve]

  unfold WellFormedGoal at hgoal
  rcases hgoal with
    ⟨_, _, _, _, _, _, _, _, _,
      hignoreAt, hignoreWants, hignoreUnpacked, hignoreCarrying,
      hsatisfiedPositive, _, hsatisfiedMatches⟩

  refine ⟨hvalidPlan, ?_⟩
  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro loc
    simp [hignoreAt loc]
  · intro loc
    cases hvalue : g.dynamic.satisfied_p loc with
    | none =>
        simp [hvalue]
    | some value =>
        cases value with
        | false =>
            exfalso
            exact hsatisfiedPositive loc hvalue
        | true =>
            have hwants :
                s.dynamic.wantspaper_p loc = true :=
              (hsatisfiedMatches loc).1 hvalue
            have hlocType : s.statics.loc_t loc = true :=
              hvalidWants' loc hwants
            have hlocObject : loc ∈ s.statics.objects :=
              htypeFacts.1 loc hlocType
            have hlocTarget : loc ∈ targets := by
              dsimp [targets]
              exact List.mem_filter.mpr ⟨hlocObject, hwants⟩
            simpa [hvalue] using hsatisfiedTargets loc hlocTarget
  · intro loc
    simp [hignoreWants loc]
  · intro paper
    simp [hignoreUnpacked paper]
  · intro paper
    simp [hignoreCarrying paper]

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)
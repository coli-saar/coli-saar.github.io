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
  link_p : Obj → Obj → Bool
  location_t : Obj → Bool
  locatable_t : Obj → Bool
  man_t : Obj → Bool
  nut_t : Obj → Bool
  spanner_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_p : Obj → Obj → α
  carrying_p : Obj → Obj → α
  useable_p : Obj → α
  tightened_p : Obj → α
  loose_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidLinkParam (s : StaticState) : Prop :=
  ∀ var_l1 var_l2, s.link_p var_l1 var_l2 = true → s.location_t var_l1 = true ∧ s.location_t var_l2 = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.location_t x = true → x ∈ s.objects) ∧
  (∀ x, s.locatable_t x = true → x ∈ s.objects) ∧
  (∀ x, s.man_t x = true → s.locatable_t x = true) ∧
  (∀ x, s.nut_t x = true → s.locatable_t x = true) ∧
  (∀ x, s.spanner_t x = true → s.locatable_t x = true) ∧
  (∀ x, s.location_t x = true → s.locatable_t x = false) ∧
  (∀ x, s.location_t x = true → s.man_t x = false) ∧
  (∀ x, s.location_t x = true → s.nut_t x = false) ∧
  (∀ x, s.location_t x = true → s.spanner_t x = false) ∧
  (∀ x, s.man_t x = true → s.nut_t x = false) ∧
  (∀ x, s.man_t x = true → s.spanner_t x = false) ∧
  (∀ x, s.nut_t x = true → s.spanner_t x = false)

def LinkFunctional (s : StaticState) : Prop :=
  ∀ l1 l2 l3, s.link_p l1 l2 = true → s.link_p l1 l3 = true → l2 = l3

def LinkInjective (s : StaticState) : Prop :=
  ∀ l1 l2 l3, s.link_p l1 l3 = true → s.link_p l2 l3 = true → l1 = l2

def LinkAcyclic (s : StaticState) : Prop :=
  ∀ l, ¬ Relation.TransGen (fun a b => s.link_p a b = true) l l

def LinkFormsSinglePath (s : StaticState) : Prop :=
  ∃ start, s.location_t start = true ∧ (∀ l, s.link_p l start = false) ∧
    ∀ l, s.location_t l = true → Relation.ReflTransGen (fun a b => s.link_p a b = true) start l

def MinNumObj (s : StaticState) : Prop :=
  (∃ m, s.man_t m = true) ∧ (∃ n, s.nut_t n = true) ∧ (∃ sp, s.spanner_t sp = true)

def AtLeastAsManySpannersAsNuts (s : StaticState) : Prop :=
  (s.objects.filter (fun x => s.nut_t x)).length ≤ (s.objects.filter (fun x => s.spanner_t x)).length

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidLinkParam s ∧
  ValidTypeHierarchy s ∧
  LinkFunctional s ∧
  LinkInjective s ∧
  LinkAcyclic s ∧
  LinkFormsSinglePath s ∧
  MinNumObj s ∧
  AtLeastAsManySpannersAsNuts s

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_m var_l, Truthy.isTrue (d.at_p var_m var_l) → s.locatable_t var_m = true ∧ s.location_t var_l = true

def ValidCarryingParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_m var_s, Truthy.isTrue (d.carrying_p var_m var_s) → s.man_t var_m = true ∧ s.spanner_t var_s = true

def ValidUseableParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_s, Truthy.isTrue (d.useable_p var_s) → s.spanner_t var_s = true

def ValidTightenedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_n, Truthy.isTrue (d.tightened_p var_n) → s.nut_t var_n = true

def ValidLooseParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_n, Truthy.isTrue (d.loose_p var_n) → s.nut_t var_n = true

def ObjectUniqueLoc {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o l1 l2, s.locatable_t o = true →
    Truthy.isTrue (d.at_p o l1) → Truthy.isTrue (d.at_p o l2) → l1 = l2

def SpannerAtXorCarried {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ sp, s.spanner_t sp = true →
    ¬ ((∃ l, Truthy.isTrue (d.at_p sp l)) ∧ (∃ m, Truthy.isTrue (d.carrying_p m sp)))

def NutTightenedLooseXor {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ n, s.nut_t n = true → ¬ (Truthy.isTrue (d.tightened_p n) ∧ Truthy.isTrue (d.loose_p n))

def SpannerUniqueCarrier {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ sp m1 m2, s.spanner_t sp = true →
    Truthy.isTrue (d.carrying_p m1 sp) → Truthy.isTrue (d.carrying_p m2 sp) → m1 = m2

def LocatableHasLocation (s : State) : Prop :=
  (∀ m, s.statics.man_t m = true → ∃ l, s.dynamic.at_p m l = true) ∧
  (∀ n, s.statics.nut_t n = true → ∃ l, s.dynamic.at_p n l = true) ∧
  (∀ sp, s.statics.spanner_t sp = true →
    (∃ l, s.dynamic.at_p sp l = true) ∨ (∃ m, s.dynamic.carrying_p m sp = true))

def NutTightenedLooseExhaustive (s : State) : Prop :=
  ∀ n, s.statics.nut_t n = true → s.dynamic.tightened_p n = true ∨ s.dynamic.loose_p n = true

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidCarryingParam s.statics s.dynamic ∧
  ValidUseableParam s.statics s.dynamic ∧
  ValidTightenedParam s.statics s.dynamic ∧
  ValidLooseParam s.statics s.dynamic ∧
  ObjectUniqueLoc s.statics s.dynamic ∧
  SpannerAtXorCarried s.statics s.dynamic ∧
  NutTightenedLooseXor s.statics s.dynamic ∧
  SpannerUniqueCarrier s.statics s.dynamic ∧
  LocatableHasLocation s ∧
  NutTightenedLooseExhaustive s

def IsPathStart (s : StaticState) (l : Obj) : Prop :=
  s.location_t l = true ∧ ∀ l', s.link_p l' l = false

def IsPathEnd (s : StaticState) (l : Obj) : Prop :=
  s.location_t l = true ∧ ∀ l', s.link_p l l' = false

def InitAllAtLocation (s : State) : Prop :=
  ∀ o, s.statics.locatable_t o = true → ∃ l, s.statics.location_t l = true ∧ s.dynamic.at_p o l = true

def InitNoSpannerCarried (s : State) : Prop :=
  ∀ m sp, s.dynamic.carrying_p m sp = false

def InitManAtStart (s : State) : Prop :=
  ∀ m start, s.statics.man_t m = true → IsPathStart s.statics start → s.dynamic.at_p m start = true

def InitNutAtEnd (s : State) : Prop :=
  ∀ n loc_end, s.statics.nut_t n = true → IsPathEnd s.statics loc_end → s.dynamic.at_p n loc_end = true

def InitNutsLoose (s : State) : Prop :=
  ∀ n, s.statics.nut_t n = true → s.dynamic.loose_p n = true

def InitSpannersUseable (s : State) : Prop :=
  ∀ sp, s.statics.spanner_t sp = true → s.dynamic.useable_p sp = true

def InitExactlyOneMan (s : State) : Prop :=
  ∃! m, s.statics.man_t m = true

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitAllAtLocation s ∧
  InitNoSpannerCarried s ∧
  InitManAtStart s ∧
  InitNutAtEnd s ∧
  InitNutsLoose s ∧
  InitSpannersUseable s ∧
  InitExactlyOneMan s

def GoalAllNutsTightened (initial : State) (g : Goal) : Prop :=
  ∀ n, initial.statics.nut_t n = true → g.dynamic.tightened_p n = some true

def GoalIgnoreAt (initial : State) (g : Goal) : Prop :=
  ∀ o l, g.dynamic.at_p o l = none

def GoalIgnoreCarrying (initial : State) (g : Goal) : Prop :=
  ∀ m sp, g.dynamic.carrying_p m sp = none

def GoalIgnoreUseable (initial : State) (g : Goal) : Prop :=
  ∀ sp, g.dynamic.useable_p sp = none

def GoalIgnoreLoose (initial : State) (g : Goal) : Prop :=
  ∀ n, g.dynamic.loose_p n = none

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidCarryingParam initial.statics g.dynamic ∧
  ValidUseableParam initial.statics g.dynamic ∧
  ValidTightenedParam initial.statics g.dynamic ∧
  ValidLooseParam initial.statics g.dynamic ∧
  ObjectUniqueLoc initial.statics g.dynamic ∧
  SpannerAtXorCarried initial.statics g.dynamic ∧
  NutTightenedLooseXor initial.statics g.dynamic ∧
  SpannerUniqueCarrier initial.statics g.dynamic ∧
  GoalAllNutsTightened initial g ∧
  GoalIgnoreAt initial g ∧
  GoalIgnoreCarrying initial g ∧
  GoalIgnoreUseable initial g ∧
  GoalIgnoreLoose initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_m var_l,
    match g.dynamic.at_p var_m var_l with
    | none => True
    | some b => s.dynamic.at_p var_m var_l = b) ∧
  (∀ var_m var_s,
    match g.dynamic.carrying_p var_m var_s with
    | none => True
    | some b => s.dynamic.carrying_p var_m var_s = b) ∧
  (∀ var_s,
    match g.dynamic.useable_p var_s with
    | none => True
    | some b => s.dynamic.useable_p var_s = b) ∧
  (∀ var_n,
    match g.dynamic.tightened_p var_n with
    | none => True
    | some b => s.dynamic.tightened_p var_n = b) ∧
  (∀ var_n,
    match g.dynamic.loose_p var_n with
    | none => True
    | some b => s.dynamic.loose_p var_n = b)

def walkPre (var_start : Obj) (var_end : Obj) (var_m : Obj) (s : State) : Prop :=
  s.statics.location_t var_start = true ∧
  s.statics.location_t var_end = true ∧
  s.statics.man_t var_m = true ∧
  s.dynamic.at_p var_m var_start = true ∧
  s.statics.link_p var_start var_end = true

def pickup_spannerPre (var_l : Obj) (var_s : Obj) (var_m : Obj) (s : State) : Prop :=
  s.statics.location_t var_l = true ∧
  s.statics.spanner_t var_s = true ∧
  s.statics.man_t var_m = true ∧
  s.dynamic.at_p var_m var_l = true ∧
  s.dynamic.at_p var_s var_l = true

def tighten_nutPre (var_l : Obj) (var_s : Obj) (var_m : Obj) (var_n : Obj) (s : State) : Prop :=
  s.statics.location_t var_l = true ∧
  s.statics.spanner_t var_s = true ∧
  s.statics.man_t var_m = true ∧
  s.statics.nut_t var_n = true ∧
  s.dynamic.at_p var_m var_l = true ∧
  s.dynamic.at_p var_n var_l = true ∧
  s.dynamic.carrying_p var_m var_s = true ∧
  s.dynamic.useable_p var_s = true ∧
  s.dynamic.loose_p var_n = true

def walk (var_start : Obj) (var_end : Obj) (var_m : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_m' var_end' =>
        if var_m' = var_m ∧ var_end' = var_end then
          true
        else if var_m' = var_m ∧ var_end' = var_start then
          false
        else
          s.dynamic.at_p var_m' var_end'
  }
}

def pickup_spanner (var_l : Obj) (var_s : Obj) (var_m : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_s' var_l' =>
        if var_s' = var_s ∧ var_l' = var_l then
          false
        else
          s.dynamic.at_p var_s' var_l',
    carrying_p :=
      fun var_m' var_s' =>
        if var_m' = var_m ∧ var_s' = var_s then
          true
        else
          s.dynamic.carrying_p var_m' var_s'
  }
}

def tighten_nut (var_l : Obj) (var_s : Obj) (var_m : Obj) (var_n : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    useable_p :=
      fun var_s' =>
        if var_s' = var_s then
          false
        else
          s.dynamic.useable_p var_s',
    tightened_p :=
      fun var_n' =>
        if var_n' = var_n then
          true
        else
          s.dynamic.tightened_p var_n',
    loose_p :=
      fun var_n' =>
        if var_n' = var_n then
          false
        else
          s.dynamic.loose_p var_n'
  }
}

inductive PlanAction where
  | walk           (var_start : Obj) (var_end : Obj) (var_m : Obj)
  | pickup_spanner (var_l : Obj) (var_s : Obj) (var_m : Obj)
  | tighten_nut    (var_l : Obj) (var_s : Obj) (var_m : Obj) (var_n : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .walk           var_start var_end var_m, s => walkPre var_start var_end var_m s
  | .pickup_spanner var_l var_s var_m      , s => pickup_spannerPre var_l var_s var_m s
  | .tighten_nut    var_l var_s var_m var_n, s => tighten_nutPre var_l var_s var_m var_n s

def actionApply : PlanAction → State → State
  | .walk           var_start var_end var_m, s => walk var_start var_end var_m s
  | .pickup_spanner var_l var_s var_m      , s => pickup_spanner var_l var_s var_m s
  | .tighten_nut    var_l var_s var_m var_n, s => tighten_nut var_l var_s var_m var_n s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def gpFindMan (s : State) : Obj :=
  match s.statics.objects.find? (fun o => s.statics.man_t o) with
  | some m => m
  | none   => 0

def gpFindPathStart (st : StaticState) : Obj :=
  match st.objects.find? (fun l =>
    st.location_t l &&
      st.objects.all (fun l' => !(st.link_p l' l))) with
  | some l => l
  | none   => 0

def gpForwardPath (st : StaticState) : Nat → Obj → List Obj
  | 0, l => [l]
  | Nat.succ fuel, l =>
      l ::
        match st.objects.find? (fun next => st.link_p l next) with
        | none      => []
        | some next => gpForwardPath st fuel next

def gpPickupsAt (s : State) (l : Obj) (m : Obj) : List PlanAction :=
  (s.statics.objects.filter (fun sp =>
    s.statics.spanner_t sp && s.dynamic.at_p sp l)).map
      (fun sp => PlanAction.pickup_spanner l sp m)

def gpTraverseFrom
    (s : State) (m : Obj) (current : Obj) :
    List Obj → List PlanAction
  | [] =>
      gpPickupsAt s current m
  | next :: rest =>
      gpPickupsAt s current m ++
        (PlanAction.walk current next m ::
          gpTraverseFrom s m next rest)

def gpTraversePath (s : State) (m : Obj) :
    List Obj → List PlanAction
  | [] => []
  | start :: rest => gpTraverseFrom s m start rest

def gpLastObj (fallback : Obj) : List Obj → Obj
  | [] => fallback
  | x :: xs => gpLastObj x xs

def gpTightenActions (l : Obj) (m : Obj) :
    List Obj → List Obj → List PlanAction
  | [], _ => []
  | _, [] => []
  | sp :: spanners, n :: nuts =>
      PlanAction.tighten_nut l sp m n ::
        gpTightenActions l m spanners nuts

def solve (s : State) (g : Goal) : List PlanAction :=
  let m := gpFindMan s
  let start := gpFindPathStart s.statics
  let path := gpForwardPath s.statics s.statics.objects.length start
  let nutLocation := gpLastObj start path
  let spanners :=
    s.statics.objects.filter (fun o => s.statics.spanner_t o)
  let nuts :=
    s.statics.objects.filter (fun o => s.statics.nut_t o)
  gpTraversePath s m path ++
    gpTightenActions nutLocation m spanners nuts

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

lemma walk_statics (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).statics = s.statics := rfl

lemma pickup_spanner_statics (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).statics = s.statics := rfl

lemma tighten_nut_statics (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | walk var_start var_end var_m        => exact walk_statics var_start var_end var_m s
      | pickup_spanner var_l var_s var_m    => exact pickup_spanner_statics var_l var_s var_m s
      | tighten_nut var_l var_s var_m var_n => exact tighten_nut_statics var_l var_s var_m var_n s

-- walk only touches at_p
lemma walk_at_p_ne_var_l (var_start var_end var_m : Obj) (s : State) {var_end' : Obj} (h1 : var_end' ≠ var_end) (h2 : var_end' ≠ var_start) :
    (walk var_start var_end var_m s).dynamic.at_p var_m var_end' = s.dynamic.at_p var_m var_end' := by
  unfold walk
  simp [h1, h2]

-- walk never touches carrying_p
lemma walk_carrying_p (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).dynamic.carrying_p = s.dynamic.carrying_p := rfl

-- walk never touches useable_p
lemma walk_useable_p (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).dynamic.useable_p = s.dynamic.useable_p := rfl

-- walk never touches tightened_p
lemma walk_tightened_p (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).dynamic.tightened_p = s.dynamic.tightened_p := rfl

-- walk never touches loose_p
lemma walk_loose_p (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).dynamic.loose_p = s.dynamic.loose_p := rfl

-- pickup_spanner only touches carrying_p, at_p
lemma pickup_spanner_at_p_ne (var_l var_s var_m : Obj) (s : State) {var_s' var_l' : Obj} (h1 : var_s' ≠ var_s) :
    (pickup_spanner var_l var_s var_m s).dynamic.at_p var_s' var_l' = s.dynamic.at_p var_s' var_l' := by
  unfold pickup_spanner
  simp [h1]

lemma pickup_spanner_at_p_ne_var_l (var_l var_s var_m : Obj) (s : State) {var_l' : Obj} (h1 : var_l' ≠ var_l) :
    (pickup_spanner var_l var_s var_m s).dynamic.at_p var_s var_l' = s.dynamic.at_p var_s var_l' := by
  unfold pickup_spanner
  simp [h1]

lemma pickup_spanner_carrying_p_ne (var_l var_s var_m : Obj) (s : State) {var_m' var_s' : Obj} (h1 : var_m' ≠ var_m) :
    (pickup_spanner var_l var_s var_m s).dynamic.carrying_p var_m' var_s' = s.dynamic.carrying_p var_m' var_s' := by
  unfold pickup_spanner
  simp [h1]

lemma pickup_spanner_carrying_p_ne_var_s (var_l var_s var_m : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (pickup_spanner var_l var_s var_m s).dynamic.carrying_p var_m var_s' = s.dynamic.carrying_p var_m var_s' := by
  unfold pickup_spanner
  simp [h1]

-- pickup_spanner never touches useable_p
lemma pickup_spanner_useable_p (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).dynamic.useable_p = s.dynamic.useable_p := rfl

-- pickup_spanner never touches tightened_p
lemma pickup_spanner_tightened_p (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).dynamic.tightened_p = s.dynamic.tightened_p := rfl

-- pickup_spanner never touches loose_p
lemma pickup_spanner_loose_p (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).dynamic.loose_p = s.dynamic.loose_p := rfl

-- tighten_nut only touches tightened_p, loose_p, useable_p
lemma tighten_nut_useable_p_ne (var_l var_s var_m var_n : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.useable_p var_s' = s.dynamic.useable_p var_s' := by
  unfold tighten_nut
  simp [h1]

lemma tighten_nut_tightened_p_ne (var_l var_s var_m var_n : Obj) (s : State) {var_n' : Obj} (h1 : var_n' ≠ var_n) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.tightened_p var_n' = s.dynamic.tightened_p var_n' := by
  unfold tighten_nut
  simp [h1]

lemma tighten_nut_loose_p_ne (var_l var_s var_m var_n : Obj) (s : State) {var_n' : Obj} (h1 : var_n' ≠ var_n) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p var_n' = s.dynamic.loose_p var_n' := by
  unfold tighten_nut
  simp [h1]

-- tighten_nut never touches at_p
lemma tighten_nut_at_p (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.at_p = s.dynamic.at_p := rfl

-- tighten_nut never touches carrying_p
lemma tighten_nut_carrying_p (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.carrying_p = s.dynamic.carrying_p := rfl

lemma walk_at_p_eq1 (var_start var_end var_m : Obj) (s : State) :
    (walk var_start var_end var_m s).dynamic.at_p var_m var_end = true := by
  unfold walk
  simp

lemma walk_at_p_eq2 (var_start var_end var_m : Obj) (s : State) (h1 : var_start ≠ var_end) :
    (walk var_start var_end var_m s).dynamic.at_p var_m var_start = false := by
  unfold walk
  simp [h1]

lemma pickup_spanner_at_p_eq1 (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).dynamic.at_p var_s var_l = false := by
  unfold pickup_spanner
  simp

lemma pickup_spanner_carrying_p_eq1 (var_l var_s var_m : Obj) (s : State) :
    (pickup_spanner var_l var_s var_m s).dynamic.carrying_p var_m var_s = true := by
  unfold pickup_spanner
  simp

lemma tighten_nut_useable_p_eq1 (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.useable_p var_s = false := by
  unfold tighten_nut
  simp

lemma tighten_nut_tightened_p_eq1 (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.tightened_p var_n = true := by
  unfold tighten_nut
  simp

lemma tighten_nut_loose_p_eq1 (var_l var_s var_m var_n : Obj) (s : State) :
    (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p var_n = false := by
  unfold tighten_nut
  simp

lemma walk_preserves_wf
    (var_start var_end var_m)
    (s : State)
    (hwf : WellFormed s)
    (hpre : walkPre var_start var_end var_m s) :
    WellFormed (walk var_start var_end var_m s) := by
  unfold WellFormed at hwf ⊢
  rcases hwf with
    ⟨hstatic, hat, hcarry, huseable, htightened, hloose,
      hunique, hspannerXor, hnutXor, huniqueCarrier, hhasLocation,
      hexhaustive⟩
  unfold walkPre at hpre
  rcases hpre with
    ⟨hStartLocation, hEndLocation, hMan, hAtStart, hLink⟩

  have hhierarchy : ValidTypeHierarchy s.statics :=
    hstatic.2.2.1
  unfold ValidTypeHierarchy at hhierarchy
  rcases hhierarchy with
    ⟨_, _, hManLocatable, _, _, _, _, _, _, hManNotNut,
      hManNotSpanner, _⟩

  have hacyclic : LinkAcyclic s.statics :=
    hstatic.2.2.2.2.2.1

  have hStartNeEnd : var_start ≠ var_end := by
    intro hEq
    subst var_end
    exact hacyclic var_start (Relation.TransGen.single hLink)

  have hMovedAtOnlyEnd :
      ∀ l,
        (walk var_start var_end var_m s).dynamic.at_p var_m l = true →
        l = var_end := by
    intro l hAt
    by_cases hEnd : l = var_end
    · exact hEnd
    · by_cases hStart : l = var_start
      · subst l
        have hFalse :
            (walk var_start var_end var_m s).dynamic.at_p
              var_m var_start = false :=
          walk_at_p_eq2 var_start var_end var_m s hStartNeEnd
        rw [hFalse] at hAt
        contradiction
      · have hOldAt : s.dynamic.at_p var_m l = true := by
          simpa [walk, hEnd, hStart] using hAt
        have hEq :=
          hunique var_m l var_start
            (hManLocatable var_m hMan) hOldAt hAtStart
        exact (hStart hEq).elim

  have hNutNeMan :
      ∀ n, s.statics.nut_t n = true → n ≠ var_m := by
    intro n hNut hEq
    subst n
    exact Bool.noConfusion
      (hNut.symm.trans (hManNotNut var_m hMan))

  have hSpannerNeMan :
      ∀ sp, s.statics.spanner_t sp = true → sp ≠ var_m := by
    intro sp hSpanner hEq
    subst sp
    exact Bool.noConfusion
      (hSpanner.symm.trans (hManNotSpanner var_m hMan))

  unfold LocatableHasLocation at hhasLocation
  rcases hhasLocation with
    ⟨hMenHaveLocation, hNutsHaveLocation, hSpannersHaveLocation⟩

  refine
    ⟨hstatic, ?_, hcarry, huseable, htightened, hloose, ?_, ?_,
      hnutXor, huniqueCarrier, ?_, hexhaustive⟩

  · unfold ValidAtParam
    intro o l hAt
    change
      (walk var_start var_end var_m s).dynamic.at_p o l = true
      at hAt
    by_cases hObject : o = var_m
    · subst o
      by_cases hEnd : l = var_end
      · subst l
        exact ⟨hManLocatable var_m hMan, hEndLocation⟩
      · by_cases hStart : l = var_start
        · subst l
          have hFalse :
              (walk var_start var_end var_m s).dynamic.at_p
                var_m var_start = false :=
            walk_at_p_eq2 var_start var_end var_m s hStartNeEnd
          rw [hFalse] at hAt
          contradiction
        · have hOldAt : s.dynamic.at_p var_m l = true := by
            simpa [walk, hEnd, hStart] using hAt
          exact hat var_m l hOldAt
    · have hOldAt : s.dynamic.at_p o l = true := by
        simpa [walk, hObject] using hAt
      exact hat o l hOldAt

  · unfold ObjectUniqueLoc
    intro o l₁ l₂ hLocatable hAt₁ hAt₂
    change
      (walk var_start var_end var_m s).dynamic.at_p o l₁ = true
      at hAt₁
    change
      (walk var_start var_end var_m s).dynamic.at_p o l₂ = true
      at hAt₂
    by_cases hObject : o = var_m
    · subst o
      exact
        (hMovedAtOnlyEnd l₁ hAt₁).trans
          (hMovedAtOnlyEnd l₂ hAt₂).symm
    · apply hunique o l₁ l₂ hLocatable
      · change s.dynamic.at_p o l₁ = true
        simpa [walk, hObject] using hAt₁
      · change s.dynamic.at_p o l₂ = true
        simpa [walk, hObject] using hAt₂

  · unfold SpannerAtXorCarried
    intro sp hSpanner hBad
    rcases hBad with
      ⟨⟨l, hAtNew⟩, ⟨carrier, hCarriedNew⟩⟩
    have hSpannerNe : sp ≠ var_m :=
      hSpannerNeMan sp hSpanner
    have hAtOld : s.dynamic.at_p sp l = true := by
      change
        (walk var_start var_end var_m s).dynamic.at_p sp l = true
        at hAtNew
      simpa [walk, hSpannerNe] using hAtNew
    change s.dynamic.carrying_p carrier sp = true at hCarriedNew
    exact
      hspannerXor sp hSpanner
        ⟨⟨l, hAtOld⟩, ⟨carrier, hCarriedNew⟩⟩

  · unfold LocatableHasLocation
    refine ⟨?_, ?_, ?_⟩
    · intro m hIsMan
      by_cases hEq : m = var_m
      · subst m
        exact
          ⟨var_end, walk_at_p_eq1 var_start var_end var_m s⟩
      · rcases hMenHaveLocation m hIsMan with ⟨l, hAt⟩
        refine ⟨l, ?_⟩
        change
          (walk var_start var_end var_m s).dynamic.at_p m l = true
        simpa [walk, hEq] using hAt
    · intro n hNut
      have hNe : n ≠ var_m := hNutNeMan n hNut
      rcases hNutsHaveLocation n hNut with ⟨l, hAt⟩
      refine ⟨l, ?_⟩
      change
        (walk var_start var_end var_m s).dynamic.at_p n l = true
      simpa [walk, hNe] using hAt
    · intro sp hSpanner
      have hNe : sp ≠ var_m :=
        hSpannerNeMan sp hSpanner
      rcases hSpannersHaveLocation sp hSpanner with hAt | hCarried
      · left
        rcases hAt with ⟨l, hAt⟩
        refine ⟨l, ?_⟩
        change
          (walk var_start var_end var_m s).dynamic.at_p sp l = true
        simpa [walk, hNe] using hAt
      · right
        exact hCarried


lemma pickup_spanner_preserves_wf
    (var_l var_s var_m)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pickup_spannerPre var_l var_s var_m s) :
    WellFormed (pickup_spanner var_l var_s var_m s) := by
  unfold WellFormed at hwf ⊢
  rcases hwf with
    ⟨hstatic, hat, hcarry, huseable, htightened, hloose,
      hunique, hspannerXor, hnutXor, huniqueCarrier, hhasLocation,
      hexhaustive⟩
  unfold pickup_spannerPre at hpre
  rcases hpre with
    ⟨hLocation, hSpanner, hMan, hManAt, hSpannerAt⟩

  have hhierarchy : ValidTypeHierarchy s.statics :=
    hstatic.2.2.1
  unfold ValidTypeHierarchy at hhierarchy
  rcases hhierarchy with
    ⟨_, _, _, _, hSpannerLocatable, _, _, _, _, _, hManNotSpanner,
      hNutNotSpanner⟩

  have hAtOldOfNew :
      ∀ o l,
        (pickup_spanner var_l var_s var_m s).dynamic.at_p o l = true →
        s.dynamic.at_p o l = true := by
    intro o l hAtNew
    by_cases ho : o = var_s
    · by_cases hl : l = var_l
      · simp [pickup_spanner, ho, hl] at hAtNew
      · simpa [pickup_spanner, ho, hl] using hAtNew
    · simpa [pickup_spanner, ho] using hAtNew

  have hNoNewAt :
      ∀ l,
        (pickup_spanner var_l var_s var_m s).dynamic.at_p var_s l =
          true →
        False := by
    intro l hAt
    by_cases hEq : l = var_l
    · subst l
      have hFalse :
          (pickup_spanner var_l var_s var_m s).dynamic.at_p
            var_s var_l = false :=
        pickup_spanner_at_p_eq1 var_l var_s var_m s
      rw [hFalse] at hAt
      contradiction
    · have hOldAt : s.dynamic.at_p var_s l = true :=
        hAtOldOfNew var_s l hAt
      have hLocationEq :=
        hunique var_s l var_l
          (hSpannerLocatable var_s hSpanner)
          hOldAt hSpannerAt
      exact hEq hLocationEq

  have hNewCarrierEq :
      ∀ m,
        (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
          m var_s = true →
        m = var_m := by
    intro m hCarried
    by_cases hEq : m = var_m
    · exact hEq
    · have hOldCarried : s.dynamic.carrying_p m var_s = true := by
        simpa [pickup_spanner, hEq] using hCarried
      exfalso
      exact
        hspannerXor var_s hSpanner
          ⟨⟨var_l, hSpannerAt⟩, ⟨m, hOldCarried⟩⟩

  have hManNeSpanner :
      ∀ m, s.statics.man_t m = true → m ≠ var_s := by
    intro m hIsMan hEq
    subst m
    exact Bool.noConfusion
      (hSpanner.symm.trans (hManNotSpanner var_s hIsMan))

  have hNutNeSpanner :
      ∀ n, s.statics.nut_t n = true → n ≠ var_s := by
    intro n hNut hEq
    subst n
    exact Bool.noConfusion
      (hSpanner.symm.trans (hNutNotSpanner var_s hNut))

  unfold LocatableHasLocation at hhasLocation
  rcases hhasLocation with
    ⟨hMenHaveLocation, hNutsHaveLocation, hSpannersHaveLocation⟩

  refine
    ⟨hstatic, ?_, ?_, huseable, htightened, hloose, ?_, ?_,
      hnutXor, ?_, ?_, hexhaustive⟩

  · unfold ValidAtParam
    intro o l hAt
    change
      (pickup_spanner var_l var_s var_m s).dynamic.at_p o l = true
      at hAt
    exact hat o l (hAtOldOfNew o l hAt)

  · unfold ValidCarryingParam
    intro m sp hCarried
    change
      (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
        m sp = true
      at hCarried
    by_cases hChanged : m = var_m ∧ sp = var_s
    · rcases hChanged with ⟨rfl, rfl⟩
      exact ⟨hMan, hSpanner⟩
    · have hOldCarried : s.dynamic.carrying_p m sp = true := by
        simpa [pickup_spanner, hChanged] using hCarried
      exact hcarry m sp hOldCarried

  · unfold ObjectUniqueLoc
    intro o l₁ l₂ hLocatable hAt₁ hAt₂
    change
      (pickup_spanner var_l var_s var_m s).dynamic.at_p o l₁ = true
      at hAt₁
    change
      (pickup_spanner var_l var_s var_m s).dynamic.at_p o l₂ = true
      at hAt₂
    exact
      hunique o l₁ l₂ hLocatable
        (hAtOldOfNew o l₁ hAt₁)
        (hAtOldOfNew o l₂ hAt₂)

  · unfold SpannerAtXorCarried
    intro sp hIsSpanner hBad
    rcases hBad with
      ⟨⟨l, hAtNew⟩, ⟨m, hCarriedNew⟩⟩
    change
      (pickup_spanner var_l var_s var_m s).dynamic.at_p sp l = true
      at hAtNew
    change
      (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
        m sp = true
      at hCarriedNew
    by_cases hEq : sp = var_s
    · subst sp
      exact hNoNewAt l hAtNew
    · have hAtOld : s.dynamic.at_p sp l = true :=
        hAtOldOfNew sp l hAtNew
      have hCarriedOld : s.dynamic.carrying_p m sp = true := by
        simpa [pickup_spanner, hEq] using hCarriedNew
      exact
        hspannerXor sp hIsSpanner
          ⟨⟨l, hAtOld⟩, ⟨m, hCarriedOld⟩⟩

  · unfold SpannerUniqueCarrier
    intro sp m₁ m₂ hIsSpanner hCarried₁ hCarried₂
    change
      (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
        m₁ sp = true
      at hCarried₁
    change
      (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
        m₂ sp = true
      at hCarried₂
    by_cases hEq : sp = var_s
    · subst sp
      exact
        (hNewCarrierEq m₁ hCarried₁).trans
          (hNewCarrierEq m₂ hCarried₂).symm
    · apply huniqueCarrier sp m₁ m₂ hIsSpanner
      · change s.dynamic.carrying_p m₁ sp = true
        simpa [pickup_spanner, hEq] using hCarried₁
      · change s.dynamic.carrying_p m₂ sp = true
        simpa [pickup_spanner, hEq] using hCarried₂

  · unfold LocatableHasLocation
    refine ⟨?_, ?_, ?_⟩
    · intro m hIsMan
      have hNe : m ≠ var_s :=
        hManNeSpanner m hIsMan
      rcases hMenHaveLocation m hIsMan with ⟨l, hAt⟩
      refine ⟨l, ?_⟩
      change
        (pickup_spanner var_l var_s var_m s).dynamic.at_p m l =
          true
      simpa [pickup_spanner, hNe] using hAt
    · intro n hNut
      have hNe : n ≠ var_s :=
        hNutNeSpanner n hNut
      rcases hNutsHaveLocation n hNut with ⟨l, hAt⟩
      refine ⟨l, ?_⟩
      change
        (pickup_spanner var_l var_s var_m s).dynamic.at_p n l =
          true
      simpa [pickup_spanner, hNe] using hAt
    · intro sp hIsSpanner
      by_cases hEq : sp = var_s
      · subst sp
        right
        exact
          ⟨var_m,
            pickup_spanner_carrying_p_eq1 var_l var_s var_m s⟩
      · rcases hSpannersHaveLocation sp hIsSpanner with hAt | hCarried
        · left
          rcases hAt with ⟨l, hAt⟩
          refine ⟨l, ?_⟩
          change
            (pickup_spanner var_l var_s var_m s).dynamic.at_p
              sp l = true
          simpa [pickup_spanner, hEq] using hAt
        · right
          rcases hCarried with ⟨m, hCarried⟩
          refine ⟨m, ?_⟩
          change
            (pickup_spanner var_l var_s var_m s).dynamic.carrying_p
              m sp = true
          simpa [pickup_spanner, hEq] using hCarried


lemma tighten_nut_preserves_wf
    (var_l var_s var_m var_n)
    (s : State)
    (hwf : WellFormed s)
    (hpre : tighten_nutPre var_l var_s var_m var_n s) :
    WellFormed (tighten_nut var_l var_s var_m var_n s) := by
  unfold WellFormed at hwf ⊢
  rcases hwf with
    ⟨hstatic, hat, hcarry, huseable, htightened, hloose,
      hunique, hspannerXor, hnutXor, huniqueCarrier, hhasLocation,
      hexhaustive⟩
  unfold tighten_nutPre at hpre
  rcases hpre with
    ⟨hLocation, hSpanner, hMan, hNut, hManAt, hNutAt,
      hCarrying, hUseable, hLoose⟩

  refine
    ⟨hstatic, hat, hcarry, ?_, ?_, ?_, hunique, hspannerXor, ?_,
      huniqueCarrier, hhasLocation, ?_⟩

  · unfold ValidUseableParam
    intro sp hUseableNew
    change
      (tighten_nut var_l var_s var_m var_n s).dynamic.useable_p sp =
        true
      at hUseableNew
    by_cases hEq : sp = var_s
    · subst sp
      have hFalse :
          (tighten_nut var_l var_s var_m var_n s).dynamic.useable_p
            var_s = false :=
        tighten_nut_useable_p_eq1 var_l var_s var_m var_n s
      rw [hFalse] at hUseableNew
      contradiction
    · have hUseableOld : s.dynamic.useable_p sp = true := by
        simpa [tighten_nut, hEq] using hUseableNew
      exact huseable sp hUseableOld

  · unfold ValidTightenedParam
    intro n hTightenedNew
    change
      (tighten_nut var_l var_s var_m var_n s).dynamic.tightened_p n =
        true
      at hTightenedNew
    by_cases hEq : n = var_n
    · subst n
      exact hNut
    · have hTightenedOld : s.dynamic.tightened_p n = true := by
        simpa [tighten_nut, hEq] using hTightenedNew
      exact htightened n hTightenedOld

  · unfold ValidLooseParam
    intro n hLooseNew
    change
      (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p n =
        true
      at hLooseNew
    by_cases hEq : n = var_n
    · subst n
      have hFalse :
          (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p
            var_n = false :=
        tighten_nut_loose_p_eq1 var_l var_s var_m var_n s
      rw [hFalse] at hLooseNew
      contradiction
    · have hLooseOld : s.dynamic.loose_p n = true := by
        simpa [tighten_nut, hEq] using hLooseNew
      exact hloose n hLooseOld

  · unfold NutTightenedLooseXor
    intro n hIsNut hBad
    rcases hBad with ⟨hTightenedNew, hLooseNew⟩
    change
      (tighten_nut var_l var_s var_m var_n s).dynamic.tightened_p n =
        true
      at hTightenedNew
    change
      (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p n =
        true
      at hLooseNew
    by_cases hEq : n = var_n
    · subst n
      have hFalse :
          (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p
            var_n = false :=
        tighten_nut_loose_p_eq1 var_l var_s var_m var_n s
      rw [hFalse] at hLooseNew
      contradiction
    · have hTightenedOld : s.dynamic.tightened_p n = true := by
        simpa [tighten_nut, hEq] using hTightenedNew
      have hLooseOld : s.dynamic.loose_p n = true := by
        simpa [tighten_nut, hEq] using hLooseNew
      exact hnutXor n hIsNut ⟨hTightenedOld, hLooseOld⟩

  · unfold NutTightenedLooseExhaustive
    intro n hIsNut
    by_cases hEq : n = var_n
    · subst n
      left
      exact
        tighten_nut_tightened_p_eq1
          var_l var_s var_m var_n s
    · rcases hexhaustive n hIsNut with hTightenedOld | hLooseOld
      · left
        change
          (tighten_nut var_l var_s var_m var_n s).dynamic.tightened_p
            n = true
        simpa [tighten_nut, hEq] using hTightenedOld
      · right
        change
          (tighten_nut var_l var_s var_m var_n s).dynamic.loose_p n =
            true
        simpa [tighten_nut, hEq] using hLooseOld

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | walk var_start var_end var_m =>
      exact walk_preserves_wf var_start var_end var_m s hwf hpre
  | pickup_spanner var_l var_s var_m =>
      exact pickup_spanner_preserves_wf var_l var_s var_m s hwf hpre
  | tighten_nut var_l var_s var_m var_n =>
      exact tighten_nut_preserves_wf var_l var_s var_m var_n s hwf hpre

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

lemma bool_and_eq_true (a b : Bool) :
    ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

lemma wf_objects_nodup {st : StaticState} (h : WellFormedStatic st) :
    st.objects.Nodup :=
  h.1

lemma wf_valid_link {st : StaticState} (h : WellFormedStatic st) :
    ValidLinkParam st :=
  h.2.1

lemma wf_type_hierarchy {st : StaticState} (h : WellFormedStatic st) :
    ValidTypeHierarchy st :=
  h.2.2.1

lemma wf_link_functional {st : StaticState} (h : WellFormedStatic st) :
    LinkFunctional st :=
  h.2.2.2.1

lemma wf_link_acyclic {st : StaticState} (h : WellFormedStatic st) :
    LinkAcyclic st :=
  h.2.2.2.2.2.1

lemma wf_single_path {st : StaticState} (h : WellFormedStatic st) :
    LinkFormsSinglePath st :=
  h.2.2.2.2.2.2.1

lemma wf_min_num_obj {st : StaticState} (h : WellFormedStatic st) :
    MinNumObj st :=
  h.2.2.2.2.2.2.2.1

lemma wf_spanner_nut_count {st : StaticState} (h : WellFormedStatic st) :
    (st.objects.filter (fun x => st.nut_t x)).length ≤
      (st.objects.filter (fun x => st.spanner_t x)).length :=
  h.2.2.2.2.2.2.2.2

lemma location_mem_objects {st : StaticState}
    (h : WellFormedStatic st) {l : Obj}
    (hl : st.location_t l = true) :
    l ∈ st.objects := by
  exact (wf_type_hierarchy h).1 l hl

lemma locatable_mem_objects {st : StaticState}
    (h : WellFormedStatic st) {o : Obj}
    (ho : st.locatable_t o = true) :
    o ∈ st.objects := by
  exact (wf_type_hierarchy h).2.1 o ho

lemma man_is_locatable {st : StaticState}
    (h : WellFormedStatic st) {m : Obj}
    (hm : st.man_t m = true) :
    st.locatable_t m = true := by
  exact (wf_type_hierarchy h).2.2.1 m hm

lemma nut_is_locatable {st : StaticState}
    (h : WellFormedStatic st) {n : Obj}
    (hn : st.nut_t n = true) :
    st.locatable_t n = true := by
  exact (wf_type_hierarchy h).2.2.2.1 n hn

lemma spanner_is_locatable {st : StaticState}
    (h : WellFormedStatic st) {sp : Obj}
    (hsp : st.spanner_t sp = true) :
    st.locatable_t sp = true := by
  exact (wf_type_hierarchy h).2.2.2.2.1 sp hsp

lemma man_ne_nut {st : StaticState}
    (h : WellFormedStatic st) {m n : Obj}
    (hm : st.man_t m = true)
    (hn : st.nut_t n = true) :
    m ≠ n := by
  intro heq
  subst n
  have hfalse :=
    (wf_type_hierarchy h).2.2.2.2.2.2.2.2.2.1 m hm
  simp [hn] at hfalse

lemma man_ne_spanner {st : StaticState}
    (h : WellFormedStatic st) {m sp : Obj}
    (hm : st.man_t m = true)
    (hsp : st.spanner_t sp = true) :
    m ≠ sp := by
  intro heq
  subst sp
  have hfalse :=
    (wf_type_hierarchy h).2.2.2.2.2.2.2.2.2.2.1 m hm
  simp [hsp] at hfalse

lemma nut_ne_spanner {st : StaticState}
    (h : WellFormedStatic st) {n sp : Obj}
    (hn : st.nut_t n = true)
    (hsp : st.spanner_t sp = true) :
    n ≠ sp := by
  intro heq
  subst sp
  have hfalse :=
    (wf_type_hierarchy h).2.2.2.2.2.2.2.2.2.2.2 n hn
  simp [hsp] at hfalse

lemma find?_some_of_mem_true
    {α : Type} (xs : List α) (p : α → Bool) {x : α}
    (hx : x ∈ xs) (hp : p x = true) :
    ∃ y, xs.find? p = some y := by
  induction xs with
  | nil =>
      simp at hx
  | cons a xs ih =>
      by_cases ha : p a = true
      · exact ⟨a, by simp [List.find?, ha]⟩
      · have haFalse : p a = false :=
          Bool.eq_false_of_not_eq_true ha
        rcases List.mem_cons.mp hx with hax | hx
        · subst x
          exact False.elim (ha hp)
        · rcases ih hx with ⟨y, hy⟩
          exact ⟨y, by simpa [List.find?, haFalse] using hy⟩

lemma find?_predicate
    {α : Type} {xs : List α} {p : α → Bool} {y : α}
    (h : xs.find? p = some y) :
    p y = true := by
  induction xs with
  | nil =>
      simp [List.find?] at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · have hred : some a = some y := by
          simpa [List.find?, ha] using h
        have hay : a = y := Option.some.inj hred
        subst y
        exact ha
      · have haFalse : p a = false :=
          Bool.eq_false_of_not_eq_true ha
        apply ih
        simpa [List.find?, haFalse] using h

lemma find?_none_not_true
    {α : Type} {xs : List α} {p : α → Bool}
    (h : xs.find? p = none) :
    ∀ x ∈ xs, p x ≠ true := by
  intro x hx hpx
  rcases find?_some_of_mem_true xs p hx hpx with ⟨y, hy⟩
  rw [h] at hy
  contradiction

lemma find_link_eq
    {st : StaticState}
    (hwf : WellFormedStatic st)
    {x y : Obj}
    (hxy : st.link_p x y = true) :
    st.objects.find? (fun z => st.link_p x z) = some y := by
  have hyLoc : st.location_t y = true :=
    (wf_valid_link hwf x y hxy).2
  have hyMem : y ∈ st.objects :=
    location_mem_objects hwf hyLoc
  rcases find?_some_of_mem_true
      st.objects (fun z => st.link_p x z) hyMem hxy with
    ⟨z, hz⟩
  have hzLink : st.link_p x z = true :=
    find?_predicate (p := fun z => st.link_p x z) hz
  have hzy : z = y :=
    wf_link_functional hwf x z y hzLink hxy
  subst z
  exact hz

lemma gpFindMan_spec
    (s : State)
    (hwf : WellFormedStatic s.statics) :
    s.statics.man_t (gpFindMan s) = true := by
  rcases wf_min_num_obj hwf with ⟨⟨m, hm⟩, _, _⟩
  have hmMem : m ∈ s.statics.objects :=
    locatable_mem_objects hwf (man_is_locatable hwf hm)
  rcases find?_some_of_mem_true
      s.statics.objects s.statics.man_t hmMem hm with
    ⟨m', hm'⟩
  unfold gpFindMan
  rw [hm']
  exact find?_predicate (p := s.statics.man_t) hm'

lemma reflTransGen_eq_of_no_incoming
    {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b)
    (hno : ∀ x, ¬ r x b) :
    a = b := by
  cases h with
  | refl =>
      rfl
  | tail h₁ h₂ =>
      exact False.elim (hno _ h₂)

lemma gpFindPathStart_spec
    (st : StaticState)
    (hwf : WellFormedStatic st) :
    IsPathStart st (gpFindPathStart st) := by
  rcases wf_single_path hwf with
    ⟨start, hStartLoc, hNoIncoming, hReach⟩

  have hAll :
      st.objects.all (fun l' => !(st.link_p l' start)) = true := by
    apply List.all_eq_true.mpr
    intro l hl
    simp [hNoIncoming l]

  have hPred :
      (st.location_t start &&
        st.objects.all (fun l' => !(st.link_p l' start))) = true := by
    exact (bool_and_eq_true _ _).mpr ⟨hStartLoc, hAll⟩

  have hStartMem : start ∈ st.objects :=
    location_mem_objects hwf hStartLoc

  rcases find?_some_of_mem_true
      st.objects
      (fun l =>
        st.location_t l &&
          st.objects.all (fun l' => !(st.link_p l' l)))
      hStartMem hPred with
    ⟨found, hfound⟩

  have hFoundPred :
      (st.location_t found &&
        st.objects.all (fun l' => !(st.link_p l' found))) = true :=
    find?_predicate
      (p := fun l =>
        st.location_t l &&
          st.objects.all (fun l' => !(st.link_p l' l)))
      hfound

  have hFoundLoc : st.location_t found = true :=
    ((bool_and_eq_true _ _).mp hFoundPred).1

  have hFoundAll :
      st.objects.all (fun l' => !(st.link_p l' found)) = true :=
    ((bool_and_eq_true _ _).mp hFoundPred).2

  have hFoundNoIncoming : ∀ l', st.link_p l' found = false := by
    intro l'
    by_cases hlMem : l' ∈ st.objects
    · have hneg :
          (!(st.link_p l' found)) = true :=
        (List.all_eq_true.mp hFoundAll) l' hlMem
      cases hval : st.link_p l' found with
      | false =>
          rfl
      | true =>
          simp [hval] at hneg
    · by_cases hlink : st.link_p l' found = true
      · have hlLoc : st.location_t l' = true :=
          (wf_valid_link hwf l' found hlink).1
        exact False.elim
          (hlMem (location_mem_objects hwf hlLoc))
      · exact Bool.eq_false_of_not_eq_true hlink

  unfold gpFindPathStart
  rw [hfound]
  exact ⟨hFoundLoc, hFoundNoIncoming⟩

lemma gpFindPathStart_reaches
    (st : StaticState)
    (hwf : WellFormedStatic st)
    {l : Obj}
    (hl : st.location_t l = true) :
    Relation.ReflTransGen
      (fun a b => st.link_p a b = true)
      (gpFindPathStart st) l := by
  rcases wf_single_path hwf with
    ⟨start, hStartLoc, hNoIncoming, hReach⟩
  have hFound := gpFindPathStart_spec st hwf
  have hReachFound := hReach (gpFindPathStart st) hFound.1
  have hEq : start = gpFindPathStart st := by
    apply reflTransGen_eq_of_no_incoming hReachFound
    intro x hx
    have hfalse := hFound.2 x
    simp [hx] at hfalse
  simpa [hEq] using hReach l hl

lemma edge_reflTransGen_to_reflTransGen
    {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : r a b)
    (hbc : Relation.ReflTransGen r b c) :
    Relation.ReflTransGen r a c := by
  induction hbc with
  | refl =>
      exact Relation.ReflTransGen.tail
        Relation.ReflTransGen.refl hab
  | tail hcd hde ih =>
      exact Relation.ReflTransGen.tail ih hde

lemma edge_reflTransGen_to_transGen
    {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : r a b)
    (hbc : Relation.ReflTransGen r b c) :
    Relation.TransGen r a c := by
  induction hbc with
  | refl =>
      exact Relation.TransGen.single hab
  | tail hcd hde ih =>
      exact Relation.TransGen.tail ih hde

lemma gpForwardPath_cons
    (st : StaticState) (fuel : Nat) (start : Obj) :
    ∃ tail, gpForwardPath st fuel start = start :: tail := by
  cases fuel with
  | zero =>
      exact ⟨[], rfl⟩
  | succ fuel =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          exact ⟨[], by simp [gpForwardPath, hfind]⟩
      | some next =>
          exact ⟨gpForwardPath st fuel next,
            by simp [gpForwardPath, hfind]⟩

lemma gpForwardPath_head_mem
    (st : StaticState) (fuel : Nat) (start : Obj) :
    start ∈ gpForwardPath st fuel start := by
  rcases gpForwardPath_cons st fuel start with ⟨tail, htail⟩
  rw [htail]
  simp

lemma gpForwardPath_nonempty
    (st : StaticState) (fuel : Nat) (start : Obj) :
    gpForwardPath st fuel start ≠ [] := by
  rcases gpForwardPath_cons st fuel start with ⟨tail, htail⟩
  rw [htail]
  simp

lemma gpForwardPath_reachable
    (st : StaticState)
    (fuel : Nat)
    {start x : Obj}
    (hx : x ∈ gpForwardPath st fuel start) :
    Relation.ReflTransGen
      (fun a b => st.link_p a b = true) start x := by
  induction fuel generalizing start x with
  | zero =>
      simp [gpForwardPath] at hx
      subst x
      exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          simp [gpForwardPath, hfind] at hx
          subst x
          exact Relation.ReflTransGen.refl
      | some next =>
          have hlink : st.link_p start next = true :=
            find?_predicate
              (p := fun next => st.link_p start next) hfind
          have hx' :
              x = start ∨ x ∈ gpForwardPath st fuel next := by
            simpa [gpForwardPath, hfind] using hx
          rcases hx' with rfl | hx'
          · exact Relation.ReflTransGen.refl
          · exact edge_reflTransGen_to_reflTransGen
              hlink (ih hx')

lemma gpForwardPath_locations
    (st : StaticState)
    (hwf : WellFormedStatic st)
    (fuel : Nat)
    {start : Obj}
    (hstart : st.location_t start = true) :
    ∀ x ∈ gpForwardPath st fuel start,
      st.location_t x = true := by
  induction fuel generalizing start with
  | zero =>
      intro x hx
      simp [gpForwardPath] at hx
      subst x
      exact hstart
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          intro x hx
          simp [gpForwardPath, hfind] at hx
          subst x
          exact hstart
      | some next =>
          have hlink : st.link_p start next = true :=
            find?_predicate
              (p := fun next => st.link_p start next) hfind
          have hnext : st.location_t next = true :=
            (wf_valid_link hwf start next hlink).2
          intro x hx
          have hx' :
              x = start ∨ x ∈ gpForwardPath st fuel next := by
            simpa [gpForwardPath, hfind] using hx
          rcases hx' with rfl | hx'
          · exact hstart
          · exact ih hnext x hx'

lemma gpForwardPath_objects
    (st : StaticState)
    (hwf : WellFormedStatic st)
    (fuel : Nat)
    {start : Obj}
    (hstart : st.location_t start = true) :
    ∀ x ∈ gpForwardPath st fuel start,
      x ∈ st.objects := by
  intro x hx
  exact location_mem_objects hwf
    (gpForwardPath_locations st hwf fuel hstart x hx)

lemma gpForwardPath_nodup
    (st : StaticState)
    (hwf : WellFormedStatic st)
    (fuel : Nat)
    {start : Obj}
    (hstart : st.location_t start = true) :
    (gpForwardPath st fuel start).Nodup := by
  induction fuel generalizing start with
  | zero =>
      simp [gpForwardPath]
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          simp [gpForwardPath, hfind]
      | some next =>
          have hlink : st.link_p start next = true :=
            find?_predicate
              (p := fun next => st.link_p start next) hfind
          have hnext : st.location_t next = true :=
            (wf_valid_link hwf start next hlink).2
          have hnot :
              start ∉ gpForwardPath st fuel next := by
            intro hmem
            have hreach :=
              gpForwardPath_reachable st fuel hmem
            have hcycle :
                Relation.TransGen
                  (fun a b => st.link_p a b = true)
                  start start :=
              edge_reflTransGen_to_transGen hlink hreach
            exact wf_link_acyclic hwf start hcycle
          have htailNodup := ih hnext
          simpa [gpForwardPath, hfind] using
            List.nodup_cons.mpr ⟨hnot, htailNodup⟩

lemma nodup_length_le_of_subset
    {α : Type} [DecidableEq α]
    {xs ys : List α}
    (hxs : xs.Nodup)
    (hys : ys.Nodup)
    (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  rw [← List.toFinset_card_of_nodup hxs]
  rw [← List.toFinset_card_of_nodup hys]
  apply Finset.card_le_card
  intro x hx
  simp only [List.mem_toFinset] at hx ⊢
  exact hsub x hx

lemma gpForwardPath_closed_or_full
    (st : StaticState)
    (hwf : WellFormedStatic st)
    (fuel : Nat)
    {start x y : Obj}
    (hx : x ∈ gpForwardPath st fuel start)
    (hxy : st.link_p x y = true) :
    y ∈ gpForwardPath st fuel start ∨
      (gpForwardPath st fuel start).length = fuel + 1 := by
  induction fuel generalizing start x y with
  | zero =>
      right
      simp [gpForwardPath]
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          have hxStart : x = start := by
            simpa [gpForwardPath, hfind] using hx
          subst x
          have hsome := find_link_eq hwf hxy
          rw [hfind] at hsome
          contradiction
      | some next =>
          have hx' :
              x = start ∨ x ∈ gpForwardPath st fuel next := by
            simpa [gpForwardPath, hfind] using hx
          rcases hx' with hxs | hx'
          · subst x
            have hsame := find_link_eq hwf hxy
            rw [hfind] at hsame
            have hnexty : next = y := Option.some.inj hsame
            subst y
            left
            simp only [gpForwardPath, hfind, List.mem_cons]
            exact Or.inr (gpForwardPath_head_mem st fuel next)
          · rcases ih hx' hxy with hy | hfull
            · left
              simp only [gpForwardPath, hfind, List.mem_cons]
              exact Or.inr hy
            · right
              simp [gpForwardPath, hfind, hfull, Nat.add_assoc]

lemma gpForwardPath_closed
    (st : StaticState)
    (hwf : WellFormedStatic st)
    {start x y : Obj}
    (hstart : st.location_t start = true)
    (hx : x ∈ gpForwardPath st st.objects.length start)
    (hxy : st.link_p x y = true) :
    y ∈ gpForwardPath st st.objects.length start := by
  rcases gpForwardPath_closed_or_full
      st hwf st.objects.length hx hxy with
    hy | hfull
  · exact hy
  · have hlen :
        (gpForwardPath st st.objects.length start).length ≤
          st.objects.length := by
      apply nodup_length_le_of_subset
      · exact gpForwardPath_nodup st hwf _ hstart
      · exact wf_objects_nodup hwf
      · exact gpForwardPath_objects st hwf _ hstart
    omega

lemma gpForwardPath_contains_reachable
    (st : StaticState)
    (hwf : WellFormedStatic st)
    {start x : Obj}
    (hstart : st.location_t start = true)
    (hreach :
      Relation.ReflTransGen
        (fun a b => st.link_p a b = true) start x) :
    x ∈ gpForwardPath st st.objects.length start := by
  induction hreach with
  | refl =>
      exact gpForwardPath_head_mem st st.objects.length start
  | tail hab hbc ih =>
      exact gpForwardPath_closed st hwf hstart ih hbc

lemma gpForwardPath_contains_all_locations
    (st : StaticState)
    (hwf : WellFormedStatic st)
    {l : Obj}
    (hl : st.location_t l = true) :
    l ∈ gpForwardPath st st.objects.length (gpFindPathStart st) := by
  exact gpForwardPath_contains_reachable
    st hwf (gpFindPathStart_spec st hwf).1
    (gpFindPathStart_reaches st hwf hl)

lemma gpLastObj_mem
    (fallback : Obj) {xs : List Obj}
    (hxs : xs ≠ []) :
    gpLastObj fallback xs ∈ xs := by
  induction xs generalizing fallback with
  | nil =>
      contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [gpLastObj]
      | cons y ys =>
          have hmem : gpLastObj x (y :: ys) ∈ y :: ys :=
            ih x (by simp)
          exact List.mem_cons_of_mem x hmem

lemma gpLastObj_fallback_irrel
    (a b : Obj) {xs : List Obj}
    (hxs : xs ≠ []) :
    gpLastObj a xs = gpLastObj b xs := by
  cases xs with
  | nil =>
      contradiction
  | cons x xs =>
      rfl

lemma gpForwardPath_last_stop_or_full
    (st : StaticState)
    (hwf : WellFormedStatic st)
    (fuel : Nat)
    (start : Obj) :
    (∀ y,
      st.link_p
        (gpLastObj start (gpForwardPath st fuel start)) y = false) ∨
    (gpForwardPath st fuel start).length = fuel + 1 := by
  induction fuel generalizing start with
  | zero =>
      right
      simp [gpForwardPath]
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          left
          intro y
          by_cases hlink : st.link_p start y = true
          · have hyLoc : st.location_t y = true :=
              (wf_valid_link hwf start y hlink).2
            have hyMem := location_mem_objects hwf hyLoc
            exact False.elim
              ((find?_none_not_true hfind y hyMem) hlink)
          · simpa [gpForwardPath, hfind, gpLastObj] using
              Bool.eq_false_of_not_eq_true hlink
      | some next =>
          rcases ih next with hstop | hfull
          · left
            intro y
            have hnonempty :
                gpForwardPath st fuel next ≠ [] :=
              gpForwardPath_nonempty st fuel next
            have hlast :
                gpLastObj start
                    (gpForwardPath st (Nat.succ fuel) start) =
                  gpLastObj next
                    (gpForwardPath st fuel next) := by
              simp only [gpForwardPath, hfind, gpLastObj]
              exact gpLastObj_fallback_irrel
                start next hnonempty
            rw [hlast]
            exact hstop y
          · right
            simp [gpForwardPath, hfind, hfull, Nat.add_assoc]

lemma gpForwardPath_last_is_end
    (st : StaticState)
    (hwf : WellFormedStatic st) :
    IsPathEnd st
      (gpLastObj
        (gpFindPathStart st)
        (gpForwardPath st st.objects.length
          (gpFindPathStart st))) := by
  let start := gpFindPathStart st
  let path := gpForwardPath st st.objects.length start
  have hstart : st.location_t start = true := by
    exact (gpFindPathStart_spec st hwf).1
  have hpathNe : path ≠ [] := by
    exact gpForwardPath_nonempty st st.objects.length start
  have hlastMem : gpLastObj start path ∈ path :=
    gpLastObj_mem start hpathNe
  have hlastLoc : st.location_t (gpLastObj start path) = true :=
    gpForwardPath_locations st hwf _ hstart _ hlastMem
  have hlen :
      path.length ≤ st.objects.length := by
    apply nodup_length_le_of_subset
    · exact gpForwardPath_nodup st hwf _ hstart
    · exact wf_objects_nodup hwf
    · exact gpForwardPath_objects st hwf _ hstart
  have hstop : ∀ y, st.link_p (gpLastObj start path) y = false := by
    rcases gpForwardPath_last_stop_or_full
        st hwf st.objects.length start with hstop | hfull
    · simpa [path] using hstop
    · have hfull' : path.length = st.objects.length + 1 := by
        simpa [path] using hfull
      omega
  exact ⟨hlastLoc, hstop⟩

lemma run_pickup_map_at_not_mem
    (l m o l' : Obj) (xs : List Obj) (q : State)
    (ho : o ∉ xs) :
    (runPlan
      (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
      q).dynamic.at_p o l' =
      q.dynamic.at_p o l' := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons sp xs ih =>
      have hne : o ≠ sp := by
        intro heq
        apply ho
        simp [heq]
      have htail : o ∉ xs := by
        intro hx
        exact ho (List.mem_cons_of_mem sp hx)
      simp only [List.map_cons, runPlan, actionApply]
      rw [ih _ htail]
      exact pickup_spanner_at_p_ne l sp m q hne

lemma run_pickup_map_carrying_true
    (l m sp : Obj) (xs : List Obj) (q : State)
    (h : q.dynamic.carrying_p m sp = true) :
    (runPlan
      (xs.map (fun x => PlanAction.pickup_spanner l x m))
      q).dynamic.carrying_p m sp = true := by
  induction xs generalizing q with
  | nil =>
      exact h
  | cons x xs ih =>
      simp only [List.map_cons, runPlan, actionApply]
      apply ih
      by_cases heq : x = sp
      · subst x
        exact pickup_spanner_carrying_p_eq1 l sp m q
      · have hne : sp ≠ x := Ne.symm heq
        rw [pickup_spanner_carrying_p_ne_var_s
          l x m q hne]
        exact h

lemma run_pickup_map_carrying_of_mem
    (l m sp : Obj) (xs : List Obj) (q : State)
    (hsp : sp ∈ xs) :
    (runPlan
      (xs.map (fun x => PlanAction.pickup_spanner l x m))
      q).dynamic.carrying_p m sp = true := by
  induction xs generalizing q with
  | nil =>
      simp at hsp
  | cons x xs ih =>
      simp only [List.map_cons, runPlan, actionApply]
      rcases List.mem_cons.mp hsp with hEq | htail
      · subst x
        apply run_pickup_map_carrying_true
        exact pickup_spanner_carrying_p_eq1 l sp m q
      · exact ih _ htail

lemma run_pickup_map_useable
    (l m : Obj) (xs : List Obj) (q : State) :
    (runPlan
      (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
      q).dynamic.useable_p =
      q.dynamic.useable_p := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons sp xs ih =>
      simp only [List.map_cons, runPlan, actionApply]
      rw [ih]
      rfl

lemma run_pickup_map_tightened
    (l m : Obj) (xs : List Obj) (q : State) :
    (runPlan
      (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
      q).dynamic.tightened_p =
      q.dynamic.tightened_p := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons sp xs ih =>
      simp only [List.map_cons, runPlan, actionApply]
      rw [ih]
      rfl

lemma run_pickup_map_loose
    (l m : Obj) (xs : List Obj) (q : State) :
    (runPlan
      (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
      q).dynamic.loose_p =
      q.dynamic.loose_p := by
  induction xs generalizing q with
  | nil =>
      rfl
  | cons sp xs ih =>
      simp only [List.map_cons, runPlan, actionApply]
      rw [ih]
      rfl

lemma valid_pickup_map
    (l m : Obj) (xs : List Obj) (q : State)
    (hLoc : q.statics.location_t l = true)
    (hMan : q.statics.man_t m = true)
    (hManAt : q.dynamic.at_p m l = true)
    (hTypes : ∀ sp ∈ xs, q.statics.spanner_t sp = true)
    (hAt : ∀ sp ∈ xs, q.dynamic.at_p sp l = true)
    (hNe : ∀ sp ∈ xs, m ≠ sp)
    (hNodup : xs.Nodup) :
    ValidPlan
      (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
      q := by
  induction xs generalizing q with
  | nil =>
      trivial
  | cons sp xs ih =>
      have hspType : q.statics.spanner_t sp = true :=
        hTypes sp (by simp)
      have hspAt : q.dynamic.at_p sp l = true :=
        hAt sp (by simp)
      have hmsp : m ≠ sp :=
        hNe sp (by simp)
      have hnd := List.nodup_cons.mp hNodup
      have hpre : pickup_spannerPre l sp m q :=
        ⟨hLoc, hspType, hMan, hManAt, hspAt⟩
      refine ⟨hpre, ?_⟩
      change ValidPlan
        (xs.map (fun sp => PlanAction.pickup_spanner l sp m))
        (pickup_spanner l sp m q)
      apply ih
      · exact hLoc
      · exact hMan
      · rw [pickup_spanner_at_p_ne l sp m q hmsp]
        exact hManAt
      · intro x hx
        exact hTypes x (List.mem_cons_of_mem sp hx)
      · intro x hx
        have hxne : x ≠ sp := by
          intro heq
          subst x
          exact hnd.1 hx
        rw [pickup_spanner_at_p_ne l sp m q hxne]
        exact hAt x (List.mem_cons_of_mem sp hx)
      · intro x hx
        exact hNe x (List.mem_cons_of_mem sp hx)
      · exact hnd.2

def GPLinked (st : StaticState) : List Obj → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs =>
      st.link_p x y = true ∧ GPLinked st (y :: xs)

lemma gpForwardPath_linked
    (st : StaticState) (fuel : Nat) (start : Obj) :
    GPLinked st (gpForwardPath st fuel start) := by
  induction fuel generalizing start with
  | zero =>
      simp [gpForwardPath, GPLinked]
  | succ fuel ih =>
      cases hfind :
          st.objects.find? (fun next => st.link_p start next) with
      | none =>
          simp [gpForwardPath, hfind, GPLinked]
      | some next =>
          have hlink : st.link_p start next = true :=
            find?_predicate
              (p := fun next => st.link_p start next) hfind
          rcases gpForwardPath_cons st fuel next with
            ⟨tail, htail⟩
          rw [show
            gpForwardPath st (Nat.succ fuel) start =
              start :: gpForwardPath st fuel next by
                simp [gpForwardPath, hfind]]
          rw [htail]
          exact ⟨hlink, by simpa [htail] using ih next⟩

lemma gpTraverseFrom_valid
    (orig q : State)
    (hwf : WellFormedStatic orig.statics)
    (m current : Obj)
    (rest : List Obj)
    (hStatics : q.statics = orig.statics)
    (hNodup : (current :: rest).Nodup)
    (hLocations :
      ∀ l ∈ current :: rest,
        orig.statics.location_t l = true)
    (hLinked : GPLinked orig.statics (current :: rest))
    (hMan : orig.statics.man_t m = true)
    (hManAt : q.dynamic.at_p m current = true)
    (hRemaining :
      ∀ sp l,
        orig.statics.spanner_t sp = true →
        l ∈ current :: rest →
        orig.dynamic.at_p sp l = true →
        q.dynamic.at_p sp l = true)
    (hUnique : ObjectUniqueLoc orig.statics orig.dynamic) :
    ValidPlan (gpTraverseFrom orig m current rest) q := by
  induction rest generalizing current q with
  | nil =>
      let xs :=
        orig.statics.objects.filter (fun sp =>
          orig.statics.spanner_t sp &&
            orig.dynamic.at_p sp current)
      have hLocOrig : orig.statics.location_t current = true :=
        hLocations current (by simp)
      have hLocQ : q.statics.location_t current = true := by
        rw [hStatics]
        exact hLocOrig
      have hManQ : q.statics.man_t m = true := by
        rw [hStatics]
        exact hMan
      have hTypes :
          ∀ sp ∈ xs, q.statics.spanner_t sp = true := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        have hs := ((bool_and_eq_true _ _).mp hp).1
        rw [hStatics]
        exact hs
      have hAt :
          ∀ sp ∈ xs, q.dynamic.at_p sp current = true := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        have hparts := (bool_and_eq_true _ _).mp hp
        exact hRemaining sp current hparts.1 (by simp) hparts.2
      have hNe :
          ∀ sp ∈ xs, m ≠ sp := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        exact man_ne_spanner hwf hMan
          (((bool_and_eq_true _ _).mp hp).1)
      have hxsNodup : xs.Nodup :=
        (wf_objects_nodup hwf).filter _
      simpa [gpTraverseFrom, gpPickupsAt, xs] using
        valid_pickup_map current m xs q
          hLocQ hManQ hManAt hTypes hAt hNe hxsNodup
  | cons next tail ih =>
      let xs :=
        orig.statics.objects.filter (fun sp =>
          orig.statics.spanner_t sp &&
            orig.dynamic.at_p sp current)
      let q₁ :=
        runPlan
          (xs.map (fun sp =>
            PlanAction.pickup_spanner current sp m)) q
      let q₂ := walk current next m q₁

      have hLocCurrent :
          orig.statics.location_t current = true :=
        hLocations current (by simp)
      have hLocNext :
          orig.statics.location_t next = true :=
        hLocations next (by simp)
      have hLink :
          orig.statics.link_p current next = true :=
        hLinked.1
      have hTailLinked :
          GPLinked orig.statics (next :: tail) :=
        hLinked.2
      have hNodupParts := List.nodup_cons.mp hNodup
      have hTailNodup : (next :: tail).Nodup :=
        hNodupParts.2

      have hTypes :
          ∀ sp ∈ xs, q.statics.spanner_t sp = true := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        rw [hStatics]
        exact ((bool_and_eq_true _ _).mp hp).1

      have hAt :
          ∀ sp ∈ xs, q.dynamic.at_p sp current = true := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        have hparts := (bool_and_eq_true _ _).mp hp
        exact hRemaining sp current hparts.1 (by simp) hparts.2

      have hNe :
          ∀ sp ∈ xs, m ≠ sp := by
        intro sp hsp
        have hp := (List.mem_filter.mp hsp).2
        exact man_ne_spanner hwf hMan
          (((bool_and_eq_true _ _).mp hp).1)

      have hmNotMem : m ∉ xs := by
        intro hm
        exact (hNe m hm) rfl

      have hBatch :
          ValidPlan
            (xs.map (fun sp =>
              PlanAction.pickup_spanner current sp m)) q := by
        apply valid_pickup_map
        · rw [hStatics]
          exact hLocCurrent
        · rw [hStatics]
          exact hMan
        · exact hManAt
        · exact hTypes
        · exact hAt
        · exact hNe
        · exact (wf_objects_nodup hwf).filter _

      have hManAtQ₁ : q₁.dynamic.at_p m current = true := by
        have heq :=
          run_pickup_map_at_not_mem
            current m m current xs q hmNotMem
        rw [heq]
        exact hManAt

      have hQ₁Statics : q₁.statics = orig.statics := by
        calc
          q₁.statics = q.statics := by
            exact runPlan_statics _ q
          _ = orig.statics := hStatics

      have hWalkPre : walkPre current next m q₁ := by
        refine ⟨?_, ?_, ?_, hManAtQ₁, ?_⟩
        · rw [hQ₁Statics]
          exact hLocCurrent
        · rw [hQ₁Statics]
          exact hLocNext
        · rw [hQ₁Statics]
          exact hMan
        · rw [hQ₁Statics]
          exact hLink

      have hQ₂Statics : q₂.statics = orig.statics := by
        change (walk current next m q₁).statics = orig.statics
        rw [walk_statics]
        exact hQ₁Statics

      have hRemainingTail :
          ∀ sp l,
            orig.statics.spanner_t sp = true →
            l ∈ next :: tail →
            orig.dynamic.at_p sp l = true →
            q₂.dynamic.at_p sp l = true := by
        intro sp l hsp hl hOrigAt
        have hspNeM : sp ≠ m :=
          (man_ne_spanner hwf hMan hsp).symm
        have hspNotMem : sp ∉ xs := by
          intro hmem
          have hp := (List.mem_filter.mp hmem).2
          have hAtCurrent :=
            ((bool_and_eq_true _ _).mp hp).2
          have hEq :=
            hUnique sp current l
              (spanner_is_locatable hwf hsp)
              hAtCurrent hOrigAt
          subst l
          exact hNodupParts.1 hl
        have hQAt : q.dynamic.at_p sp l = true :=
          hRemaining sp l hsp
            (List.mem_cons_of_mem current hl) hOrigAt
        have hQ₁At : q₁.dynamic.at_p sp l = true := by
          have heq :=
            run_pickup_map_at_not_mem
              current m sp l xs q hspNotMem
          rw [heq]
          exact hQAt
        change (walk current next m q₁).dynamic.at_p sp l = true
        simpa [walk, hspNeM] using hQ₁At

      have hRecursive :
          ValidPlan (gpTraverseFrom orig m next tail) q₂ := by
        apply ih
        · exact hQ₂Statics
        · exact hTailNodup
        · intro l hl
          exact hLocations l
            (List.mem_cons_of_mem current hl)
        · exact hTailLinked
        · exact walk_at_p_eq1 current next m q₁
        · exact hRemainingTail

      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [validPlan_append]
      constructor
      · simpa [gpPickupsAt, xs] using hBatch
      · change
          walkPre current next m q₁ ∧
            ValidPlan (gpTraverseFrom orig m next tail) q₂
        exact ⟨hWalkPre, hRecursive⟩

lemma gpTraverseFrom_preserves_useable
    (orig q : State) (m current : Obj) (rest : List Obj) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.useable_p =
      q.dynamic.useable_p := by
  induction rest generalizing current q with
  | nil =>
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_useable current m
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current)) q
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply]
      calc
        (runPlan
          (gpTraverseFrom orig m next tail)
          (walk current next m
            (runPlan (gpPickupsAt orig current m) q))).dynamic.useable_p =
            (walk current next m
              (runPlan (gpPickupsAt orig current m) q)).dynamic.useable_p :=
          ih _ _
        _ =
            (runPlan (gpPickupsAt orig current m) q).dynamic.useable_p :=
          rfl
        _ = q.dynamic.useable_p := by
          simpa [gpPickupsAt] using
            run_pickup_map_useable current m
              (orig.statics.objects.filter (fun sp =>
                orig.statics.spanner_t sp &&
                  orig.dynamic.at_p sp current)) q

lemma gpTraverseFrom_preserves_tightened
    (orig q : State) (m current : Obj) (rest : List Obj) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.tightened_p =
      q.dynamic.tightened_p := by
  induction rest generalizing current q with
  | nil =>
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_tightened current m
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current)) q
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply]
      calc
        (runPlan
          (gpTraverseFrom orig m next tail)
          (walk current next m
            (runPlan (gpPickupsAt orig current m) q))).dynamic.tightened_p =
            (walk current next m
              (runPlan (gpPickupsAt orig current m) q)).dynamic.tightened_p :=
          ih _ _
        _ =
            (runPlan (gpPickupsAt orig current m) q).dynamic.tightened_p :=
          rfl
        _ = q.dynamic.tightened_p := by
          simpa [gpPickupsAt] using
            run_pickup_map_tightened current m
              (orig.statics.objects.filter (fun sp =>
                orig.statics.spanner_t sp &&
                  orig.dynamic.at_p sp current)) q

lemma gpTraverseFrom_preserves_loose
    (orig q : State) (m current : Obj) (rest : List Obj) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.loose_p =
      q.dynamic.loose_p := by
  induction rest generalizing current q with
  | nil =>
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_loose current m
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current)) q
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply]
      calc
        (runPlan
          (gpTraverseFrom orig m next tail)
          (walk current next m
            (runPlan (gpPickupsAt orig current m) q))).dynamic.loose_p =
            (walk current next m
              (runPlan (gpPickupsAt orig current m) q)).dynamic.loose_p :=
          ih _ _
        _ =
            (runPlan (gpPickupsAt orig current m) q).dynamic.loose_p :=
          rfl
        _ = q.dynamic.loose_p := by
          simpa [gpPickupsAt] using
            run_pickup_map_loose current m
              (orig.statics.objects.filter (fun sp =>
                orig.statics.spanner_t sp &&
                  orig.dynamic.at_p sp current)) q

lemma gpTraverseFrom_preserves_carrying_true
    (orig q : State) (m current sp : Obj) (rest : List Obj)
    (h : q.dynamic.carrying_p m sp = true) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.carrying_p
      m sp = true := by
  induction rest generalizing current q with
  | nil =>
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_carrying_true current m sp
          (orig.statics.objects.filter (fun x =>
            orig.statics.spanner_t x &&
              orig.dynamic.at_p x current)) q h
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply]
      apply ih
      change
        (runPlan (gpPickupsAt orig current m) q).dynamic.carrying_p
          m sp = true
      simpa [gpPickupsAt] using
        run_pickup_map_carrying_true current m sp
          (orig.statics.objects.filter (fun x =>
            orig.statics.spanner_t x &&
              orig.dynamic.at_p x current)) q h

lemma gpTraverseFrom_carries_spanner
    (orig q : State)
    (hwf : WellFormedStatic orig.statics)
    (m current sp : Obj) (rest : List Obj)
    (hsp : orig.statics.spanner_t sp = true)
    (hVisited :
      ∃ l, l ∈ current :: rest ∧
        orig.dynamic.at_p sp l = true) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.carrying_p
      m sp = true := by
  induction rest generalizing current q with
  | nil =>
      rcases hVisited with ⟨l, hl, hat⟩
      have hlEq : l = current := by
        simpa using hl
      have hatCurrent : orig.dynamic.at_p sp current = true := by
        simpa [hlEq] using hat
      have hmem :
          sp ∈ orig.statics.objects.filter (fun x =>
            orig.statics.spanner_t x &&
              orig.dynamic.at_p x current) := by
        apply List.mem_filter.mpr
        constructor
        · exact locatable_mem_objects hwf
            (spanner_is_locatable hwf hsp)
        · exact (bool_and_eq_true _ _).mpr
            ⟨hsp, hatCurrent⟩
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_carrying_of_mem current m sp
          (orig.statics.objects.filter (fun x =>
            orig.statics.spanner_t x &&
              orig.dynamic.at_p x current)) q hmem
  | cons next tail ih =>
      rcases hVisited with ⟨l, hl, hat⟩
      rcases List.mem_cons.mp hl with hlEq | hlTail
      · have hatCurrent : orig.dynamic.at_p sp current = true := by
          simpa [hlEq] using hat
        have hmem :
            sp ∈ orig.statics.objects.filter (fun x =>
              orig.statics.spanner_t x &&
                orig.dynamic.at_p x current) := by
          apply List.mem_filter.mpr
          constructor
          · exact locatable_mem_objects hwf
              (spanner_is_locatable hwf hsp)
          · exact (bool_and_eq_true _ _).mpr
              ⟨hsp, hatCurrent⟩
        rw [show
          gpTraverseFrom orig m current (next :: tail) =
            gpPickupsAt orig current m ++
              PlanAction.walk current next m ::
                gpTraverseFrom orig m next tail by rfl]
        rw [runPlan_append]
        simp only [runPlan, actionApply]
        apply gpTraverseFrom_preserves_carrying_true
        change
          (runPlan (gpPickupsAt orig current m) q).dynamic.carrying_p
            m sp = true
        simpa [gpPickupsAt] using
          run_pickup_map_carrying_of_mem current m sp
            (orig.statics.objects.filter (fun x =>
              orig.statics.spanner_t x &&
                orig.dynamic.at_p x current)) q hmem
      · rw [show
          gpTraverseFrom orig m current (next :: tail) =
            gpPickupsAt orig current m ++
              PlanAction.walk current next m ::
                gpTraverseFrom orig m next tail by rfl]
        rw [runPlan_append]
        simp only [runPlan, actionApply]
        apply ih
        exact ⟨l, hlTail, hat⟩

lemma gpTraverseFrom_man_at_last
    (orig q : State)
    (hwf : WellFormedStatic orig.statics)
    (m current : Obj) (rest : List Obj)
    (hMan : orig.statics.man_t m = true)
    (hManAt : q.dynamic.at_p m current = true) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.at_p
      m (gpLastObj current (current :: rest)) = true := by
  induction rest generalizing current q with
  | nil =>
      have hmNot :
          m ∉ orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current) := by
        intro hm
        have hp := (List.mem_filter.mp hm).2
        exact
          (man_ne_spanner hwf hMan
            (((bool_and_eq_true _ _).mp hp).1)) rfl
      have heq :=
        run_pickup_map_at_not_mem
          current m m current
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current))
          q hmNot
      simpa [gpTraverseFrom, gpPickupsAt, gpLastObj] using
        (heq.trans hManAt)
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply, gpLastObj]
      exact ih _ _
        (walk_at_p_eq1 current next m
          (runPlan (gpPickupsAt orig current m) q))

lemma gpTraverseFrom_preserves_nut_at
    (orig q : State)
    (hwf : WellFormedStatic orig.statics)
    (m current n l : Obj) (rest : List Obj)
    (hMan : orig.statics.man_t m = true)
    (hNut : orig.statics.nut_t n = true) :
    (runPlan (gpTraverseFrom orig m current rest) q).dynamic.at_p n l =
      q.dynamic.at_p n l := by
  induction rest generalizing current q with
  | nil =>
      have hnNot :
          n ∉ orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current) := by
        intro hnMem
        have hp := (List.mem_filter.mp hnMem).2
        exact
          (nut_ne_spanner hwf hNut
            (((bool_and_eq_true _ _).mp hp).1)) rfl
      simpa [gpTraverseFrom, gpPickupsAt] using
        run_pickup_map_at_not_mem
          current m n l
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current))
          q hnNot
  | cons next tail ih =>
      rw [show
        gpTraverseFrom orig m current (next :: tail) =
          gpPickupsAt orig current m ++
            PlanAction.walk current next m ::
              gpTraverseFrom orig m next tail by rfl]
      rw [runPlan_append]
      simp only [runPlan, actionApply]
      rw [ih]
      have hnm : n ≠ m :=
        (man_ne_nut hwf hMan hNut).symm
      have hnNot :
          n ∉ orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current) := by
        intro hnMem
        have hp := (List.mem_filter.mp hnMem).2
        exact
          (nut_ne_spanner hwf hNut
            (((bool_and_eq_true _ _).mp hp).1)) rfl
      change
        (walk current next m
          (runPlan (gpPickupsAt orig current m) q)).dynamic.at_p n l =
          q.dynamic.at_p n l
      have hwalk :
          (walk current next m
            (runPlan (gpPickupsAt orig current m) q)).dynamic.at_p n l =
            (runPlan (gpPickupsAt orig current m) q).dynamic.at_p n l := by
        simp [walk, hnm]
      rw [hwalk]
      simpa [gpPickupsAt] using
        run_pickup_map_at_not_mem
          current m n l
          (orig.statics.objects.filter (fun sp =>
            orig.statics.spanner_t sp &&
              orig.dynamic.at_p sp current))
          q hnNot

lemma gpTightenActions_preserves_tightened_of_not_mem
    (l m n : Obj) (spanners nuts : List Obj) (q : State)
    (hn : n ∉ nuts) :
    (runPlan
      (gpTightenActions l m spanners nuts)
      q).dynamic.tightened_p n =
      q.dynamic.tightened_p n := by
  induction nuts generalizing spanners q with
  | nil =>
      cases spanners <;> rfl
  | cons n' nuts ih =>
      cases spanners with
      | nil =>
          rfl
      | cons sp spanners =>
          have hne : n ≠ n' := by
            intro heq
            apply hn
            simp [heq]
          have htail : n ∉ nuts := by
            intro hmem
            exact hn (List.mem_cons_of_mem n' hmem)
          simp only [gpTightenActions, runPlan, actionApply]
          rw [ih _ _ htail]
          exact tighten_nut_tightened_p_ne
            l sp m n' q hne

lemma gpTightenActions_valid_and_tightens
    (q : State)
    (l m : Obj)
    (spanners nuts : List Obj)
    (hLength : nuts.length ≤ spanners.length)
    (hSpNodup : spanners.Nodup)
    (hNutNodup : nuts.Nodup)
    (hLoc : q.statics.location_t l = true)
    (hMan : q.statics.man_t m = true)
    (hManAt : q.dynamic.at_p m l = true)
    (hSpType : ∀ sp ∈ spanners, q.statics.spanner_t sp = true)
    (hSpCarry : ∀ sp ∈ spanners,
      q.dynamic.carrying_p m sp = true)
    (hSpUseable : ∀ sp ∈ spanners,
      q.dynamic.useable_p sp = true)
    (hNutType : ∀ n ∈ nuts, q.statics.nut_t n = true)
    (hNutAt : ∀ n ∈ nuts, q.dynamic.at_p n l = true)
    (hNutLoose : ∀ n ∈ nuts, q.dynamic.loose_p n = true) :
    ValidPlan (gpTightenActions l m spanners nuts) q ∧
      ∀ n ∈ nuts,
        (runPlan
          (gpTightenActions l m spanners nuts)
          q).dynamic.tightened_p n = true := by
  induction nuts generalizing spanners q with
  | nil =>
      constructor
      · cases spanners <;> trivial
      · simp
  | cons n nuts ih =>
      cases spanners with
      | nil =>
          simp at hLength
      | cons sp spanners =>
          have hSpNd := List.nodup_cons.mp hSpNodup
          have hNutNd := List.nodup_cons.mp hNutNodup
          have hpre : tighten_nutPre l sp m n q :=
            ⟨hLoc,
              hSpType sp (by simp),
              hMan,
              hNutType n (by simp),
              hManAt,
              hNutAt n (by simp),
              hSpCarry sp (by simp),
              hSpUseable sp (by simp),
              hNutLoose n (by simp)⟩

          have hrec :
              ValidPlan
                  (gpTightenActions l m spanners nuts)
                  (tighten_nut l sp m n q) ∧
                ∀ n' ∈ nuts,
                  (runPlan
                    (gpTightenActions l m spanners nuts)
                    (tighten_nut l sp m n q)).dynamic.tightened_p n' =
                    true := by
            apply ih
            · simpa using hLength
            · exact hSpNd.2
            · exact hNutNd.2
            · exact hLoc
            · exact hMan
            · exact hManAt
            · intro sp' hmem
              exact hSpType sp'
                (List.mem_cons_of_mem sp hmem)
            · intro sp' hmem
              change q.dynamic.carrying_p m sp' = true
              exact hSpCarry sp'
                (List.mem_cons_of_mem sp hmem)
            · intro sp' hmem
              have hne : sp' ≠ sp := by
                intro heq
                subst sp'
                exact hSpNd.1 hmem
              rw [tighten_nut_useable_p_ne
                l sp m n q hne]
              exact hSpUseable sp'
                (List.mem_cons_of_mem sp hmem)
            · intro n' hmem
              exact hNutType n'
                (List.mem_cons_of_mem n hmem)
            · intro n' hmem
              change q.dynamic.at_p n' l = true
              exact hNutAt n'
                (List.mem_cons_of_mem n hmem)
            · intro n' hmem
              have hne : n' ≠ n := by
                intro heq
                subst n'
                exact hNutNd.1 hmem
              rw [tighten_nut_loose_p_ne
                l sp m n q hne]
              exact hNutLoose n'
                (List.mem_cons_of_mem n hmem)

          constructor
          · exact ⟨hpre, hrec.1⟩
          · intro n' hn'
            rcases List.mem_cons.mp hn' with hnEq | hnTail
            · subst n'
              change
                (runPlan
                  (gpTightenActions l m spanners nuts)
                  (tighten_nut l sp m n q)).dynamic.tightened_p n =
                    true
              have himmediate :
                  (tighten_nut l sp m n q).dynamic.tightened_p n =
                    true :=
                tighten_nut_tightened_p_eq1 l sp m n q
              have hpres :=
                gpTightenActions_preserves_tightened_of_not_mem
                  l m n spanners nuts
                  (tighten_nut l sp m n q) hNutNd.1
              rw [hpres]
              exact himmediate
            · change
                (runPlan
                  (gpTightenActions l m spanners nuts)
                  (tighten_nut l sp m n q)).dynamic.tightened_p n' =
                    true
              exact hrec.2 n' hnTail


-- Main correctness proof

theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  have hInitTightValid :
      ValidTightenedParam s.statics s.dynamic :=
    hinit.1.2.2.2.2.1

  rcases hinit with
    ⟨hwf, hAllAt, hNoCarried, hManAtStart, hNutAtEnd,
      hNutsLoose, hSpannersUseable, hExactlyOneMan⟩

  have hUnique : ObjectUniqueLoc s.statics s.dynamic :=
    hwf.2.2.2.2.2.2.1

  let m := gpFindMan s
  let start := gpFindPathStart s.statics
  let path :=
    gpForwardPath s.statics s.statics.objects.length start
  let last := gpLastObj start path
  let spanners :=
    s.statics.objects.filter (fun o => s.statics.spanner_t o)
  let nuts :=
    s.statics.objects.filter (fun o => s.statics.nut_t o)
  let traverse := gpTraversePath s m path
  let afterTraverse := runPlan traverse s

  have hMan : s.statics.man_t m = true := by
    simpa [m] using gpFindMan_spec s hstatic

  have hStartSpec : IsPathStart s.statics start := by
    simpa [start] using
      gpFindPathStart_spec s.statics hstatic

  obtain ⟨rest, hPath⟩ : ∃ rest, path = start :: rest := by
    simpa [path] using
      gpForwardPath_cons
        s.statics s.statics.objects.length start

  have hManAt : s.dynamic.at_p m start = true :=
    hManAtStart m start hMan hStartSpec

  have hPathNodup : path.Nodup := by
    simpa [path] using
      gpForwardPath_nodup s.statics hstatic _
        hStartSpec.1

  have hPathLocations :
      ∀ l ∈ path, s.statics.location_t l = true := by
    simpa [path] using
      gpForwardPath_locations s.statics hstatic _
        hStartSpec.1

  have hPathLinked : GPLinked s.statics path := by
    simpa [path] using
      gpForwardPath_linked s.statics
        s.statics.objects.length start

  have hTraverseValid : ValidPlan traverse s := by
    change ValidPlan (gpTraversePath s m path) s
    rw [hPath]
    simp only [gpTraversePath]
    apply gpTraverseFrom_valid
      s s hstatic m start rest
    · rfl
    · simpa [hPath] using hPathNodup
    · intro l hl
      exact hPathLocations l (by simpa [hPath] using hl)
    · simpa [hPath] using hPathLinked
    · exact hMan
    · exact hManAt
    · intro sp l hsp hl hat
      exact hat
    · exact hUnique

  have hLastEnd : IsPathEnd s.statics last := by
    simpa [last, path, start] using
      gpForwardPath_last_is_end s.statics hstatic

  have hAfterManAt :
      afterTraverse.dynamic.at_p m last = true := by
    change
      (runPlan (gpTraversePath s m path) s).dynamic.at_p
        m (gpLastObj start path) = true
    rw [hPath]
    simp only [gpTraversePath]
    exact gpTraverseFrom_man_at_last
      s s hstatic m start rest hMan hManAt

  have hAfterSpCarry :
      ∀ sp ∈ spanners,
        afterTraverse.dynamic.carrying_p m sp = true := by
    intro sp hmem
    have hsp : s.statics.spanner_t sp = true :=
      (List.mem_filter.mp hmem).2
    have hlocatable :=
      spanner_is_locatable hstatic hsp
    rcases hAllAt sp hlocatable with
      ⟨l, hlLoc, hspAt⟩
    have hlPath : l ∈ path := by
      simpa [path, start] using
        gpForwardPath_contains_all_locations
          s.statics hstatic hlLoc
    have hlRest : l ∈ start :: rest := by
      simpa [hPath] using hlPath
    change
      (runPlan (gpTraversePath s m path) s).dynamic.carrying_p
        m sp = true
    rw [hPath]
    simp only [gpTraversePath]
    exact gpTraverseFrom_carries_spanner
      s s hstatic m start sp rest hsp
      ⟨l, hlRest, hspAt⟩

  have hAfterUseable :
      ∀ sp ∈ spanners,
        afterTraverse.dynamic.useable_p sp = true := by
    intro sp hmem
    have hsp : s.statics.spanner_t sp = true :=
      (List.mem_filter.mp hmem).2
    have heq :
        afterTraverse.dynamic.useable_p =
          s.dynamic.useable_p := by
      change
        (runPlan (gpTraversePath s m path) s).dynamic.useable_p =
          s.dynamic.useable_p
      rw [hPath]
      simp only [gpTraversePath]
      exact gpTraverseFrom_preserves_useable
        s s m start rest
    rw [heq]
    exact hSpannersUseable sp hsp

  have hAfterNutAt :
      ∀ n ∈ nuts,
        afterTraverse.dynamic.at_p n last = true := by
    intro n hmem
    have hn : s.statics.nut_t n = true :=
      (List.mem_filter.mp hmem).2
    have hInitialAt : s.dynamic.at_p n last = true :=
      hNutAtEnd n last hn hLastEnd
    have heq :
        afterTraverse.dynamic.at_p n last =
          s.dynamic.at_p n last := by
      change
        (runPlan (gpTraversePath s m path) s).dynamic.at_p
          n last = s.dynamic.at_p n last
      rw [hPath]
      simp only [gpTraversePath]
      exact gpTraverseFrom_preserves_nut_at
        s s hstatic m start n last rest hMan hn
    rw [heq]
    exact hInitialAt

  have hAfterLoose :
      ∀ n ∈ nuts,
        afterTraverse.dynamic.loose_p n = true := by
    intro n hmem
    have hn : s.statics.nut_t n = true :=
      (List.mem_filter.mp hmem).2
    have heq :
        afterTraverse.dynamic.loose_p =
          s.dynamic.loose_p := by
      change
        (runPlan (gpTraversePath s m path) s).dynamic.loose_p =
          s.dynamic.loose_p
      rw [hPath]
      simp only [gpTraversePath]
      exact gpTraverseFrom_preserves_loose
        s s m start rest
    rw [heq]
    exact hNutsLoose n hn

  have hAfterTightened :
      afterTraverse.dynamic.tightened_p =
        s.dynamic.tightened_p := by
    change
      (runPlan (gpTraversePath s m path) s).dynamic.tightened_p =
        s.dynamic.tightened_p
    rw [hPath]
    simp only [gpTraversePath]
    exact gpTraverseFrom_preserves_tightened
      s s m start rest

  have hAfterStatics :
      afterTraverse.statics = s.statics := by
    change (runPlan traverse s).statics = s.statics
    exact runPlan_statics traverse s

  have hTighten :
      ValidPlan
          (gpTightenActions last m spanners nuts)
          afterTraverse ∧
        ∀ n ∈ nuts,
          (runPlan
            (gpTightenActions last m spanners nuts)
            afterTraverse).dynamic.tightened_p n = true := by
    apply gpTightenActions_valid_and_tightens
    · simpa [spanners, nuts] using
        wf_spanner_nut_count hstatic
    · exact (wf_objects_nodup hstatic).filter _
    · exact (wf_objects_nodup hstatic).filter _
    · rw [hAfterStatics]
      exact hLastEnd.1
    · rw [hAfterStatics]
      exact hMan
    · exact hAfterManAt
    · intro sp hmem
      rw [hAfterStatics]
      exact (List.mem_filter.mp hmem).2
    · exact hAfterSpCarry
    · exact hAfterUseable
    · intro n hmem
      rw [hAfterStatics]
      exact (List.mem_filter.mp hmem).2
    · exact hAfterNutAt
    · exact hAfterLoose

  have hSolveShape :
      solve s g =
        traverse ++
          gpTightenActions last m spanners nuts := by
    simp [solve, traverse, last, path, start, m, spanners, nuts]

  have hSolveValid : ValidPlan (solve s g) s := by
    rw [hSolveShape, validPlan_append]
    exact ⟨hTraverseValid, hTighten.1⟩

  have hAllTightened :
      ∀ n, s.statics.nut_t n = true →
        (runPlan (solve s g) s).dynamic.tightened_p n = true := by
    intro n hn
    have hnMemObj :
        n ∈ s.statics.objects :=
      locatable_mem_objects hstatic
        (nut_is_locatable hstatic hn)
    have hnMem : n ∈ nuts := by
      apply List.mem_filter.mpr
      exact ⟨hnMemObj, hn⟩
    rw [hSolveShape, runPlan_append]
    exact hTighten.2 n hnMem

  have hNonNutUnchanged :
      ∀ n, s.statics.nut_t n ≠ true →
        (runPlan (solve s g) s).dynamic.tightened_p n =
          s.dynamic.tightened_p n := by
    intro n hn
    have hnNotMem : n ∉ nuts := by
      intro hmem
      exact hn (List.mem_filter.mp hmem).2
    rw [hSolveShape, runPlan_append]
    rw [gpTightenActions_preserves_tightened_of_not_mem
      last m n spanners nuts afterTraverse hnNotMem]
    exact congrFun hAfterTightened n

  rcases hgoal with
    ⟨_, _, _, _, hGoalTightValid, _, _, _, _, _,
      hGoalAll, hIgnoreAt, hIgnoreCarry, hIgnoreUseable,
      hIgnoreLoose⟩

  refine ⟨hSolveValid, ?_⟩
  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro o l
    rw [hIgnoreAt o l]
    trivial
  · intro m' sp
    rw [hIgnoreCarry m' sp]
    trivial
  · intro sp
    rw [hIgnoreUseable sp]
    trivial
  · intro n
    cases hgn : g.dynamic.tightened_p n with
    | none =>
        trivial
    | some b =>
        cases b with
        | false =>
            have hn : s.statics.nut_t n ≠ true := by
              intro hn
              have htrue := hGoalAll n hn
              rw [htrue] at hgn
              contradiction
            have hInitialFalse :
                s.dynamic.tightened_p n = false := by
              by_cases ht : s.dynamic.tightened_p n = true
              · exact False.elim (hn (hInitTightValid n ht))
              · exact Bool.eq_false_of_not_eq_true ht
            rw [hNonNutUnchanged n hn]
            exact hInitialFalse
        | true =>
            have hn : s.statics.nut_t n = true := by
              apply hGoalTightValid n
              change g.dynamic.tightened_p n = some true
              exact hgn
            exact hAllTightened n hn
  · intro n
    rw [hIgnoreLoose n]
    trivial

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

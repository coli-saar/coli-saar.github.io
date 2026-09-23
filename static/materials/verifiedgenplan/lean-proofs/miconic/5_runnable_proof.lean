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
  destin_p : Obj → Obj → Bool
  above_p : Obj → Obj → Bool
  passenger_t : Obj → Bool
  floor_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  origin_p : Obj → Obj → α
  boarded_p : Obj → α
  served_p : Obj → α
  lift_at_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidDestinParam (s : StaticState) : Prop :=
  ∀ var_person var_floor, s.destin_p var_person var_floor = true → s.passenger_t var_person = true ∧ s.floor_t var_floor = true

def ValidAboveParam (s : StaticState) : Prop :=
  ∀ var_floor1 var_floor2, s.above_p var_floor1 var_floor2 = true → s.floor_t var_floor1 = true ∧ s.floor_t var_floor2 = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.passenger_t x = true → x ∈ s.objects) ∧
  (∀ x, s.floor_t x = true → x ∈ s.objects) ∧
  (∀ x, s.passenger_t x = true → s.floor_t x = false)

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects → (s.passenger_t x = true ∨ s.floor_t x = true)

def AboveIrreflexive (s : StaticState) : Prop :=
  ∀ f, s.above_p f f = false

def AboveAsymmetric (s : StaticState) : Prop :=
  ∀ f1 f2, s.above_p f1 f2 = true → s.above_p f2 f1 = false

def AboveTransitive (s : StaticState) : Prop :=
  ∀ f1 f2 f3, s.above_p f1 f2 = true → s.above_p f2 f3 = true → s.above_p f1 f3 = true

def DestinFunctional (s : StaticState) : Prop :=
  ∀ p f1 f2, s.destin_p p f1 = true → s.destin_p p f2 = true → f1 = f2

def DestinExists (s : StaticState) : Prop :=
  ∀ p, s.passenger_t p = true → ∃ f, s.destin_p p f = true

def WellFormedStatic (s : StaticState) : Prop := 
  ObjectsUnique s ∧
  ValidDestinParam s ∧
  ValidAboveParam s ∧
  ValidTypeHierarchy s ∧
  TypeCoverage s ∧
  AboveIrreflexive s ∧
  AboveAsymmetric s ∧
  AboveTransitive s ∧
  DestinFunctional s ∧
  DestinExists s

def ValidOriginParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_person var_floor, Truthy.isTrue (d.origin_p var_person var_floor) → s.passenger_t var_person = true ∧ s.floor_t var_floor = true

def ValidBoardedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_person, Truthy.isTrue (d.boarded_p var_person) → s.passenger_t var_person = true

def ValidServedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_person, Truthy.isTrue (d.served_p var_person) → s.passenger_t var_person = true

def ValidLiftAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_floor, Truthy.isTrue (d.lift_at_p var_floor) → s.floor_t var_floor = true

def OriginFunctional {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ p f1 f2, Truthy.isTrue (d.origin_p p f1) → Truthy.isTrue (d.origin_p p f2) → f1 = f2

def BoardedOrServedImpliesNoOrigin {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ p f, (Truthy.isTrue (d.boarded_p p) ∨ Truthy.isTrue (d.served_p p)) → ¬ Truthy.isTrue (d.origin_p p f)

def SameBuilding (s : StaticState) (f1 f2 : Obj) : Prop :=
  Relation.ReflTransGen (fun a b => s.above_p a b = true ∨ s.above_p b a = true) f1 f2

def LiftAtUniquePerBuilding {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ f1 f2, SameBuilding s f1 f2 →
    Truthy.isTrue (d.lift_at_p f1) → Truthy.isTrue (d.lift_at_p f2) → f1 = f2

def LiftAtExistsPerBuilding (s : State) : Prop :=
  ∀ f, s.statics.floor_t f = true →
    ∃ f', SameBuilding s.statics f f' ∧ s.dynamic.lift_at_p f' = true

def WellFormed (s : State) : Prop := 
  WellFormedStatic s.statics ∧
  ValidOriginParam s.statics s.dynamic ∧
  ValidBoardedParam s.statics s.dynamic ∧
  ValidServedParam s.statics s.dynamic ∧
  ValidLiftAtParam s.statics s.dynamic ∧
  OriginFunctional s.statics s.dynamic ∧
  BoardedOrServedImpliesNoOrigin s.statics s.dynamic ∧
  LiftAtUniquePerBuilding s.statics s.dynamic ∧
  LiftAtExistsPerBuilding s

def InitNoOneBoarded (s : State) : Prop :=
  ∀ p, s.statics.passenger_t p = true → s.dynamic.boarded_p p = false

def InitNoOneServed (s : State) : Prop :=
  ∀ p, s.statics.passenger_t p = true → s.dynamic.served_p p = false

def InitEveryPassengerHasOrigin (s : State) : Prop :=
  ∀ p, s.statics.passenger_t p = true → ∃ f, s.dynamic.origin_p p f = true

def WellFormedInit (s : State) : Prop := 
  WellFormed s ∧
  InitNoOneBoarded s ∧
  InitNoOneServed s ∧
  InitEveryPassengerHasOrigin s

def GoalIgnoreOrigin (initial : State) (g : Goal) : Prop :=
  ∀ p f, g.dynamic.origin_p p f = none

def GoalIgnoreBoarded (initial : State) (g : Goal) : Prop :=
  ∀ p, g.dynamic.boarded_p p = none

def GoalIgnoreLiftAt (initial : State) (g : Goal) : Prop :=
  ∀ f, g.dynamic.lift_at_p f = none

def GoalServedOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ p, g.dynamic.served_p p ≠ some false

def GoalEveryPassengerServed (initial : State) (g : Goal) : Prop :=
  ∀ p, initial.statics.passenger_t p = true → g.dynamic.served_p p = some true

def WellFormedGoal (initial : State) (g : Goal) : Prop := 
  WellFormedStatic initial.statics ∧
  ValidOriginParam initial.statics g.dynamic ∧
  ValidBoardedParam initial.statics g.dynamic ∧
  ValidServedParam initial.statics g.dynamic ∧
  ValidLiftAtParam initial.statics g.dynamic ∧
  OriginFunctional initial.statics g.dynamic ∧
  BoardedOrServedImpliesNoOrigin initial.statics g.dynamic ∧
  LiftAtUniquePerBuilding initial.statics g.dynamic ∧
  GoalIgnoreOrigin initial g ∧
  GoalIgnoreBoarded initial g ∧
  GoalIgnoreLiftAt initial g ∧
  GoalServedOnlyPositive initial g ∧
  GoalEveryPassengerServed initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_person var_floor,
    match g.dynamic.origin_p var_person var_floor with
    | none => True
    | some b => s.dynamic.origin_p var_person var_floor = b) ∧
  (∀ var_person,
    match g.dynamic.boarded_p var_person with
    | none => True
    | some b => s.dynamic.boarded_p var_person = b) ∧
  (∀ var_person,
    match g.dynamic.served_p var_person with
    | none => True
    | some b => s.dynamic.served_p var_person = b) ∧
  (∀ var_floor,
    match g.dynamic.lift_at_p var_floor with
    | none => True
    | some b => s.dynamic.lift_at_p var_floor = b)

def boardPre (var_f : Obj) (var_p : Obj) (s : State) : Prop :=
  s.statics.floor_t var_f = true ∧
  s.statics.passenger_t var_p = true ∧
  s.dynamic.lift_at_p var_f = true ∧
  s.dynamic.origin_p var_p var_f = true

def departPre (var_f : Obj) (var_p : Obj) (s : State) : Prop :=
  s.statics.floor_t var_f = true ∧
  s.statics.passenger_t var_p = true ∧
  s.dynamic.lift_at_p var_f = true ∧
  s.statics.destin_p var_p var_f = true ∧
  s.dynamic.boarded_p var_p = true

def upPre (var_f1 : Obj) (var_f2 : Obj) (s : State) : Prop :=
  s.statics.floor_t var_f1 = true ∧
  s.statics.floor_t var_f2 = true ∧
  s.dynamic.lift_at_p var_f1 = true ∧
  s.statics.above_p var_f1 var_f2 = true

def downPre (var_f1 : Obj) (var_f2 : Obj) (s : State) : Prop :=
  s.statics.floor_t var_f1 = true ∧
  s.statics.floor_t var_f2 = true ∧
  s.dynamic.lift_at_p var_f1 = true ∧
  s.statics.above_p var_f2 var_f1 = true

def board (var_f : Obj) (var_p : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    origin_p :=
      fun var_p' var_f' =>
        if var_p' = var_p ∧ var_f' = var_f then
          false
        else
          s.dynamic.origin_p var_p' var_f',
    boarded_p :=
      fun var_p' =>
        if var_p' = var_p then
          true
        else
          s.dynamic.boarded_p var_p'
  }
}

def depart (var_f : Obj) (var_p : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    boarded_p :=
      fun var_p' =>
        if var_p' = var_p then
          false
        else
          s.dynamic.boarded_p var_p',
    served_p :=
      fun var_p' =>
        if var_p' = var_p then
          true
        else
          s.dynamic.served_p var_p'
  }
}

def up (var_f1 : Obj) (var_f2 : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    lift_at_p :=
      fun var_f2' =>
        if var_f2' = var_f2 then
          true
        else if var_f2' = var_f1 then
          false
        else
          s.dynamic.lift_at_p var_f2'
  }
}

def down (var_f1 : Obj) (var_f2 : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    lift_at_p :=
      fun var_f2' =>
        if var_f2' = var_f2 then
          true
        else if var_f2' = var_f1 then
          false
        else
          s.dynamic.lift_at_p var_f2'
  }
}

inductive PlanAction where
  | board  (var_f : Obj) (var_p : Obj)
  | depart (var_f : Obj) (var_p : Obj)
  | up     (var_f1 : Obj) (var_f2 : Obj)
  | down   (var_f1 : Obj) (var_f2 : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .board  var_f var_p  , s => boardPre var_f var_p s
  | .depart var_f var_p  , s => departPre var_f var_p s
  | .up     var_f1 var_f2, s => upPre var_f1 var_f2 s
  | .down   var_f1 var_f2, s => downPre var_f1 var_f2 s

def actionApply : PlanAction → State → State
  | .board  var_f var_p  , s => board var_f var_p s
  | .depart var_f var_p  , s => depart var_f var_p s
  | .up     var_f1 var_f2, s => up var_f1 var_f2 s
  | .down   var_f1 var_f2, s => down var_f1 var_f2 s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Floors reachable by one lift movement from f.
def gpNeighbors (st : StaticState) (f : Obj) : List Obj :=
  st.objects.filter fun x =>
    st.floor_t x &&
      (st.above_p f x || st.above_p x f)

-- Breadth-first search. Paths are stored in reverse order while searching.
def gpBfsAux (st : StaticState) (goal : Obj) :
    Nat → List (Obj × List Obj) → List Obj → Option (List Obj)
  | 0, _, _ => none
  | Nat.succ _, [], _ => none
  | Nat.succ fuel, (current, revPath) :: queue, seen =>
      if current = goal then
        some revPath.reverse
      else
        let fresh :=
          (gpNeighbors st current).filter fun x =>
            !(seen.contains x)
        let newEntries :=
          fresh.map fun x => (x, x :: revPath)
        gpBfsAux st goal fuel
          (queue ++ newEntries)
          (seen ++ fresh)

def gpFindPath (st : StaticState) (start goal : Obj) :
    Option (List Obj) :=
  gpBfsAux st goal (st.objects.length + 1)
    [(start, [start])] [start]

def gpPathActionsFrom
    (st : StaticState) (current : Obj) :
    List Obj → List PlanAction
  | [] => []
  | next :: rest =>
      let action :=
        if st.above_p current next = true then
          PlanAction.up current next
        else
          PlanAction.down current next
      action :: gpPathActionsFrom st next rest

def gpPathActions (st : StaticState) :
    List Obj → List PlanAction
  | [] => []
  | start :: rest => gpPathActionsFrom st start rest

def gpFind? (pred : Obj → Bool) :
    List Obj → Option Obj
  | [] => none
  | x :: xs =>
      if pred x = true then
        some x
      else
        gpFind? pred xs

def gpFindLiftPath (s : State) (target : Obj) :
    List Obj → Option (List Obj)
  | [] => none
  | f :: fs =>
      if s.dynamic.lift_at_p f = true then
        match gpFindPath s.statics f target with
        | some path => some path
        | none => gpFindLiftPath s target fs
      else
        gpFindLiftPath s target fs

def gpMoveTo (s : State) (target : Obj) :
    List PlanAction × State :=
  match gpFindLiftPath s target s.statics.objects with
  | none => ([], s)
  | some path =>
      let actions := gpPathActions s.statics path
      (actions, runPlan actions s)

def gpOrigin? (s : State) (p : Obj) : Option Obj :=
  gpFind?
    (fun f => s.dynamic.origin_p p f)
    s.statics.objects

def gpDestination? (s : State) (p : Obj) : Option Obj :=
  gpFind?
    (fun f => s.statics.destin_p p f)
    s.statics.objects

def gpServePassenger (p : Obj) (s : State) :
    List PlanAction × State :=
  match gpOrigin? s p, gpDestination? s p with
  | some origin, some destination =>
      let (toOrigin, sAtOrigin) := gpMoveTo s origin

      let boardAction := PlanAction.board origin p
      let sBoarded := actionApply boardAction sAtOrigin

      let (toDestination, sAtDestination) :=
        gpMoveTo sBoarded destination

      let departAction := PlanAction.depart destination p
      let sServed := actionApply departAction sAtDestination

      (toOrigin ++
        [boardAction] ++
        toDestination ++
        [departAction],
       sServed)
  | _, _ => ([], s)

def gpServePassengers :
    List Obj → State → List PlanAction × State
  | [], s => ([], s)
  | p :: ps, s =>
      let (currentPlan, nextState) := gpServePassenger p s
      let (remainingPlan, finalState) :=
        gpServePassengers ps nextState
      (currentPlan ++ remainingPlan, finalState)

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  let passengers :=
    s.statics.objects.filter fun p =>
      s.statics.passenger_t p
  (gpServePassengers passengers s).1

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

lemma board_statics (var_f var_p : Obj) (s : State) :
    (board var_f var_p s).statics = s.statics := rfl

lemma depart_statics (var_f var_p : Obj) (s : State) :
    (depart var_f var_p s).statics = s.statics := rfl

lemma up_statics (var_f1 var_f2 : Obj) (s : State) :
    (up var_f1 var_f2 s).statics = s.statics := rfl

lemma down_statics (var_f1 var_f2 : Obj) (s : State) :
    (down var_f1 var_f2 s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | board var_f var_p  => exact board_statics var_f var_p s
      | depart var_f var_p => exact depart_statics var_f var_p s
      | up var_f1 var_f2   => exact up_statics var_f1 var_f2 s
      | down var_f1 var_f2 => exact down_statics var_f1 var_f2 s

-- board only touches boarded_p, origin_p
lemma board_origin_p_ne (var_f var_p : Obj) (s : State) {var_p' var_f' : Obj} (h1 : var_p' ≠ var_p) :
    (board var_f var_p s).dynamic.origin_p var_p' var_f' = s.dynamic.origin_p var_p' var_f' := by
  unfold board
  simp [h1]

lemma board_origin_p_ne_var_floor (var_f var_p : Obj) (s : State) {var_f' : Obj} (h1 : var_f' ≠ var_f) :
    (board var_f var_p s).dynamic.origin_p var_p var_f' = s.dynamic.origin_p var_p var_f' := by
  unfold board
  simp [h1]

lemma board_boarded_p_ne (var_f var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (board var_f var_p s).dynamic.boarded_p var_p' = s.dynamic.boarded_p var_p' := by
  unfold board
  simp [h1]

-- board never touches served_p
lemma board_served_p (var_f var_p : Obj) (s : State) :
    (board var_f var_p s).dynamic.served_p = s.dynamic.served_p := rfl

-- board never touches lift_at_p
lemma board_lift_at_p (var_f var_p : Obj) (s : State) :
    (board var_f var_p s).dynamic.lift_at_p = s.dynamic.lift_at_p := rfl

-- depart only touches served_p, boarded_p
lemma depart_boarded_p_ne (var_f var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (depart var_f var_p s).dynamic.boarded_p var_p' = s.dynamic.boarded_p var_p' := by
  unfold depart
  simp [h1]

lemma depart_served_p_ne (var_f var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (depart var_f var_p s).dynamic.served_p var_p' = s.dynamic.served_p var_p' := by
  unfold depart
  simp [h1]

-- depart never touches origin_p
lemma depart_origin_p (var_f var_p : Obj) (s : State) :
    (depart var_f var_p s).dynamic.origin_p = s.dynamic.origin_p := rfl

-- depart never touches lift_at_p
lemma depart_lift_at_p (var_f var_p : Obj) (s : State) :
    (depart var_f var_p s).dynamic.lift_at_p = s.dynamic.lift_at_p := rfl

-- up only touches lift_at_p
lemma up_lift_at_p_ne (var_f1 var_f2 : Obj) (s : State) {var_f2' : Obj} (h1 : var_f2' ≠ var_f2) (h2 : var_f2' ≠ var_f1) :
    (up var_f1 var_f2 s).dynamic.lift_at_p var_f2' = s.dynamic.lift_at_p var_f2' := by
  unfold up
  simp [h1, h2]

-- up never touches origin_p
lemma up_origin_p (var_f1 var_f2 : Obj) (s : State) :
    (up var_f1 var_f2 s).dynamic.origin_p = s.dynamic.origin_p := rfl

-- up never touches boarded_p
lemma up_boarded_p (var_f1 var_f2 : Obj) (s : State) :
    (up var_f1 var_f2 s).dynamic.boarded_p = s.dynamic.boarded_p := rfl

-- up never touches served_p
lemma up_served_p (var_f1 var_f2 : Obj) (s : State) :
    (up var_f1 var_f2 s).dynamic.served_p = s.dynamic.served_p := rfl

-- down only touches lift_at_p
lemma down_lift_at_p_ne (var_f1 var_f2 : Obj) (s : State) {var_f2' : Obj} (h1 : var_f2' ≠ var_f2) (h2 : var_f2' ≠ var_f1) :
    (down var_f1 var_f2 s).dynamic.lift_at_p var_f2' = s.dynamic.lift_at_p var_f2' := by
  unfold down
  simp [h1, h2]

-- down never touches origin_p
lemma down_origin_p (var_f1 var_f2 : Obj) (s : State) :
    (down var_f1 var_f2 s).dynamic.origin_p = s.dynamic.origin_p := rfl

-- down never touches boarded_p
lemma down_boarded_p (var_f1 var_f2 : Obj) (s : State) :
    (down var_f1 var_f2 s).dynamic.boarded_p = s.dynamic.boarded_p := rfl

-- down never touches served_p
lemma down_served_p (var_f1 var_f2 : Obj) (s : State) :
    (down var_f1 var_f2 s).dynamic.served_p = s.dynamic.served_p := rfl

lemma board_origin_p_eq1 (var_f var_p : Obj) (s : State) :
    (board var_f var_p s).dynamic.origin_p var_p var_f = false := by
  unfold board
  simp

lemma board_boarded_p_eq1 (var_f var_p : Obj) (s : State) :
    (board var_f var_p s).dynamic.boarded_p var_p = true := by
  unfold board
  simp

lemma depart_boarded_p_eq1 (var_f var_p : Obj) (s : State) :
    (depart var_f var_p s).dynamic.boarded_p var_p = false := by
  unfold depart
  simp

lemma depart_served_p_eq1 (var_f var_p : Obj) (s : State) :
    (depart var_f var_p s).dynamic.served_p var_p = true := by
  unfold depart
  simp

lemma up_lift_at_p_eq1 (var_f1 var_f2 : Obj) (s : State) :
    (up var_f1 var_f2 s).dynamic.lift_at_p var_f2 = true := by
  unfold up
  simp

lemma up_lift_at_p_eq2 (var_f1 var_f2 : Obj) (s : State) (h1 : var_f1 ≠ var_f2) :
    (up var_f1 var_f2 s).dynamic.lift_at_p var_f1 = false := by
  unfold up
  simp [h1]

lemma down_lift_at_p_eq1 (var_f1 var_f2 : Obj) (s : State) :
    (down var_f1 var_f2 s).dynamic.lift_at_p var_f2 = true := by
  unfold down
  simp

lemma down_lift_at_p_eq2 (var_f1 var_f2 : Obj) (s : State) (h1 : var_f1 ≠ var_f2) :
    (down var_f1 var_f2 s).dynamic.lift_at_p var_f1 = false := by
  unfold down
  simp [h1]

lemma sameBuilding_of_link
    (s : StaticState) {f1 f2 : Obj}
    (hlink :
      s.above_p f1 f2 = true ∨
      s.above_p f2 f1 = true) :
    SameBuilding s f1 f2 := by
  exact Relation.ReflTransGen.single hlink

lemma sameBuilding_trans
    (s : StaticState) {f1 f2 f3 : Obj}
    (h12 : SameBuilding s f1 f2)
    (h23 : SameBuilding s f2 f3) :
    SameBuilding s f1 f3 := by
  exact h12.trans h23

lemma board_preserves_wf
    (var_f var_p)
    (s : State)
    (hwf : WellFormed s)
    (hpre : boardPre var_f var_p s) :
    WellFormed (board var_f var_p s) := by
  rcases hwf with
    ⟨hstatic, horigin, hboarded, hserved, hliftValid,
      horiginFunctional, hnoOrigin, hliftUnique, hliftExists⟩
  rcases hpre with
    ⟨hfloor, hpassenger, hliftAt, horiginAt⟩

  have h_origin_old :
      ∀ p f,
        (board var_f var_p s).dynamic.origin_p p f = true →
        s.dynamic.origin_p p f = true := by
    intro p f h
    by_cases hp : p = var_p
    · subst p
      by_cases hf : f = var_f
      · subst f
        rw [board_origin_p_eq1] at h
        simp at h
      · rw [board_origin_p_ne_var_floor var_f var_p s hf] at h
        exact h
    · rw [board_origin_p_ne var_f var_p s hp] at h
      exact h

  refine
    ⟨hstatic, ?_, ?_, hserved, hliftValid, ?_, ?_,
      hliftUnique, hliftExists⟩
  · intro p f h
    change (board var_f var_p s).dynamic.origin_p p f = true at h
    exact horigin p f (h_origin_old p f h)
  · intro p h
    change (board var_f var_p s).dynamic.boarded_p p = true at h
    by_cases hp : p = var_p
    · subst p
      exact hpassenger
    · rw [board_boarded_p_ne var_f var_p s hp] at h
      exact hboarded p h
  · intro p f1 f2 h1 h2
    change (board var_f var_p s).dynamic.origin_p p f1 = true at h1
    change (board var_f var_p s).dynamic.origin_p p f2 = true at h2
    exact horiginFunctional p f1 f2
      (h_origin_old p f1 h1)
      (h_origin_old p f2 h2)
  · intro p f hboardedOrServed hnewOrigin
    change
      ((board var_f var_p s).dynamic.boarded_p p = true ∨
       (board var_f var_p s).dynamic.served_p p = true)
      at hboardedOrServed
    change
      (board var_f var_p s).dynamic.origin_p p f = true
      at hnewOrigin
    by_cases hp : p = var_p
    · subst p
      have hf : f = var_f :=
        horiginFunctional var_p f var_f
          (h_origin_old var_p f hnewOrigin)
          horiginAt
      subst f
      rw [board_origin_p_eq1] at hnewOrigin
      simp at hnewOrigin
    · have holdBoardedOrServed :
          s.dynamic.boarded_p p = true ∨
          s.dynamic.served_p p = true := by
        rcases hboardedOrServed with hb | hs
        · left
          rw [board_boarded_p_ne var_f var_p s hp] at hb
          exact hb
        · right
          exact hs
      exact
        (hnoOrigin p f holdBoardedOrServed)
          (h_origin_old p f hnewOrigin)

lemma depart_preserves_wf
    (var_f var_p)
    (s : State)
    (hwf : WellFormed s)
    (hpre : departPre var_f var_p s) :
    WellFormed (depart var_f var_p s) := by
  rcases hwf with
    ⟨hstatic, horigin, hboarded, hserved, hliftValid,
      horiginFunctional, hnoOrigin, hliftUnique, hliftExists⟩
  rcases hpre with
    ⟨hfloor, hpassenger, hliftAt, hdestin, hboardedPre⟩

  refine
    ⟨hstatic, horigin, ?_, ?_, hliftValid, horiginFunctional,
      ?_, hliftUnique, hliftExists⟩
  · intro p h
    change (depart var_f var_p s).dynamic.boarded_p p = true at h
    by_cases hp : p = var_p
    · subst p
      rw [depart_boarded_p_eq1] at h
      simp at h
    · rw [depart_boarded_p_ne var_f var_p s hp] at h
      exact hboarded p h
  · intro p h
    change (depart var_f var_p s).dynamic.served_p p = true at h
    by_cases hp : p = var_p
    · subst p
      exact hpassenger
    · rw [depart_served_p_ne var_f var_p s hp] at h
      exact hserved p h
  · intro p f hboardedOrServed hnewOrigin
    change
      ((depart var_f var_p s).dynamic.boarded_p p = true ∨
       (depart var_f var_p s).dynamic.served_p p = true)
      at hboardedOrServed
    change s.dynamic.origin_p p f = true at hnewOrigin
    by_cases hp : p = var_p
    · subst p
      exact
        (hnoOrigin var_p f (Or.inl hboardedPre)) hnewOrigin
    · have holdBoardedOrServed :
          s.dynamic.boarded_p p = true ∨
          s.dynamic.served_p p = true := by
        rcases hboardedOrServed with hb | hs
        · left
          rw [depart_boarded_p_ne var_f var_p s hp] at hb
          exact hb
        · right
          rw [depart_served_p_ne var_f var_p s hp] at hs
          exact hs
      exact
        (hnoOrigin p f holdBoardedOrServed) hnewOrigin

lemma lift_move_preserves_wf
    (var_f1 var_f2 : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hfloor1 : s.statics.floor_t var_f1 = true)
    (hfloor2 : s.statics.floor_t var_f2 = true)
    (hliftAtSource : s.dynamic.lift_at_p var_f1 = true)
    (hlink :
      s.statics.above_p var_f1 var_f2 = true ∨
      s.statics.above_p var_f2 var_f1 = true)
    (hne : var_f1 ≠ var_f2) :
    WellFormed (up var_f1 var_f2 s) := by
  rcases hwf with
    ⟨hstatic, horigin, hboarded, hserved, hliftValid,
      horiginFunctional, hnoOrigin, hliftUnique, hliftExists⟩

  have hmove :
      SameBuilding s.statics var_f1 var_f2 :=
    sameBuilding_of_link s.statics hlink

  have hlinkReverse :
      s.statics.above_p var_f2 var_f1 = true ∨
      s.statics.above_p var_f1 var_f2 = true := by
    rcases hlink with h | h
    · exact Or.inr h
    · exact Or.inl h

  have hmoveReverse :
      SameBuilding s.statics var_f2 var_f1 :=
    sameBuilding_of_link s.statics hlinkReverse

  have hnewLiftCases :
      ∀ f,
        (up var_f1 var_f2 s).dynamic.lift_at_p f = true →
        f = var_f2 ∨
          (f ≠ var_f1 ∧ s.dynamic.lift_at_p f = true) := by
    intro f h
    by_cases hf2 : f = var_f2
    · exact Or.inl hf2
    · by_cases hf1 : f = var_f1
      · subst f
        have hfalse :=
          up_lift_at_p_eq2 var_f1 var_f2 s hne
        rw [hfalse] at h
        simp at h
      · right
        constructor
        · exact hf1
        · rw [up_lift_at_p_ne var_f1 var_f2 s hf2 hf1] at h
          exact h

  refine
    ⟨hstatic, horigin, hboarded, hserved, ?_,
      horiginFunctional, hnoOrigin, ?_, ?_⟩
  · intro f h
    change (up var_f1 var_f2 s).dynamic.lift_at_p f = true at h
    rcases hnewLiftCases f h with hf2 | ⟨hf1, hold⟩
    · subst f
      exact hfloor2
    · exact hliftValid f hold
  · intro f1 f2 hsame h1 h2
    change (up var_f1 var_f2 s).dynamic.lift_at_p f1 = true at h1
    change (up var_f1 var_f2 s).dynamic.lift_at_p f2 = true at h2
    rcases hnewLiftCases f1 h1 with hf1Target | ⟨hf1Source, hf1Old⟩
    · subst f1
      rcases hnewLiftCases f2 h2 with hf2Target | ⟨hf2Source, hf2Old⟩
      · subst f2
        rfl
      · have hsourceToF2 :
            SameBuilding s.statics var_f1 f2 :=
          sameBuilding_trans s.statics hmove hsame
        have heq : var_f1 = f2 :=
          hliftUnique var_f1 f2 hsourceToF2 hliftAtSource hf2Old
        exact (hf2Source heq.symm).elim
    · rcases hnewLiftCases f2 h2 with hf2Target | ⟨hf2Source, hf2Old⟩
      · subst f2
        have hf1ToSource :
            SameBuilding s.statics f1 var_f1 :=
          sameBuilding_trans s.statics hsame hmoveReverse
        have heq : f1 = var_f1 :=
          hliftUnique f1 var_f1 hf1ToSource hf1Old hliftAtSource
        exact (hf1Source heq).elim
      · exact hliftUnique f1 f2 hsame hf1Old hf2Old
  · intro f hf
    obtain ⟨w, hfw, hw⟩ := hliftExists f hf
    change s.dynamic.lift_at_p w = true at hw
    by_cases hw1 : w = var_f1
    · subst w
      refine ⟨var_f2, ?_, up_lift_at_p_eq1 var_f1 var_f2 s⟩
      exact sameBuilding_trans s.statics hfw hmove
    · by_cases hw2 : w = var_f2
      · subst w
        exact
          ⟨var_f2, hfw, up_lift_at_p_eq1 var_f1 var_f2 s⟩
      · refine ⟨w, hfw, ?_⟩
        rw [up_lift_at_p_ne var_f1 var_f2 s hw2 hw1]
        exact hw

lemma up_preserves_wf
    (var_f1 var_f2)
    (s : State)
    (hwf : WellFormed s)
    (hpre : upPre var_f1 var_f2 s) :
    WellFormed (up var_f1 var_f2 s) := by
  rcases hpre with
    ⟨hfloor1, hfloor2, hliftAtSource, habove⟩

  have hirreflexive : AboveIrreflexive s.statics :=
    hwf.1.2.2.2.2.2.1

  have hne : var_f1 ≠ var_f2 := by
    intro heq
    subst var_f2
    have hfalse := hirreflexive var_f1
    rw [habove] at hfalse
    simp at hfalse

  exact
    lift_move_preserves_wf
      var_f1 var_f2 s hwf
      hfloor1 hfloor2 hliftAtSource
      (Or.inl habove) hne

lemma down_preserves_wf
    (var_f1 var_f2)
    (s : State)
    (hwf : WellFormed s)
    (hpre : downPre var_f1 var_f2 s) :
    WellFormed (down var_f1 var_f2 s) := by
  rcases hpre with
    ⟨hfloor1, hfloor2, hliftAtSource, habove⟩

  have hirreflexive : AboveIrreflexive s.statics :=
    hwf.1.2.2.2.2.2.1

  have hne : var_f1 ≠ var_f2 := by
    intro heq
    subst var_f2
    have hfalse := hirreflexive var_f1
    rw [habove] at hfalse
    simp at hfalse

  exact
    lift_move_preserves_wf
      var_f1 var_f2 s hwf
      hfloor1 hfloor2 hliftAtSource
      (Or.inr habove) hne

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | board var_f var_p =>
      exact board_preserves_wf var_f var_p s hwf hpre
  | depart var_f var_p =>
      exact depart_preserves_wf var_f var_p s hwf hpre
  | up var_f1 var_f2 =>
      exact up_preserves_wf var_f1 var_f2 s hwf hpre
  | down var_f1 var_f2 =>
      exact down_preserves_wf var_f1 var_f2 s hwf hpre

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

def gpQueueNodes (queue : List (Obj × List Obj)) : List Obj :=
  queue.map Prod.fst

inductive GpFullPath (st : StaticState) (start : Obj) :
    List Obj → Obj → Prop
  | single :
      GpFullPath st start [start] start
  | snoc {path current next} :
      GpFullPath st start path current →
      next ∈ gpNeighbors st current →
      GpFullPath st start (path ++ [next]) next

inductive GpMovePath (st : StaticState) :
    Obj → List Obj → Obj → Prop
  | nil (current : Obj) :
      GpMovePath st current [] current
  | cons {current next rest goal} :
      next ∈ gpNeighbors st current →
      GpMovePath st next rest goal →
      GpMovePath st current (next :: rest) goal

lemma gpNeighbors_mem
    (st : StaticState) (current next : Obj) :
    next ∈ gpNeighbors st current ↔
      next ∈ st.objects ∧
      st.floor_t next = true ∧
      (st.above_p current next = true ∨
       st.above_p next current = true) := by
  simp [gpNeighbors, Bool.and_eq_true]

lemma gpMovePath_snoc
    {st : StaticState}
    {start last z : Obj}
    {rest : List Obj}
    (hpath : GpMovePath st start rest last)
    (hz : z ∈ gpNeighbors st last) :
    GpMovePath st start (rest ++ [z]) z := by
  induction hpath generalizing z with
  | nil =>
      simpa using
        (GpMovePath.cons hz (GpMovePath.nil z))
  | cons hhead htail ih =>
      exact GpMovePath.cons hhead (ih hz)

lemma gpFullPath_to_movePath
    {st : StaticState}
    {start goal : Obj}
    {path : List Obj}
    (hpath : GpFullPath st start path goal) :
    ∃ rest,
      path = start :: rest ∧
      GpMovePath st start rest goal := by
  induction hpath with
  | single =>
      exact ⟨[], rfl, GpMovePath.nil start⟩
  | @snoc path current next hprefix hnext ih =>
      rcases ih with ⟨rest, hshape, hmove⟩
      refine ⟨rest ++ [next], ?_, gpMovePath_snoc hmove hnext⟩
      rw [hshape]
      simp

lemma gpBfsAux_sound
    (st : StaticState)
    (start goal : Obj)
    (fuel : Nat)
    (queue : List (Obj × List Obj))
    (seen : List Obj)
    (hqueue :
      ∀ entry ∈ queue,
        GpFullPath st start entry.2.reverse entry.1)
    {path : List Obj}
    (hout : gpBfsAux st goal fuel queue seen = some path) :
    GpFullPath st start path goal := by
  induction fuel generalizing queue seen path with
  | zero =>
      simp [gpBfsAux] at hout
  | succ fuel ih =>
      cases queue with
      | nil =>
          simp [gpBfsAux] at hout
      | cons entry queue =>
          rcases entry with ⟨current, revPath⟩
          by_cases hgoal : current = goal
          · subst current
            simp [gpBfsAux] at hout
            subst path
            exact hqueue (goal, revPath) (by simp)
          · let fresh :=
              (gpNeighbors st current).filter fun x =>
                !(seen.contains x)
            let newEntries :=
              fresh.map fun x => (x, x :: revPath)
            have hrec :
                gpBfsAux st goal fuel
                    (queue ++ newEntries)
                    (seen ++ fresh) =
                  some path := by
              simpa [gpBfsAux, hgoal, fresh, newEntries] using hout
            apply ih
              (queue := queue ++ newEntries)
              (seen := seen ++ fresh)
              (path := path)
              ?_ hrec
            intro entry hentry
            rcases List.mem_append.mp hentry with hentry | hentry
            · exact hqueue entry (by simp [hentry])
            · rcases List.mem_map.mp hentry with ⟨x, hx, rfl⟩
              have hprefix :
                  GpFullPath st start revPath.reverse current :=
                hqueue (current, revPath) (by simp)
              have hxFilter :
                  x ∈ (gpNeighbors st current).filter
                    (fun y => !(seen.contains y)) := by
                simpa [fresh] using hx
              have hxNeighbor : x ∈ gpNeighbors st current :=
                (List.mem_filter.mp hxFilter).1
              simpa using GpFullPath.snoc hprefix hxNeighbor

lemma gpReachable_mem_of_closed
    {st : StaticState}
    {start goal : Obj}
    {seen : List Obj}
    (hstart : start ∈ seen)
    (hclosed :
      ∀ current, current ∈ seen →
        ∀ next, next ∈ gpNeighbors st current →
          next ∈ seen)
    (hreach :
      Relation.ReflTransGen
        (fun current next => next ∈ gpNeighbors st current)
        start goal) :
    goal ∈ seen := by
  induction hreach with
  | refl =>
      exact hstart
  | tail hprefix hstep ih =>
      exact hclosed _ ih _ hstep

lemma gpBfsAux_complete
    (st : StaticState)
    (goal root : Obj)
    (fuel : Nat)
    (queue : List (Obj × List Obj))
    (seen done : List Obj)
    (hobjects : st.objects.Nodup)
    (hseenEq : seen = done ++ gpQueueNodes queue)
    (hseenNodup : seen.Nodup)
    (hseenObjects : ∀ x ∈ seen, x ∈ st.objects)
    (hclosed :
      ∀ current, current ∈ done →
        ∀ next, next ∈ gpNeighbors st current →
          next ∈ seen)
    (hroot : root ∈ seen)
    (hreach :
      Relation.ReflTransGen
        (fun current next => next ∈ gpNeighbors st current)
        root goal)
    (hgoalDone : goal ∉ done)
    (hbudget : st.objects.length < done.length + fuel) :
    ∃ path, gpBfsAux st goal fuel queue seen = some path := by
  induction fuel generalizing queue seen done with
  | zero =>
      have hdoneNodup : done.Nodup := by
        rw [hseenEq] at hseenNodup
        exact (List.nodup_append.mp hseenNodup).1
      have hsubset :
          done.toFinset ⊆ st.objects.toFinset := by
        intro x hx
        have hxDone : x ∈ done := by
          simpa using hx
        have hxSeen : x ∈ seen := by
          rw [hseenEq]
          exact List.mem_append_left _ hxDone
        have hxObjects := hseenObjects x hxSeen
        simpa using hxObjects
      have hcard := Finset.card_le_card hsubset
      rw [List.toFinset_card_of_nodup hdoneNodup,
          List.toFinset_card_of_nodup hobjects] at hcard
      omega
  | succ fuel ih =>
      cases queue with
      | nil =>
          have hseenDone : seen = done := by
            simpa [gpQueueNodes] using hseenEq
          have hgoalSeen : goal ∈ seen := by
            apply gpReachable_mem_of_closed hroot
            · intro current hcurrent next hnext
              have hcurrentDone : current ∈ done := by
                simpa [hseenDone] using hcurrent
              exact hclosed current hcurrentDone next hnext
            · exact hreach
          have hgoalDone' : goal ∈ done := by
            simpa [hseenDone] using hgoalSeen
          exact (hgoalDone hgoalDone').elim
      | cons entry queue =>
          rcases entry with ⟨current, revPath⟩
          by_cases hcurrentGoal : current = goal
          · subst current
            exact ⟨revPath.reverse, by simp [gpBfsAux]⟩
          · let fresh :=
              (gpNeighbors st current).filter fun x =>
                !(seen.contains x)
            let newEntries :=
              fresh.map fun x => (x, x :: revPath)

            have hcurrentSeen : current ∈ seen := by
              rw [hseenEq]
              simp [gpQueueNodes]

            have hfreshSpec :
                ∀ x, x ∈ fresh ↔
                  x ∈ gpNeighbors st current ∧ x ∉ seen := by
              intro x
              simp [fresh]

            have hfreshNodup : fresh.Nodup := by
              exact (hobjects.filter _).filter _

            have hnewSeenNodup : (seen ++ fresh).Nodup := by
              apply hseenNodup.append hfreshNodup
              intro x hxSeen hxFresh
              exact ((hfreshSpec x).mp hxFresh).2 hxSeen

            have hqueueNodes :
                gpQueueNodes (queue ++ newEntries) =
                  gpQueueNodes queue ++ fresh := by
              simp [gpQueueNodes, newEntries, Function.comp_def]

            have hnewSeenEq :
                seen ++ fresh =
                  (done ++ [current]) ++
                    gpQueueNodes (queue ++ newEntries) := by
              calc
                seen ++ fresh =
                    (done ++ (current :: gpQueueNodes queue)) ++ fresh := by
                      rw [hseenEq]
                      rfl
                _ =
                    (done ++ [current]) ++
                      (gpQueueNodes queue ++ fresh) := by
                      simp [List.append_assoc]
                _ =
                    (done ++ [current]) ++
                      gpQueueNodes (queue ++ newEntries) := by
                      rw [hqueueNodes]

            have hnewSeenObjects :
                ∀ x ∈ seen ++ fresh, x ∈ st.objects := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hseenObjects x hx
              · have hxNeighbor :=
                  ((hfreshSpec x).mp hx).1
                exact (gpNeighbors_mem st current x).mp hxNeighbor |>.1

            have hnewClosed :
                ∀ d, d ∈ done ++ [current] →
                  ∀ next, next ∈ gpNeighbors st d →
                    next ∈ seen ++ fresh := by
              intro d hd next hnext
              rcases List.mem_append.mp hd with hd | hd
              · exact List.mem_append_left _
                  (hclosed d hd next hnext)
              · have hdEq : d = current := by
                  simpa using hd
                subst d
                by_cases hnextSeen : next ∈ seen
                · exact List.mem_append_left _ hnextSeen
                · exact List.mem_append_right _
                    ((hfreshSpec next).mpr ⟨hnext, hnextSeen⟩)

            have hnewRoot : root ∈ seen ++ fresh :=
              List.mem_append_left _ hroot

            have hnewGoalDone :
                goal ∉ done ++ [current] := by
              intro hmem
              rcases List.mem_append.mp hmem with hmem | hmem
              · exact hgoalDone hmem
              · have : goal = current := by
                  simpa using hmem
                exact hcurrentGoal this.symm

            have hnewBudget :
                st.objects.length <
                  (done ++ [current]).length + fuel := by
              simp only [List.length_append, List.length_singleton]
              omega

            rcases ih
                (queue := queue ++ newEntries)
                (seen := seen ++ fresh)
                (done := done ++ [current])
                hnewSeenEq
                hnewSeenNodup
                hnewSeenObjects
                hnewClosed
                hnewRoot
                hnewGoalDone
                hnewBudget with
              ⟨path, hpath⟩

            refine ⟨path, ?_⟩
            simpa [gpBfsAux, hcurrentGoal, fresh, newEntries]
              using hpath

lemma sameBuilding_symm
    (st : StaticState)
    {f1 f2 : Obj}
    (h : SameBuilding st f1 f2) :
    SameBuilding st f2 f1 := by
  have hreverse :
      ∀ a b,
        (st.above_p a b = true ∨ st.above_p b a = true) →
        (st.above_p b a = true ∨ st.above_p a b = true) := by
    intro a b hab
    exact hab.symm
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprefix hlink ih =>
      exact
        sameBuilding_trans st
          (sameBuilding_of_link st (hreverse _ _ hlink))
          ih

lemma sameBuilding_to_neighbors
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    {f1 f2 : Obj}
    (h : SameBuilding st f1 f2) :
    Relation.ReflTransGen
      (fun current next => next ∈ gpNeighbors st current)
      f1 f2 := by
  have hedge :
      ∀ a b,
        (st.above_p a b = true ∨ st.above_p b a = true) →
        b ∈ gpNeighbors st a := by
    intro a b hab
    have hfloorB : st.floor_t b = true := by
      rcases hab with hab | hab
      · exact (hstatic.2.2.1 a b hab).2
      · exact (hstatic.2.2.1 b a hab).1
    have hbObjects : b ∈ st.objects :=
      hstatic.2.2.2.1.2.1 b hfloorB
    exact (gpNeighbors_mem st a b).mpr
      ⟨hbObjects, hfloorB, hab⟩
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprefix hlink ih =>
      exact Relation.ReflTransGen.tail ih (hedge _ _ hlink)

lemma gpFindPath_complete
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    {start goal : Obj}
    (hstartFloor : st.floor_t start = true)
    (hgoalFloor : st.floor_t goal = true)
    (hsame : SameBuilding st start goal) :
    ∃ path,
      gpFindPath st start goal = some path ∧
      ∃ rest,
        path = start :: rest ∧
        GpMovePath st start rest goal := by
  have hreach :
      Relation.ReflTransGen
        (fun current next => next ∈ gpNeighbors st current)
        start goal :=
    sameBuilding_to_neighbors st hstatic hsame

  have hstartObjects : start ∈ st.objects :=
    hstatic.2.2.2.1.2.1 start hstartFloor

  have haux :
      ∃ path,
        gpBfsAux st goal (st.objects.length + 1)
          [(start, [start])] [start] = some path := by
    apply gpBfsAux_complete
      (st := st)
      (goal := goal)
      (root := start)
      (fuel := st.objects.length + 1)
      (queue := [(start, [start])])
      (seen := [start])
      (done := [])
      hstatic.1
    · simp [gpQueueNodes]
    · simp
    · intro x hx
      have hxEq : x = start := by
        simpa using hx
      subst x
      exact hstartObjects
    · simp
    · simp
    · exact hreach
    · simp
    · omega

  rcases haux with ⟨path, hpath⟩

  have hfull : GpFullPath st start path goal := by
    apply gpBfsAux_sound
      (st := st)
      (start := start)
      (goal := goal)
      (fuel := st.objects.length + 1)
      (queue := [(start, [start])])
      (seen := [start])
    · intro entry hentry
      have hentryEq : entry = (start, [start]) := by
        simpa using hentry
      subst entry
      simpa using
        (GpFullPath.single (st := st) (start := start))
    · exact hpath

  rcases gpFullPath_to_movePath hfull with
    ⟨rest, hshape, hmove⟩
  exact ⟨path, hpath, rest, hshape, hmove⟩

lemma gpFind?_sound
    (pred : Obj → Bool)
    (xs : List Obj)
    {x : Obj}
    (h : gpFind? pred xs = some x) :
    x ∈ xs ∧ pred x = true := by
  induction xs with
  | nil =>
      simp [gpFind?] at h
  | cons y ys ih =>
      by_cases hy : pred y = true
      · simp [gpFind?, hy] at h
        subst x
        exact ⟨by simp, hy⟩
      · have htail : gpFind? pred ys = some x := by
          simpa [gpFind?, hy] using h
        rcases ih htail with ⟨hx, hpred⟩
        exact ⟨by simp [hx], hpred⟩

lemma gpFind?_complete
    (pred : Obj → Bool)
    (xs : List Obj)
    (hexists : ∃ x ∈ xs, pred x = true) :
    ∃ x, gpFind? pred xs = some x := by
  induction xs with
  | nil =>
      simp at hexists
  | cons y ys ih =>
      by_cases hy : pred y = true
      · exact ⟨y, by simp [gpFind?, hy]⟩
      · have htail : ∃ x ∈ ys, pred x = true := by
          rcases hexists with ⟨x, hx, hpred⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact (hy hpred).elim
          · exact ⟨x, hx, hpred⟩
        rcases ih htail with ⟨x, hx⟩
        exact ⟨x, by simpa [gpFind?, hy] using hx⟩

lemma gpOrigin_exists
    (s : State)
    (hwf : WellFormed s)
    {p : Obj}
    (horigin : ∃ f, s.dynamic.origin_p p f = true) :
    ∃ f,
      gpOrigin? s p = some f ∧
      s.dynamic.origin_p p f = true := by
  rcases horigin with ⟨f, hf⟩
  have hfloor : s.statics.floor_t f = true :=
    (hwf.2.1 p f hf).2
  have hfObjects : f ∈ s.statics.objects :=
    hwf.1.2.2.2.1.2.1 f hfloor
  rcases gpFind?_complete
      (fun x => s.dynamic.origin_p p x)
      s.statics.objects
      ⟨f, hfObjects, hf⟩ with
    ⟨found, hfound⟩
  have hsound :=
    gpFind?_sound
      (fun x => s.dynamic.origin_p p x)
      s.statics.objects hfound
  exact ⟨found, hfound, hsound.2⟩

lemma gpDestination_exists
    (s : State)
    (hwf : WellFormed s)
    {p : Obj}
    (hpassenger : s.statics.passenger_t p = true) :
    ∃ f,
      gpDestination? s p = some f ∧
      s.statics.destin_p p f = true := by
  have hdestExists : DestinExists s.statics :=
    hwf.1.2.2.2.2.2.2.2.2.2
  rcases hdestExists p hpassenger with ⟨f, hf⟩
  have hfloor : s.statics.floor_t f = true :=
    (hwf.1.2.1 p f hf).2
  have hfObjects : f ∈ s.statics.objects :=
    hwf.1.2.2.2.1.2.1 f hfloor
  rcases gpFind?_complete
      (fun x => s.statics.destin_p p x)
      s.statics.objects
      ⟨f, hfObjects, hf⟩ with
    ⟨found, hfound⟩
  have hsound :=
    gpFind?_sound
      (fun x => s.statics.destin_p p x)
      s.statics.objects hfound
  exact ⟨found, hfound, hsound.2⟩

lemma gpFindLiftPath_complete_of_witness
    (s : State)
    (target witness : Obj)
    (xs : List Obj)
    (hwitness : witness ∈ xs)
    (hlift : s.dynamic.lift_at_p witness = true)
    {path : List Obj}
    (hpath : gpFindPath s.statics witness target = some path) :
    ∃ foundPath,
      gpFindLiftPath s target xs = some foundPath := by
  induction xs with
  | nil =>
      simp at hwitness
  | cons f fs ih =>
      by_cases hflift : s.dynamic.lift_at_p f = true
      · cases hfind : gpFindPath s.statics f target with
        | some found =>
            exact
              ⟨found,
                by simp [gpFindLiftPath, hflift, hfind]⟩
        | none =>
            have hwNe : witness ≠ f := by
              intro heq
              subst witness
              rw [hfind] at hpath
              simp at hpath
            have hwTail : witness ∈ fs := by
              rcases List.mem_cons.mp hwitness with hwEq | hwMem
              · exact (hwNe hwEq).elim
              · exact hwMem
            rcases ih hwTail with ⟨found, hfound⟩
            exact
              ⟨found,
                by simpa [gpFindLiftPath, hflift, hfind]
                  using hfound⟩
      · have hwNe : witness ≠ f := by
          intro heq
          subst witness
          exact hflift hlift
        have hwTail : witness ∈ fs := by
          rcases List.mem_cons.mp hwitness with hwEq | hwMem
          · exact (hwNe hwEq).elim
          · exact hwMem
        rcases ih hwTail with ⟨found, hfound⟩
        exact
          ⟨found,
            by simpa [gpFindLiftPath, hflift] using hfound⟩

lemma gpFindLiftPath_sound
    (s : State)
    (target : Obj)
    (xs : List Obj)
    {path : List Obj}
    (hfound : gpFindLiftPath s target xs = some path) :
    ∃ start rest,
      start ∈ xs ∧
      s.dynamic.lift_at_p start = true ∧
      path = start :: rest ∧
      GpMovePath s.statics start rest target := by
  induction xs with
  | nil =>
      simp [gpFindLiftPath] at hfound
  | cons f fs ih =>
      by_cases hflift : s.dynamic.lift_at_p f = true
      · cases hpath : gpFindPath s.statics f target with
        | some found =>
            have hEq : found = path := by
              simpa [gpFindLiftPath, hflift, hpath] using hfound
            subst path
            have hfull :
                GpFullPath s.statics f found target := by
              apply gpBfsAux_sound
                (st := s.statics)
                (start := f)
                (goal := target)
                (fuel := s.statics.objects.length + 1)
                (queue := [(f, [f])])
                (seen := [f])
              · intro entry hentry
                have hentryEq : entry = (f, [f]) := by
                  simpa using hentry
                subst entry
                simpa using
                  (GpFullPath.single
                    (st := s.statics) (start := f))
              · simpa [gpFindPath] using hpath
            rcases gpFullPath_to_movePath hfull with
              ⟨rest, hshape, hmove⟩
            exact
              ⟨f, rest, by simp, hflift, hshape, hmove⟩
        | none =>
            have htail :
                gpFindLiftPath s target fs = some path := by
              simpa [gpFindLiftPath, hflift, hpath] using hfound
            rcases ih htail with
              ⟨start, rest, hmem, hlift, hshape, hmove⟩
            exact
              ⟨start, rest, by simp [hmem],
                hlift, hshape, hmove⟩
      · have htail :
            gpFindLiftPath s target fs = some path := by
          simpa [gpFindLiftPath, hflift] using hfound
        rcases ih htail with
          ⟨start, rest, hmem, hlift, hshape, hmove⟩
        exact
          ⟨start, rest, by simp [hmem],
            hlift, hshape, hmove⟩

lemma gpMovePath_execute
    (st : StaticState)
    {current target : Obj}
    {rest : List Obj}
    (hpath : GpMovePath st current rest target)
    (s : State)
    (hstatics : s.statics = st)
    (hwf : WellFormed s)
    (hlift : s.dynamic.lift_at_p current = true) :
    ValidPlan (gpPathActionsFrom st current rest) s ∧
    WellFormed (runPlan (gpPathActionsFrom st current rest) s) ∧
    (runPlan (gpPathActionsFrom st current rest) s).dynamic.lift_at_p
      target = true ∧
    (runPlan (gpPathActionsFrom st current rest) s).dynamic.origin_p =
      s.dynamic.origin_p ∧
    (runPlan (gpPathActionsFrom st current rest) s).dynamic.boarded_p =
      s.dynamic.boarded_p ∧
    (runPlan (gpPathActionsFrom st current rest) s).dynamic.served_p =
      s.dynamic.served_p := by
  induction hpath generalizing s with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact True.intro
      · exact hwf
      · exact hlift
      · rfl
      · rfl
      · rfl
  | @cons current next rest target hneighbor htail ih =>
      rcases (gpNeighbors_mem st current next).mp hneighbor with
        ⟨hnextObject, hnextFloor, hlink⟩

      have hcurrentFloorState :
          s.statics.floor_t current = true :=
        hwf.2.2.2.2.1 current hlift
      have hcurrentFloor : st.floor_t current = true := by
        simpa [hstatics] using hcurrentFloorState

      by_cases habove : st.above_p current next = true
      · have hpre : upPre current next s := by
          refine ⟨?_, ?_, hlift, ?_⟩
          · simpa [hstatics] using hcurrentFloor
          · simpa [hstatics] using hnextFloor
          · simpa [hstatics] using habove

        have hwf' : WellFormed (up current next s) :=
          up_preserves_wf current next s hwf hpre

        have hstatics' :
            (up current next s).statics = st :=
          (up_statics current next s).trans hstatics

        have hlift' :
            (up current next s).dynamic.lift_at_p next = true :=
          up_lift_at_p_eq1 current next s

        rcases ih (up current next s) hstatics' hwf' hlift' with
          ⟨hvalid, hwfFinal, hliftFinal,
            horigin, hboarded, hserved⟩

        have hactions :
            gpPathActionsFrom st current (next :: rest) =
              PlanAction.up current next ::
                gpPathActionsFrom st next rest := by
          simp [gpPathActionsFrom, habove]

        rw [hactions]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · change
            upPre current next s ∧
              ValidPlan (gpPathActionsFrom st next rest)
                (up current next s)
          exact ⟨hpre, hvalid⟩
        · change
            WellFormed
              (runPlan (gpPathActionsFrom st next rest)
                (up current next s))
          exact hwfFinal
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (up current next s)).dynamic.lift_at_p target = true
          exact hliftFinal
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (up current next s)).dynamic.origin_p =
                s.dynamic.origin_p
          calc
            _ = (up current next s).dynamic.origin_p := horigin
            _ = s.dynamic.origin_p := up_origin_p current next s
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (up current next s)).dynamic.boarded_p =
                s.dynamic.boarded_p
          calc
            _ = (up current next s).dynamic.boarded_p := hboarded
            _ = s.dynamic.boarded_p := up_boarded_p current next s
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (up current next s)).dynamic.served_p =
                s.dynamic.served_p
          calc
            _ = (up current next s).dynamic.served_p := hserved
            _ = s.dynamic.served_p := up_served_p current next s

      · have hbelow : st.above_p next current = true := by
          rcases hlink with h | h
          · exact (habove h).elim
          · exact h

        have hpre : downPre current next s := by
          refine ⟨?_, ?_, hlift, ?_⟩
          · simpa [hstatics] using hcurrentFloor
          · simpa [hstatics] using hnextFloor
          · simpa [hstatics] using hbelow

        have hwf' : WellFormed (down current next s) :=
          down_preserves_wf current next s hwf hpre

        have hstatics' :
            (down current next s).statics = st :=
          (down_statics current next s).trans hstatics

        have hlift' :
            (down current next s).dynamic.lift_at_p next = true :=
          down_lift_at_p_eq1 current next s

        rcases ih (down current next s) hstatics' hwf' hlift' with
          ⟨hvalid, hwfFinal, hliftFinal,
            horigin, hboarded, hserved⟩

        have hactions :
            gpPathActionsFrom st current (next :: rest) =
              PlanAction.down current next ::
                gpPathActionsFrom st next rest := by
          simp [gpPathActionsFrom, habove]

        rw [hactions]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · change
            downPre current next s ∧
              ValidPlan (gpPathActionsFrom st next rest)
                (down current next s)
          exact ⟨hpre, hvalid⟩
        · change
            WellFormed
              (runPlan (gpPathActionsFrom st next rest)
                (down current next s))
          exact hwfFinal
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (down current next s)).dynamic.lift_at_p target = true
          exact hliftFinal
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (down current next s)).dynamic.origin_p =
                s.dynamic.origin_p
          calc
            _ = (down current next s).dynamic.origin_p := horigin
            _ = s.dynamic.origin_p := down_origin_p current next s
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (down current next s)).dynamic.boarded_p =
                s.dynamic.boarded_p
          calc
            _ = (down current next s).dynamic.boarded_p := hboarded
            _ = s.dynamic.boarded_p := down_boarded_p current next s
        · change
            (runPlan (gpPathActionsFrom st next rest)
              (down current next s)).dynamic.served_p =
                s.dynamic.served_p
          calc
            _ = (down current next s).dynamic.served_p := hserved
            _ = s.dynamic.served_p := down_served_p current next s

lemma gpMoveTo_correct
    (s : State)
    (target : Obj)
    (hwf : WellFormed s)
    (htargetFloor : s.statics.floor_t target = true) :
    ValidPlan (gpMoveTo s target).1 s ∧
    runPlan (gpMoveTo s target).1 s = (gpMoveTo s target).2 ∧
    WellFormed (gpMoveTo s target).2 ∧
    (gpMoveTo s target).2.dynamic.lift_at_p target = true ∧
    (gpMoveTo s target).2.dynamic.origin_p =
      s.dynamic.origin_p ∧
    (gpMoveTo s target).2.dynamic.boarded_p =
      s.dynamic.boarded_p ∧
    (gpMoveTo s target).2.dynamic.served_p =
      s.dynamic.served_p := by
  rcases hwf.2.2.2.2.2.2.2.2 target htargetFloor with
    ⟨witness, hsame, hlift⟩

  have hwitnessFloor :
      s.statics.floor_t witness = true :=
    hwf.2.2.2.2.1 witness hlift

  have hwitnessObjects :
      witness ∈ s.statics.objects :=
    hwf.1.2.2.2.1.2.1 witness hwitnessFloor

  have hreverse :
      SameBuilding s.statics witness target :=
    sameBuilding_symm s.statics hsame

  rcases gpFindPath_complete
      s.statics hwf.1 hwitnessFloor htargetFloor hreverse with
    ⟨path, hpath, rest, hshape, hmove⟩

  rcases gpFindLiftPath_complete_of_witness
      s target witness s.statics.objects
      hwitnessObjects hlift hpath with
    ⟨foundPath, hfound⟩

  rcases gpFindLiftPath_sound
      s target s.statics.objects hfound with
    ⟨start, foundRest, hstartMem, hstartLift,
      hfoundShape, hfoundMove⟩

  subst foundPath

  rcases gpMovePath_execute
      s.statics hfoundMove s rfl hwf hstartLift with
    ⟨hvalid, hwfFinal, hliftFinal,
      horigin, hboarded, hserved⟩

  unfold gpMoveTo
  rw [hfound]
  dsimp only
  simp only [gpPathActions]
  exact
    ⟨hvalid, True.intro, hwfFinal, hliftFinal,
      horigin, hboarded, hserved⟩

lemma gpServePassenger_correct
    (p : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hpassenger : s.statics.passenger_t p = true)
    (horiginExists : ∃ f, s.dynamic.origin_p p f = true)
    (hboardedFalse : s.dynamic.boarded_p p = false) :
    ValidPlan (gpServePassenger p s).1 s ∧
    runPlan (gpServePassenger p s).1 s =
      (gpServePassenger p s).2 ∧
    WellFormed (gpServePassenger p s).2 ∧
    (gpServePassenger p s).2.dynamic.served_p p = true ∧
    (∀ q, q ≠ p →
      (gpServePassenger p s).2.dynamic.served_p q =
        s.dynamic.served_p q) ∧
    (∀ q, q ≠ p →
      (gpServePassenger p s).2.dynamic.boarded_p q =
        s.dynamic.boarded_p q) ∧
    (∀ q f, q ≠ p →
      (gpServePassenger p s).2.dynamic.origin_p q f =
        s.dynamic.origin_p q f) := by
  rcases gpOrigin_exists s hwf horiginExists with
    ⟨origin, horiginFind, horiginTrue⟩
  rcases gpDestination_exists s hwf hpassenger with
    ⟨destination, hdestFind, hdestTrue⟩

  have horiginFloor :
      s.statics.floor_t origin = true :=
    (hwf.2.1 p origin horiginTrue).2
  have hdestFloor :
      s.statics.floor_t destination = true :=
    (hwf.1.2.1 p destination hdestTrue).2

  rcases gpMoveTo_correct s origin hwf horiginFloor with
    ⟨hvalidOrigin, hrunOrigin, hwfOrigin, hliftOrigin,
      horiginOrigin, hboardedOrigin, hservedOrigin⟩

  have hstaticsOrigin :
      (gpMoveTo s origin).2.statics = s.statics := by
    calc
      (gpMoveTo s origin).2.statics =
          (runPlan (gpMoveTo s origin).1 s).statics := by
            exact congrArg State.statics hrunOrigin |>.symm
      _ = s.statics :=
        runPlan_statics (gpMoveTo s origin).1 s

  have hboardPre :
      boardPre origin p (gpMoveTo s origin).2 := by
    refine ⟨?_, ?_, hliftOrigin, ?_⟩
    · rw [hstaticsOrigin]
      exact horiginFloor
    · rw [hstaticsOrigin]
      exact hpassenger
    · exact congrFun (congrFun horiginOrigin p) origin ▸ horiginTrue

  have hwfBoarded :
      WellFormed (board origin p (gpMoveTo s origin).2) :=
    board_preserves_wf
      origin p (gpMoveTo s origin).2 hwfOrigin hboardPre

  have hboardedTrue :
      (board origin p (gpMoveTo s origin).2).dynamic.boarded_p p =
        true :=
    board_boarded_p_eq1 origin p (gpMoveTo s origin).2

  have hdestFloorBoarded :
      (board origin p (gpMoveTo s origin).2).statics.floor_t
        destination = true := by
    change
      (gpMoveTo s origin).2.statics.floor_t destination = true
    rw [hstaticsOrigin]
    exact hdestFloor

  rcases gpMoveTo_correct
      (board origin p (gpMoveTo s origin).2)
      destination hwfBoarded hdestFloorBoarded with
    ⟨hvalidDestination, hrunDestination, hwfDestination,
      hliftDestination, horiginDestination,
      hboardedDestination, hservedDestination⟩

  have hstaticsDestination :
      (gpMoveTo
        (board origin p (gpMoveTo s origin).2)
        destination).2.statics = s.statics := by
    calc
      (gpMoveTo
        (board origin p (gpMoveTo s origin).2)
        destination).2.statics =
          (runPlan
            (gpMoveTo
              (board origin p (gpMoveTo s origin).2)
              destination).1
            (board origin p (gpMoveTo s origin).2)).statics := by
              exact congrArg State.statics hrunDestination |>.symm
      _ =
          (board origin p (gpMoveTo s origin).2).statics :=
            runPlan_statics
              (gpMoveTo
                (board origin p (gpMoveTo s origin).2)
                destination).1
              (board origin p (gpMoveTo s origin).2)
      _ = (gpMoveTo s origin).2.statics :=
            board_statics origin p (gpMoveTo s origin).2
      _ = s.statics := hstaticsOrigin

  have hdepartPre :
      departPre destination p
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2 := by
    refine ⟨?_, ?_, hliftDestination, ?_, ?_⟩
    · rw [hstaticsDestination]
      exact hdestFloor
    · rw [hstaticsDestination]
      exact hpassenger
    · rw [hstaticsDestination]
      exact hdestTrue
    · exact
        congrFun hboardedDestination p ▸ hboardedTrue

  have hwfFinal :
      WellFormed
        (depart destination p
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2) :=
    depart_preserves_wf
      destination p
      (gpMoveTo
        (board origin p (gpMoveTo s origin).2)
        destination).2
      hwfDestination hdepartPre

  have hvalidBoard :
      ValidPlan [PlanAction.board origin p]
        (gpMoveTo s origin).2 := by
    exact ⟨hboardPre, True.intro⟩

  have hvalidDepart :
      ValidPlan [PlanAction.depart destination p]
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2 := by
    exact ⟨hdepartPre, True.intro⟩

  have hvalidDestinationDepart :
      ValidPlan
        ((gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).1 ++
          [PlanAction.depart destination p])
        (board origin p (gpMoveTo s origin).2) := by
    apply
      (validPlan_append
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).1
        [PlanAction.depart destination p]
        (board origin p (gpMoveTo s origin).2)).2
    refine ⟨hvalidDestination, ?_⟩
    rw [hrunDestination]
    exact hvalidDepart

  have hvalidBoardTail :
      ValidPlan
        ([PlanAction.board origin p] ++
          ((gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).1 ++
            [PlanAction.depart destination p]))
        (gpMoveTo s origin).2 := by
    apply
      (validPlan_append
        [PlanAction.board origin p]
        ((gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).1 ++
          [PlanAction.depart destination p])
        (gpMoveTo s origin).2).2
    refine ⟨hvalidBoard, ?_⟩
    change
      ValidPlan
        ((gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).1 ++
          [PlanAction.depart destination p])
        (board origin p (gpMoveTo s origin).2)
    exact hvalidDestinationDepart

  have hvalidAll :
      ValidPlan
        ((gpMoveTo s origin).1 ++
          ([PlanAction.board origin p] ++
            ((gpMoveTo
              (board origin p (gpMoveTo s origin).2)
              destination).1 ++
              [PlanAction.depart destination p])))
        s := by
    apply
      (validPlan_append
        (gpMoveTo s origin).1
        ([PlanAction.board origin p] ++
          ((gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).1 ++
            [PlanAction.depart destination p]))
        s).2
    refine ⟨hvalidOrigin, ?_⟩
    rw [hrunOrigin]
    exact hvalidBoardTail

  have hrunAll :
      runPlan
        ((gpMoveTo s origin).1 ++
          ([PlanAction.board origin p] ++
            ((gpMoveTo
              (board origin p (gpMoveTo s origin).2)
              destination).1 ++
              [PlanAction.depart destination p])))
        s =
      depart destination p
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2 := by
    rw [runPlan_append, hrunOrigin]
    change
      runPlan
        ((gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).1 ++
          [PlanAction.depart destination p])
        (board origin p (gpMoveTo s origin).2) =
      depart destination p
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2
    rw [runPlan_append, hrunDestination]
    rfl

  have hservedP :
      (depart destination p
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2).dynamic.served_p p = true :=
    depart_served_p_eq1 destination p
      (gpMoveTo
        (board origin p (gpMoveTo s origin).2)
        destination).2

  have hservedOther :
      ∀ q, q ≠ p →
        (depart destination p
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2).dynamic.served_p q =
          s.dynamic.served_p q := by
    intro q hqp
    calc
      _ =
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2.dynamic.served_p q :=
        depart_served_p_ne destination p _ hqp
      _ =
          (board origin p
            (gpMoveTo s origin).2).dynamic.served_p q :=
        congrFun hservedDestination q
      _ = (gpMoveTo s origin).2.dynamic.served_p q := rfl
      _ = s.dynamic.served_p q :=
        congrFun hservedOrigin q

  have hboardedOther :
      ∀ q, q ≠ p →
        (depart destination p
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2).dynamic.boarded_p q =
          s.dynamic.boarded_p q := by
    intro q hqp
    calc
      _ =
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2.dynamic.boarded_p q :=
        depart_boarded_p_ne destination p _ hqp
      _ =
          (board origin p
            (gpMoveTo s origin).2).dynamic.boarded_p q :=
        congrFun hboardedDestination q
      _ = (gpMoveTo s origin).2.dynamic.boarded_p q :=
        board_boarded_p_ne origin p _ hqp
      _ = s.dynamic.boarded_p q :=
        congrFun hboardedOrigin q

  have horiginOther :
      ∀ q f, q ≠ p →
        (depart destination p
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2).dynamic.origin_p q f =
          s.dynamic.origin_p q f := by
    intro q f hqp
    calc
      _ =
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).2.dynamic.origin_p q f := rfl
      _ =
          (board origin p
            (gpMoveTo s origin).2).dynamic.origin_p q f :=
        congrFun (congrFun horiginDestination q) f
      _ = (gpMoveTo s origin).2.dynamic.origin_p q f :=
        board_origin_p_ne origin p _ hqp
      _ = s.dynamic.origin_p q f :=
        congrFun (congrFun horiginOrigin q) f

  unfold gpServePassenger
  rw [horiginFind, hdestFind]
  dsimp only
  refine
    ⟨?_, ?_, hwfFinal, hservedP,
      hservedOther, hboardedOther, horiginOther⟩
  · change
      ValidPlan
        ((gpMoveTo s origin).1 ++
          [PlanAction.board origin p] ++
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).1 ++
          [PlanAction.depart destination p])
        s
    simpa only [List.append_assoc] using hvalidAll
  · change
      runPlan
        ((gpMoveTo s origin).1 ++
          [PlanAction.board origin p] ++
          (gpMoveTo
            (board origin p (gpMoveTo s origin).2)
            destination).1 ++
          [PlanAction.depart destination p])
        s =
      depart destination p
        (gpMoveTo
          (board origin p (gpMoveTo s origin).2)
          destination).2
    simpa only [List.append_assoc] using hrunAll

lemma gpServePassengers_correct
    (ps : List Obj)
    (s : State)
    (hwf : WellFormed s)
    (hnodup : ps.Nodup)
    (hpassengers :
      ∀ p ∈ ps, s.statics.passenger_t p = true)
    (horigins :
      ∀ p ∈ ps, ∃ f, s.dynamic.origin_p p f = true)
    (hboarded :
      ∀ p ∈ ps, s.dynamic.boarded_p p = false) :
    ValidPlan (gpServePassengers ps s).1 s ∧
    runPlan (gpServePassengers ps s).1 s =
      (gpServePassengers ps s).2 ∧
    WellFormed (gpServePassengers ps s).2 ∧
    (∀ p ∈ ps,
      (gpServePassengers ps s).2.dynamic.served_p p = true) ∧
    (∀ q, q ∉ ps →
      (gpServePassengers ps s).2.dynamic.served_p q =
        s.dynamic.served_p q) := by
  induction ps generalizing s with
  | nil =>
      simp only [gpServePassengers]
      refine ⟨True.intro, rfl, hwf, ?_, ?_⟩
      · simp
      · intro q hq
        exact True.intro

  | cons p ps ih =>
      have hpNotMem : p ∉ ps :=
        (List.nodup_cons.mp hnodup).1
      have hpsNodup : ps.Nodup :=
        (List.nodup_cons.mp hnodup).2

      have hpPassenger :
          s.statics.passenger_t p = true :=
        hpassengers p (by simp)
      have hpOrigin :
          ∃ f, s.dynamic.origin_p p f = true :=
        horigins p (by simp)
      have hpBoarded :
          s.dynamic.boarded_p p = false :=
        hboarded p (by simp)

      rcases gpServePassenger_correct
          p s hwf hpPassenger hpOrigin hpBoarded with
        ⟨hvalidCurrent, hrunCurrent, hwfNext, hpServed,
          hservedNe, hboardedNe, horiginNe⟩

      have hnextStatics :
          (gpServePassenger p s).2.statics = s.statics := by
        calc
          (gpServePassenger p s).2.statics =
              (runPlan (gpServePassenger p s).1 s).statics := by
                exact congrArg State.statics hrunCurrent |>.symm
          _ = s.statics :=
            runPlan_statics (gpServePassenger p s).1 s

      have hpassengersTail :
          ∀ q ∈ ps,
            (gpServePassenger p s).2.statics.passenger_t q = true := by
        intro q hq
        rw [hnextStatics]
        exact hpassengers q (by simp [hq])

      have horiginsTail :
          ∀ q ∈ ps,
            ∃ f, (gpServePassenger p s).2.dynamic.origin_p q f =
              true := by
        intro q hq
        rcases horigins q (by simp [hq]) with ⟨f, hf⟩
        have hqNe : q ≠ p := by
          intro heq
          subst q
          exact hpNotMem hq
        exact ⟨f, by rw [horiginNe q f hqNe]; exact hf⟩

      have hboardedTail :
          ∀ q ∈ ps,
            (gpServePassenger p s).2.dynamic.boarded_p q = false := by
        intro q hq
        have hqNe : q ≠ p := by
          intro heq
          subst q
          exact hpNotMem hq
        rw [hboardedNe q hqNe]
        exact hboarded q (by simp [hq])

      rcases ih
          (gpServePassenger p s).2
          hwfNext hpsNodup
          hpassengersTail horiginsTail hboardedTail with
        ⟨hvalidRemaining, hrunRemaining, hwfFinal,
          hservedTail, hservedOutside⟩

      have hvalidAll :
          ValidPlan
            ((gpServePassenger p s).1 ++
              (gpServePassengers ps
                (gpServePassenger p s).2).1)
            s := by
        apply
          (validPlan_append
            (gpServePassenger p s).1
            (gpServePassengers ps
              (gpServePassenger p s).2).1
            s).2
        refine ⟨hvalidCurrent, ?_⟩
        rw [hrunCurrent]
        exact hvalidRemaining

      have hrunAll :
          runPlan
            ((gpServePassenger p s).1 ++
              (gpServePassengers ps
                (gpServePassenger p s).2).1)
            s =
          (gpServePassengers ps
            (gpServePassenger p s).2).2 := by
        rw [runPlan_append, hrunCurrent, hrunRemaining]

      have hservedAll :
          ∀ q ∈ p :: ps,
            (gpServePassengers ps
              (gpServePassenger p s).2).2.dynamic.served_p q =
              true := by
        intro q hq
        rcases List.mem_cons.mp hq with hqp | hqTail
        · subst q
          rw [hservedOutside p hpNotMem]
          exact hpServed
        · exact hservedTail q hqTail

      have hservedOther :
          ∀ q, q ∉ p :: ps →
            (gpServePassengers ps
              (gpServePassenger p s).2).2.dynamic.served_p q =
              s.dynamic.served_p q := by
        intro q hq
        have hqNe : q ≠ p := by
          intro heq
          subst q
          exact hq (by simp)
        have hqTail : q ∉ ps := by
          intro hmem
          exact hq (by simp [hmem])
        calc
          _ = (gpServePassenger p s).2.dynamic.served_p q :=
            hservedOutside q hqTail
          _ = s.dynamic.served_p q :=
            hservedNe q hqNe

      simp only [gpServePassengers]
      exact
        ⟨hvalidAll, hrunAll, hwfFinal,
          hservedAll, hservedOther⟩

-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  rcases hinit with
    ⟨hwf, hnoneBoarded, hnoneServed, heveryOrigin⟩

  rcases hgoal with
    ⟨hgoalStatic, hgoalOriginValid, hgoalBoardedValid,
      hgoalServedValid, hgoalLiftValid, hgoalOriginFunctional,
      hgoalNoOrigin, hgoalLiftUnique, hignoreOrigin,
      hignoreBoarded, hignoreLift, hservedPositive,
      heveryServed⟩

  let passengers :=
    s.statics.objects.filter fun p =>
      s.statics.passenger_t p

  have hpassengersNodup : passengers.Nodup := by
    exact hwf.1.1.filter _

  have hpassengerTypes :
      ∀ p ∈ passengers,
        s.statics.passenger_t p = true := by
    intro p hp
    have hpFilter :
        p ∈ s.statics.objects.filter
          (fun q => s.statics.passenger_t q) := by
      simpa [passengers] using hp
    exact (List.mem_filter.mp hpFilter).2

  have hpassengerOrigins :
      ∀ p ∈ passengers,
        ∃ f, s.dynamic.origin_p p f = true := by
    intro p hp
    exact heveryOrigin p (hpassengerTypes p hp)

  have hpassengerBoarded :
      ∀ p ∈ passengers,
        s.dynamic.boarded_p p = false := by
    intro p hp
    exact hnoneBoarded p (hpassengerTypes p hp)

  rcases gpServePassengers_correct
      passengers s hwf hpassengersNodup
      hpassengerTypes hpassengerOrigins hpassengerBoarded with
    ⟨hvalid, hrun, hwfFinal, hservedAll, hservedOutside⟩

  have hsolve :
      solve s g = (gpServePassengers passengers s).1 := by
    rfl

  have hfinalServed :
      ∀ p, s.statics.passenger_t p = true →
        (runPlan (solve s g) s).dynamic.served_p p = true := by
    intro p hp
    have hpObjects : p ∈ s.statics.objects :=
      hwf.1.2.2.2.1.1 p hp
    have hpPassengers : p ∈ passengers := by
      apply List.mem_filter.mpr
      exact ⟨hpObjects, hp⟩
    rw [hsolve, hrun]
    exact hservedAll p hpPassengers

  refine ⟨?_, ?_⟩
  · rw [hsolve]
    exact hvalid
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro p f
      rw [hignoreOrigin p f]
      trivial
    · intro p
      rw [hignoreBoarded p]
      trivial
    · intro p
      cases hserved : g.dynamic.served_p p with
      | none =>
          trivial
      | some b =>
          cases b with
          | false =>
              exact (hservedPositive p hserved).elim
          | true =>
              have hpPassenger :
                  s.statics.passenger_t p = true := by
                apply hgoalServedValid p
                change g.dynamic.served_p p = some true
                exact hserved
              simpa [hserved] using
                hfinalServed p hpPassenger
    · intro f
      rw [hignoreLift f]
      trivial

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)
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
  room_t : Obj → Bool
  obj_t : Obj → Bool
  robot_t : Obj → Bool
  gripper_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_robby_p : Obj → Obj → α
  at_p : Obj → Obj → α
  free_p : Obj → Obj → α
  carry_p : Obj → Obj → Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.room_t x = true → x ∈ s.objects) ∧
  (∀ x, s.obj_t x = true → x ∈ s.objects) ∧
  (∀ x, s.robot_t x = true → x ∈ s.objects) ∧
  (∀ x, s.gripper_t x = true → x ∈ s.objects) ∧
  (∀ x, s.room_t x = true → s.obj_t x = false) ∧
  (∀ x, s.room_t x = true → s.robot_t x = false) ∧
  (∀ x, s.room_t x = true → s.gripper_t x = false) ∧
  (∀ x, s.obj_t x = true → s.robot_t x = false) ∧
  (∀ x, s.obj_t x = true → s.gripper_t x = false) ∧
  (∀ x, s.robot_t x = true → s.gripper_t x = false)

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects →
    (s.room_t x = true ∨ s.robot_t x = true ∨ s.gripper_t x = true ∨ s.obj_t x = true)

def MinObj (s : StaticState) : Prop :=
  (∃ x, s.room_t x = true) ∧
  (∃ x, s.obj_t x = true) ∧
  (∃ x, s.robot_t x = true) ∧
  (∃ x y, s.gripper_t x = true ∧ s.gripper_t y = true ∧ x ≠ y)

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidTypeHierarchy s ∧
  TypeCoverage s ∧
  MinObj s

def ValidAtRobbyParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_x, Truthy.isTrue (d.at_robby_p var_r var_x) → s.robot_t var_r = true ∧ s.room_t var_x = true

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_o var_x, Truthy.isTrue (d.at_p var_o var_x) → s.obj_t var_o = true ∧ s.room_t var_x = true

def ValidFreeParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_g, Truthy.isTrue (d.free_p var_r var_g) → s.robot_t var_r = true ∧ s.gripper_t var_g = true

def ValidCarryParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_o var_g, Truthy.isTrue (d.carry_p var_r var_o var_g) → s.robot_t var_r = true ∧ s.obj_t var_o = true ∧ s.gripper_t var_g = true

def AtRobbyMostOneRoom {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r room1 room2, Truthy.isTrue (d.at_robby_p r room1) → Truthy.isTrue (d.at_robby_p r room2) → room1 = room2

def AtMostOneRoom {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o room1 room2, Truthy.isTrue (d.at_p o room1) → Truthy.isTrue (d.at_p o room2) → room1 = room2

def AtCarryExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o room r g, ¬ (Truthy.isTrue (d.at_p o room) ∧ Truthy.isTrue (d.carry_p r o g))

def FreeCarryExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r g o, ¬ (Truthy.isTrue (d.free_p r g) ∧ Truthy.isTrue (d.carry_p r o g))

def CarryUniqueObjectPerGripper {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r g o1 o2, Truthy.isTrue (d.carry_p r o1 g) → Truthy.isTrue (d.carry_p r o2 g) → o1 = o2

def CarryUniqueCarrier {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o r1 g1 r2 g2, Truthy.isTrue (d.carry_p r1 o g1) → Truthy.isTrue (d.carry_p r2 o g2) → r1 = r2 ∧ g1 = g2

def RobotHasLocation (s : State) : Prop :=
  ∀ r, s.statics.robot_t r = true → ∃ room, s.dynamic.at_robby_p r room = true

def ObjectHasLocation (s : State) : Prop :=
  ∀ o, s.statics.obj_t o = true →
    (∃ room, s.dynamic.at_p o room = true) ∨ (∃ r g, s.dynamic.carry_p r o g = true)

def GripperFreeOrCarrying (s : State) : Prop :=
  ∀ r g, s.statics.robot_t r = true → s.statics.gripper_t g = true →
    (s.dynamic.free_p r g = true ∨ ∃ o, s.dynamic.carry_p r o g = true)

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidAtRobbyParam s.statics s.dynamic ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidFreeParam s.statics s.dynamic ∧
  ValidCarryParam s.statics s.dynamic ∧
  AtRobbyMostOneRoom s.statics s.dynamic ∧
  AtMostOneRoom s.statics s.dynamic ∧
  AtCarryExclusive s.statics s.dynamic ∧
  FreeCarryExclusive s.statics s.dynamic ∧
  CarryUniqueObjectPerGripper s.statics s.dynamic ∧
  CarryUniqueCarrier s.statics s.dynamic ∧
  RobotHasLocation s ∧
  ObjectHasLocation s ∧
  GripperFreeOrCarrying s

def InitAllGrippersFree (s : State) : Prop :=
  ∀ r g, s.statics.robot_t r = true → s.statics.gripper_t g = true → s.dynamic.free_p r g = true

def InitTwoFreeGrippersPerRobot (s : State) : Prop :=
  ∀ r, s.statics.robot_t r = true →
    ∃ g1 g2, s.statics.gripper_t g1 = true ∧ s.statics.gripper_t g2 = true ∧
      g1 ≠ g2 ∧ s.dynamic.free_p r g1 = true ∧ s.dynamic.free_p r g2 = true

def InitGrippersPartitionedByRobot (s : State) : Prop :=
  ∀ r1 r2 g, r1 ≠ r2 →
    s.statics.robot_t r1 = true → s.statics.robot_t r2 = true →
    s.statics.gripper_t g = true →
    ¬ (s.dynamic.free_p r1 g = true ∧ s.dynamic.free_p r2 g = true)

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitAllGrippersFree s ∧
  InitTwoFreeGrippersPerRobot s ∧
  InitGrippersPartitionedByRobot s

def GoalIgnoreAtRobby (initial : State) (g : Goal) : Prop :=
  ∀ r room, g.dynamic.at_robby_p r room = none

def GoalIgnoreFree (initial : State) (g : Goal) : Prop :=
  ∀ r gr, g.dynamic.free_p r gr = none

def GoalIgnoreCarry (initial : State) (g : Goal) : Prop :=
  ∀ r o gr, g.dynamic.carry_p r o gr = none

def GoalAtOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ o room, g.dynamic.at_p o room ≠ some false

def GoalEveryObjectHasTarget (initial : State) (g : Goal) : Prop :=
  ∀ o, initial.statics.obj_t o = true → ∃ room, g.dynamic.at_p o room = some true

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidAtRobbyParam initial.statics g.dynamic ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidFreeParam initial.statics g.dynamic ∧
  ValidCarryParam initial.statics g.dynamic ∧
  AtRobbyMostOneRoom initial.statics g.dynamic ∧
  AtMostOneRoom initial.statics g.dynamic ∧
  AtCarryExclusive initial.statics g.dynamic ∧
  FreeCarryExclusive initial.statics g.dynamic ∧
  CarryUniqueObjectPerGripper initial.statics g.dynamic ∧
  CarryUniqueCarrier initial.statics g.dynamic ∧
  GoalIgnoreAtRobby initial g ∧
  GoalIgnoreFree initial g ∧
  GoalIgnoreCarry initial g ∧
  GoalAtOnlyPositive initial g ∧
  GoalEveryObjectHasTarget initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_r var_x,
    match g.dynamic.at_robby_p var_r var_x with
    | none => True
    | some b => s.dynamic.at_robby_p var_r var_x = b) ∧
  (∀ var_o var_x,
    match g.dynamic.at_p var_o var_x with
    | none => True
    | some b => s.dynamic.at_p var_o var_x = b) ∧
  (∀ var_r var_g,
    match g.dynamic.free_p var_r var_g with
    | none => True
    | some b => s.dynamic.free_p var_r var_g = b) ∧
  (∀ var_r var_o var_g,
    match g.dynamic.carry_p var_r var_o var_g with
    | none => True
    | some b => s.dynamic.carry_p var_r var_o var_g = b)

def movePre (var_r : Obj) (var_from : Obj) (var_to : Obj) (s : State) : Prop :=
  s.statics.robot_t var_r = true ∧
  s.statics.room_t var_from = true ∧
  s.statics.room_t var_to = true ∧
  s.dynamic.at_robby_p var_r var_from = true

def pickPre (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj) (s : State) : Prop :=
  s.statics.robot_t var_r = true ∧
  s.statics.obj_t var_obj = true ∧
  s.statics.room_t var_room = true ∧
  s.statics.gripper_t var_g = true ∧
  s.dynamic.at_p var_obj var_room = true ∧
  s.dynamic.at_robby_p var_r var_room = true ∧
  s.dynamic.free_p var_r var_g = true

def dropPre (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj) (s : State) : Prop :=
  s.statics.robot_t var_r = true ∧
  s.statics.obj_t var_obj = true ∧
  s.statics.room_t var_room = true ∧
  s.statics.gripper_t var_g = true ∧
  s.dynamic.carry_p var_r var_obj var_g = true ∧
  s.dynamic.at_robby_p var_r var_room = true

def move (var_r : Obj) (var_from : Obj) (var_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_robby_p :=
      fun var_r' var_to' =>
        if var_r' = var_r ∧ var_to' = var_to then
          true
        else if var_r' = var_r ∧ var_to' = var_from then
          false
        else
          s.dynamic.at_robby_p var_r' var_to'
  }
}

def pick (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_room' =>
        if var_obj' = var_obj ∧ var_room' = var_room then
          false
        else
          s.dynamic.at_p var_obj' var_room',
    free_p :=
      fun var_r' var_g' =>
        if var_r' = var_r ∧ var_g' = var_g then
          false
        else
          s.dynamic.free_p var_r' var_g',
    carry_p :=
      fun var_r' var_obj' var_g' =>
        if var_r' = var_r ∧ var_obj' = var_obj ∧ var_g' = var_g then
          true
        else
          s.dynamic.carry_p var_r' var_obj' var_g'
  }
}

def drop (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_room' =>
        if var_obj' = var_obj ∧ var_room' = var_room then
          true
        else
          s.dynamic.at_p var_obj' var_room',
    free_p :=
      fun var_r' var_g' =>
        if var_r' = var_r ∧ var_g' = var_g then
          true
        else
          s.dynamic.free_p var_r' var_g',
    carry_p :=
      fun var_r' var_obj' var_g' =>
        if var_r' = var_r ∧ var_obj' = var_obj ∧ var_g' = var_g then
          false
        else
          s.dynamic.carry_p var_r' var_obj' var_g'
  }
}

inductive PlanAction where
  | move (var_r : Obj) (var_from : Obj) (var_to : Obj)
  | pick (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj)
  | drop (var_r : Obj) (var_obj : Obj) (var_room : Obj) (var_g : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .move var_r var_from var_to       , s => movePre var_r var_from var_to s
  | .pick var_r var_obj var_room var_g, s => pickPre var_r var_obj var_room var_g s
  | .drop var_r var_obj var_room var_g, s => dropPre var_r var_obj var_room var_g s

def actionApply : PlanAction → State → State
  | .move var_r var_from var_to       , s => move var_r var_from var_to s
  | .pick var_r var_obj var_room var_g, s => pick var_r var_obj var_room var_g s
  | .drop var_r var_obj var_room var_g, s => drop var_r var_obj var_room var_g s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Return the first object in a list satisfying a Boolean predicate.
def gpFind? (p : Obj → Bool) : List Obj → Option Obj
  | [] => none
  | x :: xs =>
      if p x then some x else gpFind? p xs

def gpObjectRoom? (s : State) (o : Obj) : Option Obj :=
  gpFind?
    (fun room =>
      s.statics.room_t room &&
      s.dynamic.at_p o room)
    s.statics.objects

def gpGoalRoom? (s : State) (g : Goal) (o : Obj) : Option Obj :=
  gpFind?
    (fun room =>
      s.statics.room_t room &&
      match g.dynamic.at_p o room with
      | some true => true
      | _ => false)
    s.statics.objects

def gpRobot? (s : State) : Option Obj :=
  gpFind?
    (fun r => s.statics.robot_t r)
    s.statics.objects

def gpRobotRoom? (s : State) (r : Obj) : Option Obj :=
  gpFind?
    (fun room =>
      s.statics.room_t room &&
      s.dynamic.at_robby_p r room)
    s.statics.objects

def gpFreeGripper? (s : State) (r : Obj) : Option Obj :=
  gpFind?
    (fun gripper =>
      s.statics.gripper_t gripper &&
      s.dynamic.free_p r gripper)
    s.statics.objects

-- Construct the actions needed to place one object in its goal room.
def gpPlanObject (o : Obj) (s : State) (g : Goal) : List PlanAction :=
  if s.statics.obj_t o then
    match gpObjectRoom? s o, gpGoalRoom? s g o, gpRobot? s with
    | some objectRoom, some goalRoom, some robot =>
        if objectRoom = goalRoom then
          []
        else
          match gpRobotRoom? s robot, gpFreeGripper? s robot with
          | some robotRoom, some gripper =>
              [ PlanAction.move robot robotRoom objectRoom,
                PlanAction.pick robot o objectRoom gripper,
                PlanAction.move robot objectRoom goalRoom,
                PlanAction.drop robot o goalRoom gripper ]
          | _, _ => []
    | _, _, _ => []
  else
    []

-- Process the objects sequentially while threading the resulting state.
def gpSolveAux (g : Goal) : List Obj → State → List PlanAction
  | [], _ => []
  | o :: os, s =>
      let actions := gpPlanObject o s g
      actions ++ gpSolveAux g os (runPlan actions s)

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  gpSolveAux g s.statics.objects s

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

lemma move_statics (var_r var_from var_to : Obj) (s : State) :
    (move var_r var_from var_to s).statics = s.statics := rfl

lemma pick_statics (var_r var_obj var_room var_g : Obj) (s : State) :
    (pick var_r var_obj var_room var_g s).statics = s.statics := rfl

lemma drop_statics (var_r var_obj var_room var_g : Obj) (s : State) :
    (drop var_r var_obj var_room var_g s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | move var_r var_from var_to        => exact move_statics var_r var_from var_to s
      | pick var_r var_obj var_room var_g => exact pick_statics var_r var_obj var_room var_g s
      | drop var_r var_obj var_room var_g => exact drop_statics var_r var_obj var_room var_g s

-- move only touches at_robby_p
lemma move_at_robby_p_ne_var_x (var_r var_from var_to : Obj) (s : State) {var_to' : Obj} (h1 : var_to' ≠ var_to) (h2 : var_to' ≠ var_from) :
    (move var_r var_from var_to s).dynamic.at_robby_p var_r var_to' = s.dynamic.at_robby_p var_r var_to' := by
  unfold move
  simp [h1, h2]

-- move never touches at_p
lemma move_at_p (var_r var_from var_to : Obj) (s : State) :
    (move var_r var_from var_to s).dynamic.at_p = s.dynamic.at_p := rfl

-- move never touches free_p
lemma move_free_p (var_r var_from var_to : Obj) (s : State) :
    (move var_r var_from var_to s).dynamic.free_p = s.dynamic.free_p := rfl

-- move never touches carry_p
lemma move_carry_p (var_r var_from var_to : Obj) (s : State) :
    (move var_r var_from var_to s).dynamic.carry_p = s.dynamic.carry_p := rfl

-- pick only touches carry_p, at_p, free_p
lemma pick_at_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_obj' var_room' : Obj} (h1 : var_obj' ≠ var_obj) :
    (pick var_r var_obj var_room var_g s).dynamic.at_p var_obj' var_room' = s.dynamic.at_p var_obj' var_room' := by
  unfold pick
  simp [h1]

lemma pick_at_p_ne_var_x (var_r var_obj var_room var_g : Obj) (s : State) {var_room' : Obj} (h1 : var_room' ≠ var_room) :
    (pick var_r var_obj var_room var_g s).dynamic.at_p var_obj var_room' = s.dynamic.at_p var_obj var_room' := by
  unfold pick
  simp [h1]

lemma pick_free_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_r' var_g' : Obj} (h1 : var_r' ≠ var_r) :
    (pick var_r var_obj var_room var_g s).dynamic.free_p var_r' var_g' = s.dynamic.free_p var_r' var_g' := by
  unfold pick
  simp [h1]

lemma pick_free_p_ne_var_g (var_r var_obj var_room var_g : Obj) (s : State) {var_g' : Obj} (h1 : var_g' ≠ var_g) :
    (pick var_r var_obj var_room var_g s).dynamic.free_p var_r var_g' = s.dynamic.free_p var_r var_g' := by
  unfold pick
  simp [h1]

lemma pick_carry_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_r' var_obj' var_g' : Obj} (h1 : var_r' ≠ var_r) :
    (pick var_r var_obj var_room var_g s).dynamic.carry_p var_r' var_obj' var_g' = s.dynamic.carry_p var_r' var_obj' var_g' := by
  unfold pick
  simp [h1]

lemma pick_carry_p_ne_var_o (var_r var_obj var_room var_g : Obj) (s : State) {var_obj' var_g' : Obj} (h1 : var_obj' ≠ var_obj) :
    (pick var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj' var_g' = s.dynamic.carry_p var_r var_obj' var_g' := by
  unfold pick
  simp [h1]

lemma pick_carry_p_ne_var_g (var_r var_obj var_room var_g : Obj) (s : State) {var_g' : Obj} (h1 : var_g' ≠ var_g) :
    (pick var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj var_g' = s.dynamic.carry_p var_r var_obj var_g' := by
  unfold pick
  simp [h1]

-- pick never touches at_robby_p
lemma pick_at_robby_p (var_r var_obj var_room var_g : Obj) (s : State) :
    (pick var_r var_obj var_room var_g s).dynamic.at_robby_p = s.dynamic.at_robby_p := rfl

-- drop only touches at_p, free_p, carry_p
lemma drop_at_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_obj' var_room' : Obj} (h1 : var_obj' ≠ var_obj) :
    (drop var_r var_obj var_room var_g s).dynamic.at_p var_obj' var_room' = s.dynamic.at_p var_obj' var_room' := by
  unfold drop
  simp [h1]

lemma drop_at_p_ne_var_x (var_r var_obj var_room var_g : Obj) (s : State) {var_room' : Obj} (h1 : var_room' ≠ var_room) :
    (drop var_r var_obj var_room var_g s).dynamic.at_p var_obj var_room' = s.dynamic.at_p var_obj var_room' := by
  unfold drop
  simp [h1]

lemma drop_free_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_r' var_g' : Obj} (h1 : var_r' ≠ var_r) :
    (drop var_r var_obj var_room var_g s).dynamic.free_p var_r' var_g' = s.dynamic.free_p var_r' var_g' := by
  unfold drop
  simp [h1]

lemma drop_free_p_ne_var_g (var_r var_obj var_room var_g : Obj) (s : State) {var_g' : Obj} (h1 : var_g' ≠ var_g) :
    (drop var_r var_obj var_room var_g s).dynamic.free_p var_r var_g' = s.dynamic.free_p var_r var_g' := by
  unfold drop
  simp [h1]

lemma drop_carry_p_ne (var_r var_obj var_room var_g : Obj) (s : State) {var_r' var_obj' var_g' : Obj} (h1 : var_r' ≠ var_r) :
    (drop var_r var_obj var_room var_g s).dynamic.carry_p var_r' var_obj' var_g' = s.dynamic.carry_p var_r' var_obj' var_g' := by
  unfold drop
  simp [h1]

lemma drop_carry_p_ne_var_o (var_r var_obj var_room var_g : Obj) (s : State) {var_obj' var_g' : Obj} (h1 : var_obj' ≠ var_obj) :
    (drop var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj' var_g' = s.dynamic.carry_p var_r var_obj' var_g' := by
  unfold drop
  simp [h1]

lemma drop_carry_p_ne_var_g (var_r var_obj var_room var_g : Obj) (s : State) {var_g' : Obj} (h1 : var_g' ≠ var_g) :
    (drop var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj var_g' = s.dynamic.carry_p var_r var_obj var_g' := by
  unfold drop
  simp [h1]

-- drop never touches at_robby_p
lemma drop_at_robby_p (var_r var_obj var_room var_g : Obj) (s : State) :
    (drop var_r var_obj var_room var_g s).dynamic.at_robby_p = s.dynamic.at_robby_p := rfl

lemma move_at_robby_p_eq1 (var_r var_from var_to : Obj) (s : State) :
    (move var_r var_from var_to s).dynamic.at_robby_p var_r var_to = true := by
  unfold move
  simp

lemma move_at_robby_p_eq2 (var_r var_from var_to : Obj) (s : State) (h1 : var_from ≠ var_to) :
    (move var_r var_from var_to s).dynamic.at_robby_p var_r var_from = false := by
  unfold move
  simp [h1]

lemma pick_at_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (pick var_r var_obj var_room var_g s).dynamic.at_p var_obj var_room = false := by
  unfold pick
  simp

lemma pick_free_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (pick var_r var_obj var_room var_g s).dynamic.free_p var_r var_g = false := by
  unfold pick
  simp

lemma pick_carry_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (pick var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj var_g = true := by
  unfold pick
  simp

lemma drop_at_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (drop var_r var_obj var_room var_g s).dynamic.at_p var_obj var_room = true := by
  unfold drop
  simp

lemma drop_free_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (drop var_r var_obj var_room var_g s).dynamic.free_p var_r var_g = true := by
  unfold drop
  simp

lemma drop_carry_p_eq1 (var_r var_obj var_room var_g : Obj) (s : State) :
    (drop var_r var_obj var_room var_g s).dynamic.carry_p var_r var_obj var_g = false := by
  unfold drop
  simp

lemma move_at_robby_p_ne_var_r
    (var_r var_from var_to : Obj) (s : State)
    {var_r' var_room' : Obj} (h : var_r' ≠ var_r) :
    (move var_r var_from var_to s).dynamic.at_robby_p var_r' var_room' =
      s.dynamic.at_robby_p var_r' var_room' := by
  unfold move
  simp [h]

lemma pick_carry_p_ne_gripper
    (var_r var_obj var_room var_g : Obj) (s : State)
    {var_r' var_obj' var_g' : Obj} (h : var_g' ≠ var_g) :
    (pick var_r var_obj var_room var_g s).dynamic.carry_p
        var_r' var_obj' var_g' =
      s.dynamic.carry_p var_r' var_obj' var_g' := by
  unfold pick
  simp [h]

lemma drop_carry_p_ne_gripper
    (var_r var_obj var_room var_g : Obj) (s : State)
    {var_r' var_obj' var_g' : Obj} (h : var_g' ≠ var_g) :
    (drop var_r var_obj var_room var_g s).dynamic.carry_p
        var_r' var_obj' var_g' =
      s.dynamic.carry_p var_r' var_obj' var_g' := by
  unfold drop
  simp [h]


lemma move_preserves_wf
    (var_r var_from var_to)
    (s : State)
    (hwf : WellFormed s)
    (hpre : movePre var_r var_from var_to s) :
    WellFormed (move var_r var_from var_to s) := by
  rcases hwf with
    ⟨hstatic, hvalidAtRobby, hvalidAt, hvalidFree, hvalidCarry,
      hatRobbyUnique, hatUnique, hatCarry, hfreeCarry,
      hgripperUnique, hcarrierUnique, hrobotLoc, hobjectLoc, hgripperLoc⟩
  rcases hpre with ⟨hrType, hfromType, htoType, hatFrom⟩

  have htarget :
      ∀ room,
        (move var_r var_from var_to s).dynamic.at_robby_p var_r room = true →
        room = var_to := by
    intro room hroom
    by_cases hto : room = var_to
    · exact hto
    · by_cases hfrom : room = var_from
      · subst room
        rw [move_at_robby_p_eq2 var_r var_from var_to s hto] at hroom
        simp at hroom
      · have hold :
            s.dynamic.at_robby_p var_r room = true := by
          rw [move_at_robby_p_ne_var_x
            var_r var_from var_to s hto hfrom] at hroom
          exact hroom
        exfalso
        apply hfrom
        apply hatRobbyUnique var_r room var_from
        · change s.dynamic.at_robby_p var_r room = true
          exact hold
        · change s.dynamic.at_robby_p var_r var_from = true
          exact hatFrom

  refine
    ⟨hstatic, ?_, hvalidAt, hvalidFree, hvalidCarry, ?_, hatUnique,
      hatCarry, hfreeCarry, hgripperUnique, hcarrierUnique, ?_,
      hobjectLoc, hgripperLoc⟩
  · intro r room h
    change
      (move var_r var_from var_to s).dynamic.at_robby_p r room = true at h
    change s.statics.robot_t r = true ∧ s.statics.room_t room = true
    by_cases hr : r = var_r
    · subst r
      by_cases hto : room = var_to
      · subst room
        exact ⟨hrType, htoType⟩
      · by_cases hfrom : room = var_from
        · subst room
          rw [move_at_robby_p_eq2 var_r var_from var_to s hto] at h
          simp at h
        · rw [move_at_robby_p_ne_var_x
            var_r var_from var_to s hto hfrom] at h
          apply hvalidAtRobby var_r room
          change s.dynamic.at_robby_p var_r room = true
          exact h
    · rw [move_at_robby_p_ne_var_r
        var_r var_from var_to s hr] at h
      apply hvalidAtRobby r room
      change s.dynamic.at_robby_p r room = true
      exact h
  · intro r room₁ room₂ h₁ h₂
    change
      (move var_r var_from var_to s).dynamic.at_robby_p r room₁ = true at h₁
    change
      (move var_r var_from var_to s).dynamic.at_robby_p r room₂ = true at h₂
    by_cases hr : r = var_r
    · subst r
      exact (htarget room₁ h₁).trans (htarget room₂ h₂).symm
    · apply hatRobbyUnique r room₁ room₂
      · change s.dynamic.at_robby_p r room₁ = true
        rw [move_at_robby_p_ne_var_r
          var_r var_from var_to s hr] at h₁
        exact h₁
      · change s.dynamic.at_robby_p r room₂ = true
        rw [move_at_robby_p_ne_var_r
          var_r var_from var_to s hr] at h₂
        exact h₂
  · intro r hr'
    by_cases hr : r = var_r
    · subst r
      exact ⟨var_to, move_at_robby_p_eq1 var_r var_from var_to s⟩
    · rcases hrobotLoc r hr' with ⟨room, hroom⟩
      refine ⟨room, ?_⟩
      rw [move_at_robby_p_ne_var_r
        var_r var_from var_to s hr]
      exact hroom


lemma pick_preserves_wf
    (var_r var_obj var_room var_g)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pickPre var_r var_obj var_room var_g s) :
    WellFormed (pick var_r var_obj var_room var_g s) := by
  rcases hwf with
    ⟨hstatic, hvalidAtRobby, hvalidAt, hvalidFree, hvalidCarry,
      hatRobbyUnique, hatUnique, hatCarry, hfreeCarry,
      hgripperUnique, hcarrierUnique, hrobotLoc, hobjectLoc, hgripperLoc⟩
  rcases hpre with
    ⟨hrType, hobjType, hroomType, hgType, hatObj, hatRobot, hfree⟩

  have hpickAtOld :
      ∀ o room,
        (pick var_r var_obj var_room var_g s).dynamic.at_p o room = true →
        s.dynamic.at_p o room = true := by
    intro o room h
    by_cases ho : o = var_obj
    · subst o
      by_cases hroom : room = var_room
      · subst room
        rw [pick_at_p_eq1 var_r var_obj var_room var_g s] at h
        simp at h
      · rw [pick_at_p_ne_var_x
          var_r var_obj var_room var_g s hroom] at h
        exact h
    · rw [pick_at_p_ne
        var_r var_obj var_room var_g s ho] at h
      exact h

  have hpickFreeOld :
      ∀ r g,
        (pick var_r var_obj var_room var_g s).dynamic.free_p r g = true →
        s.dynamic.free_p r g = true := by
    intro r g h
    by_cases hr : r = var_r
    · subst r
      by_cases hg : g = var_g
      · subst g
        rw [pick_free_p_eq1 var_r var_obj var_room var_g s] at h
        simp at h
      · rw [pick_free_p_ne_var_g
          var_r var_obj var_room var_g s hg] at h
        exact h
    · rw [pick_free_p_ne
        var_r var_obj var_room var_g s hr] at h
      exact h

  have hpickCarryCases :
      ∀ r o g,
        (pick var_r var_obj var_room var_g s).dynamic.carry_p r o g = true →
        (r = var_r ∧ o = var_obj ∧ g = var_g) ∨
          s.dynamic.carry_p r o g = true := by
    intro r o g h
    by_cases hr : r = var_r
    · subst r
      by_cases ho : o = var_obj
      · subst o
        by_cases hg : g = var_g
        · subst g
          exact Or.inl ⟨rfl, rfl, rfl⟩
        · right
          rw [pick_carry_p_ne_gripper
            var_r var_obj var_room var_g s hg] at h
          exact h
      · right
        rw [pick_carry_p_ne_var_o
          var_r var_obj var_room var_g s ho] at h
        exact h
    · right
      rw [pick_carry_p_ne
        var_r var_obj var_room var_g s hr] at h
      exact h

  refine
    ⟨hstatic, hvalidAtRobby, ?_, ?_, ?_, hatRobbyUnique, ?_, ?_, ?_,
      ?_, ?_, hrobotLoc, ?_, ?_⟩
  · intro o room h
    change
      (pick var_r var_obj var_room var_g s).dynamic.at_p o room = true at h
    apply hvalidAt o room
    change s.dynamic.at_p o room = true
    exact hpickAtOld o room h
  · intro r g h
    change
      (pick var_r var_obj var_room var_g s).dynamic.free_p r g = true at h
    apply hvalidFree r g
    change s.dynamic.free_p r g = true
    exact hpickFreeOld r g h
  · intro r o g h
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at h
    change
      s.statics.robot_t r = true ∧
      s.statics.obj_t o = true ∧
      s.statics.gripper_t g = true
    rcases hpickCarryCases r o g h with hnew | hold
    · rcases hnew with ⟨rfl, rfl, rfl⟩
      exact ⟨hrType, hobjType, hgType⟩
    · apply hvalidCarry r o g
      change s.dynamic.carry_p r o g = true
      exact hold
  · intro o room₁ room₂ h₁ h₂
    change
      (pick var_r var_obj var_room var_g s).dynamic.at_p o room₁ = true at h₁
    change
      (pick var_r var_obj var_room var_g s).dynamic.at_p o room₂ = true at h₂
    apply hatUnique o room₁ room₂
    · change s.dynamic.at_p o room₁ = true
      exact hpickAtOld o room₁ h₁
    · change s.dynamic.at_p o room₂ = true
      exact hpickAtOld o room₂ h₂
  · intro o room r g h
    rcases h with ⟨ha, hc⟩
    change
      (pick var_r var_obj var_room var_g s).dynamic.at_p o room = true at ha
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at hc
    have haOld := hpickAtOld o room ha
    rcases hpickCarryCases r o g hc with hnew | hcOld
    · have hroom : room = var_room := by
        apply hatUnique o room var_room
        · change s.dynamic.at_p o room = true
          exact haOld
        · change s.dynamic.at_p o var_room = true
          simpa [hnew.2.1] using hatObj
      have hfalse :
          (pick var_r var_obj var_room var_g s).dynamic.at_p
            var_obj var_room = true := by
        simpa [hnew.2.1, hroom] using ha
      rw [pick_at_p_eq1 var_r var_obj var_room var_g s] at hfalse
      simp at hfalse
    · apply hatCarry o room r g
      constructor
      · change s.dynamic.at_p o room = true
        exact haOld
      · change s.dynamic.carry_p r o g = true
        exact hcOld
  · intro r g o h
    rcases h with ⟨hf, hc⟩
    change
      (pick var_r var_obj var_room var_g s).dynamic.free_p r g = true at hf
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at hc
    have hfOld := hpickFreeOld r g hf
    rcases hpickCarryCases r o g hc with hnew | hcOld
    · have hfalse :
          (pick var_r var_obj var_room var_g s).dynamic.free_p
            var_r var_g = true := by
        simpa [hnew.1, hnew.2.2] using hf
      rw [pick_free_p_eq1 var_r var_obj var_room var_g s] at hfalse
      simp at hfalse
    · apply hfreeCarry r g o
      constructor
      · change s.dynamic.free_p r g = true
        exact hfOld
      · change s.dynamic.carry_p r o g = true
        exact hcOld
  · intro r g o₁ o₂ hc₁ hc₂
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r o₁ g = true at hc₁
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r o₂ g = true at hc₂
    rcases hpickCarryCases r o₁ g hc₁ with hnew₁ | hold₁
    · rcases hpickCarryCases r o₂ g hc₂ with hnew₂ | hold₂
      · exact hnew₁.2.1.trans hnew₂.2.1.symm
      · have hold₂' :
            s.dynamic.carry_p var_r o₂ var_g = true := by
          simpa [hnew₁.1, hnew₁.2.2] using hold₂
        exfalso
        apply hfreeCarry var_r var_g o₂
        constructor
        · change s.dynamic.free_p var_r var_g = true
          exact hfree
        · change s.dynamic.carry_p var_r o₂ var_g = true
          exact hold₂'
    · rcases hpickCarryCases r o₂ g hc₂ with hnew₂ | hold₂
      · have hold₁' :
            s.dynamic.carry_p var_r o₁ var_g = true := by
          simpa [hnew₂.1, hnew₂.2.2] using hold₁
        exfalso
        apply hfreeCarry var_r var_g o₁
        constructor
        · change s.dynamic.free_p var_r var_g = true
          exact hfree
        · change s.dynamic.carry_p var_r o₁ var_g = true
          exact hold₁'
      · apply hgripperUnique r g o₁ o₂
        · change s.dynamic.carry_p r o₁ g = true
          exact hold₁
        · change s.dynamic.carry_p r o₂ g = true
          exact hold₂
  · intro o r₁ g₁ r₂ g₂ hc₁ hc₂
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r₁ o g₁ = true at hc₁
    change
      (pick var_r var_obj var_room var_g s).dynamic.carry_p r₂ o g₂ = true at hc₂
    rcases hpickCarryCases r₁ o g₁ hc₁ with hnew₁ | hold₁
    · rcases hpickCarryCases r₂ o g₂ hc₂ with hnew₂ | hold₂
      · exact
          ⟨hnew₁.1.trans hnew₂.1.symm,
            hnew₁.2.2.trans hnew₂.2.2.symm⟩
      · have hold₂' :
            s.dynamic.carry_p r₂ var_obj g₂ = true := by
          simpa [hnew₁.2.1] using hold₂
        exfalso
        apply hatCarry var_obj var_room r₂ g₂
        constructor
        · change s.dynamic.at_p var_obj var_room = true
          exact hatObj
        · change s.dynamic.carry_p r₂ var_obj g₂ = true
          exact hold₂'
    · rcases hpickCarryCases r₂ o g₂ hc₂ with hnew₂ | hold₂
      · have hold₁' :
            s.dynamic.carry_p r₁ var_obj g₁ = true := by
          simpa [hnew₂.2.1] using hold₁
        exfalso
        apply hatCarry var_obj var_room r₁ g₁
        constructor
        · change s.dynamic.at_p var_obj var_room = true
          exact hatObj
        · change s.dynamic.carry_p r₁ var_obj g₁ = true
          exact hold₁'
      · apply hcarrierUnique o r₁ g₁ r₂ g₂
        · change s.dynamic.carry_p r₁ o g₁ = true
          exact hold₁
        · change s.dynamic.carry_p r₂ o g₂ = true
          exact hold₂
  · intro o hoType
    by_cases ho : o = var_obj
    · subst o
      exact Or.inr
        ⟨var_r, var_g, pick_carry_p_eq1 var_r var_obj var_room var_g s⟩
    · rcases hobjectLoc o hoType with hat | hcarry
      · rcases hat with ⟨room, hroom⟩
        refine Or.inl ⟨room, ?_⟩
        rw [pick_at_p_ne var_r var_obj var_room var_g s ho]
        exact hroom
      · rcases hcarry with ⟨r, g, hc⟩
        refine Or.inr ⟨r, g, ?_⟩
        by_cases hr : r = var_r
        · subst r
          rw [pick_carry_p_ne_var_o
            var_r var_obj var_room var_g s ho]
          exact hc
        · rw [pick_carry_p_ne
            var_r var_obj var_room var_g s hr]
          exact hc
  · intro r g hrType' hgType'
    by_cases hpair : r = var_r ∧ g = var_g
    · right
      refine ⟨var_obj, ?_⟩
      simpa [hpair.1, hpair.2] using
        pick_carry_p_eq1 var_r var_obj var_room var_g s
    · rcases hgripperLoc r g hrType' hgType' with hf | hc
      · left
        by_cases hr : r = var_r
        · subst r
          have hg : g ≠ var_g := by
            intro heq
            apply hpair
            exact ⟨rfl, heq⟩
          rw [pick_free_p_ne_var_g
            var_r var_obj var_room var_g s hg]
          exact hf
        · rw [pick_free_p_ne
            var_r var_obj var_room var_g s hr]
          exact hf
      · rcases hc with ⟨o, ho⟩
        right
        refine ⟨o, ?_⟩
        by_cases hr : r = var_r
        · subst r
          have hg : g ≠ var_g := by
            intro heq
            apply hpair
            exact ⟨rfl, heq⟩
          rw [pick_carry_p_ne_gripper
            var_r var_obj var_room var_g s hg]
          exact ho
        · rw [pick_carry_p_ne
            var_r var_obj var_room var_g s hr]
          exact ho


lemma drop_preserves_wf
    (var_r var_obj var_room var_g)
    (s : State)
    (hwf : WellFormed s)
    (hpre : dropPre var_r var_obj var_room var_g s) :
    WellFormed (drop var_r var_obj var_room var_g s) := by
  rcases hwf with
    ⟨hstatic, hvalidAtRobby, hvalidAt, hvalidFree, hvalidCarry,
      hatRobbyUnique, hatUnique, hatCarry, hfreeCarry,
      hgripperUnique, hcarrierUnique, hrobotLoc, hobjectLoc, hgripperLoc⟩
  rcases hpre with
    ⟨hrType, hobjType, hroomType, hgType, hcarried, hatRobot⟩

  have hdropAtCases :
      ∀ o room,
        (drop var_r var_obj var_room var_g s).dynamic.at_p o room = true →
        (o = var_obj ∧ room = var_room) ∨
          s.dynamic.at_p o room = true := by
    intro o room h
    by_cases ho : o = var_obj
    · subst o
      by_cases hroom : room = var_room
      · exact Or.inl ⟨rfl, hroom⟩
      · right
        rw [drop_at_p_ne_var_x
          var_r var_obj var_room var_g s hroom] at h
        exact h
    · right
      rw [drop_at_p_ne
        var_r var_obj var_room var_g s ho] at h
      exact h

  have hdropFreeCases :
      ∀ r g,
        (drop var_r var_obj var_room var_g s).dynamic.free_p r g = true →
        (r = var_r ∧ g = var_g) ∨
          s.dynamic.free_p r g = true := by
    intro r g h
    by_cases hr : r = var_r
    · subst r
      by_cases hg : g = var_g
      · exact Or.inl ⟨rfl, hg⟩
      · right
        rw [drop_free_p_ne_var_g
          var_r var_obj var_room var_g s hg] at h
        exact h
    · right
      rw [drop_free_p_ne
        var_r var_obj var_room var_g s hr] at h
      exact h

  have hdropCarryOld :
      ∀ r o g,
        (drop var_r var_obj var_room var_g s).dynamic.carry_p r o g = true →
        s.dynamic.carry_p r o g = true := by
    intro r o g h
    by_cases hr : r = var_r
    · subst r
      by_cases ho : o = var_obj
      · subst o
        by_cases hg : g = var_g
        · subst g
          rw [drop_carry_p_eq1 var_r var_obj var_room var_g s] at h
          simp at h
        · rw [drop_carry_p_ne_gripper
            var_r var_obj var_room var_g s hg] at h
          exact h
      · rw [drop_carry_p_ne_var_o
          var_r var_obj var_room var_g s ho] at h
        exact h
    · rw [drop_carry_p_ne
        var_r var_obj var_room var_g s hr] at h
      exact h

  refine
    ⟨hstatic, hvalidAtRobby, ?_, ?_, ?_, hatRobbyUnique, ?_, ?_, ?_,
      ?_, ?_, hrobotLoc, ?_, ?_⟩
  · intro o room h
    change
      (drop var_r var_obj var_room var_g s).dynamic.at_p o room = true at h
    change s.statics.obj_t o = true ∧ s.statics.room_t room = true
    rcases hdropAtCases o room h with hnew | hold
    · rcases hnew with ⟨rfl, rfl⟩
      exact ⟨hobjType, hroomType⟩
    · apply hvalidAt o room
      change s.dynamic.at_p o room = true
      exact hold
  · intro r g h
    change
      (drop var_r var_obj var_room var_g s).dynamic.free_p r g = true at h
    change s.statics.robot_t r = true ∧ s.statics.gripper_t g = true
    rcases hdropFreeCases r g h with hnew | hold
    · rcases hnew with ⟨rfl, rfl⟩
      exact ⟨hrType, hgType⟩
    · apply hvalidFree r g
      change s.dynamic.free_p r g = true
      exact hold
  · intro r o g h
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at h
    apply hvalidCarry r o g
    change s.dynamic.carry_p r o g = true
    exact hdropCarryOld r o g h
  · intro o room₁ room₂ h₁ h₂
    change
      (drop var_r var_obj var_room var_g s).dynamic.at_p o room₁ = true at h₁
    change
      (drop var_r var_obj var_room var_g s).dynamic.at_p o room₂ = true at h₂
    rcases hdropAtCases o room₁ h₁ with hnew₁ | hold₁
    · rcases hdropAtCases o room₂ h₂ with hnew₂ | hold₂
      · exact hnew₁.2.trans hnew₂.2.symm
      · have hold₂' :
            s.dynamic.at_p var_obj room₂ = true := by
          simpa [hnew₁.1] using hold₂
        exfalso
        apply hatCarry var_obj room₂ var_r var_g
        constructor
        · change s.dynamic.at_p var_obj room₂ = true
          exact hold₂'
        · change s.dynamic.carry_p var_r var_obj var_g = true
          exact hcarried
    · rcases hdropAtCases o room₂ h₂ with hnew₂ | hold₂
      · have hold₁' :
            s.dynamic.at_p var_obj room₁ = true := by
          simpa [hnew₂.1] using hold₁
        exfalso
        apply hatCarry var_obj room₁ var_r var_g
        constructor
        · change s.dynamic.at_p var_obj room₁ = true
          exact hold₁'
        · change s.dynamic.carry_p var_r var_obj var_g = true
          exact hcarried
      · apply hatUnique o room₁ room₂
        · change s.dynamic.at_p o room₁ = true
          exact hold₁
        · change s.dynamic.at_p o room₂ = true
          exact hold₂
  · intro o room r g h
    rcases h with ⟨ha, hc⟩
    change
      (drop var_r var_obj var_room var_g s).dynamic.at_p o room = true at ha
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at hc
    have hcOld := hdropCarryOld r o g hc
    rcases hdropAtCases o room ha with hnew | haOld
    · have hcOld' :
          s.dynamic.carry_p r var_obj g = true := by
        simpa [hnew.1] using hcOld
      have hu : var_r = r ∧ var_g = g := by
        apply hcarrierUnique var_obj var_r var_g r g
        · change s.dynamic.carry_p var_r var_obj var_g = true
          exact hcarried
        · change s.dynamic.carry_p r var_obj g = true
          exact hcOld'
      have hfalse :
          (drop var_r var_obj var_room var_g s).dynamic.carry_p
            var_r var_obj var_g = true := by
        simpa [hnew.1, hu.1, hu.2] using hc
      rw [drop_carry_p_eq1 var_r var_obj var_room var_g s] at hfalse
      simp at hfalse
    · apply hatCarry o room r g
      constructor
      · change s.dynamic.at_p o room = true
        exact haOld
      · change s.dynamic.carry_p r o g = true
        exact hcOld
  · intro r g o h
    rcases h with ⟨hf, hc⟩
    change
      (drop var_r var_obj var_room var_g s).dynamic.free_p r g = true at hf
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r o g = true at hc
    have hcOld := hdropCarryOld r o g hc
    rcases hdropFreeCases r g hf with hnew | hfOld
    · have hcOld' :
          s.dynamic.carry_p var_r o var_g = true := by
        simpa [hnew.1, hnew.2] using hcOld
      have hoEq : var_obj = o := by
        apply hgripperUnique var_r var_g var_obj o
        · change s.dynamic.carry_p var_r var_obj var_g = true
          exact hcarried
        · change s.dynamic.carry_p var_r o var_g = true
          exact hcOld'
      have hfalse :
          (drop var_r var_obj var_room var_g s).dynamic.carry_p
            var_r var_obj var_g = true := by
        simpa [hnew.1, hnew.2, hoEq] using hc
      rw [drop_carry_p_eq1 var_r var_obj var_room var_g s] at hfalse
      simp at hfalse
    · apply hfreeCarry r g o
      constructor
      · change s.dynamic.free_p r g = true
        exact hfOld
      · change s.dynamic.carry_p r o g = true
        exact hcOld
  · intro r g o₁ o₂ hc₁ hc₂
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r o₁ g = true at hc₁
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r o₂ g = true at hc₂
    apply hgripperUnique r g o₁ o₂
    · change s.dynamic.carry_p r o₁ g = true
      exact hdropCarryOld r o₁ g hc₁
    · change s.dynamic.carry_p r o₂ g = true
      exact hdropCarryOld r o₂ g hc₂
  · intro o r₁ g₁ r₂ g₂ hc₁ hc₂
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r₁ o g₁ = true at hc₁
    change
      (drop var_r var_obj var_room var_g s).dynamic.carry_p r₂ o g₂ = true at hc₂
    apply hcarrierUnique o r₁ g₁ r₂ g₂
    · change s.dynamic.carry_p r₁ o g₁ = true
      exact hdropCarryOld r₁ o g₁ hc₁
    · change s.dynamic.carry_p r₂ o g₂ = true
      exact hdropCarryOld r₂ o g₂ hc₂
  · intro o hoType
    by_cases ho : o = var_obj
    · subst o
      exact Or.inl
        ⟨var_room, drop_at_p_eq1 var_r var_obj var_room var_g s⟩
    · rcases hobjectLoc o hoType with hat | hcarry
      · rcases hat with ⟨room, hroom⟩
        refine Or.inl ⟨room, ?_⟩
        rw [drop_at_p_ne var_r var_obj var_room var_g s ho]
        exact hroom
      · rcases hcarry with ⟨r, g, hc⟩
        refine Or.inr ⟨r, g, ?_⟩
        by_cases hr : r = var_r
        · subst r
          rw [drop_carry_p_ne_var_o
            var_r var_obj var_room var_g s ho]
          exact hc
        · rw [drop_carry_p_ne
            var_r var_obj var_room var_g s hr]
          exact hc
  · intro r g hrType' hgType'
    by_cases hpair : r = var_r ∧ g = var_g
    · left
      simpa [hpair.1, hpair.2] using
        drop_free_p_eq1 var_r var_obj var_room var_g s
    · rcases hgripperLoc r g hrType' hgType' with hf | hc
      · left
        by_cases hr : r = var_r
        · subst r
          have hg : g ≠ var_g := by
            intro heq
            apply hpair
            exact ⟨rfl, heq⟩
          rw [drop_free_p_ne_var_g
            var_r var_obj var_room var_g s hg]
          exact hf
        · rw [drop_free_p_ne
            var_r var_obj var_room var_g s hr]
          exact hf
      · rcases hc with ⟨o, ho⟩
        right
        refine ⟨o, ?_⟩
        by_cases hr : r = var_r
        · subst r
          have hg : g ≠ var_g := by
            intro heq
            apply hpair
            exact ⟨rfl, heq⟩
          rw [drop_carry_p_ne_gripper
            var_r var_obj var_room var_g s hg]
          exact ho
        · rw [drop_carry_p_ne
            var_r var_obj var_room var_g s hr]
          exact ho

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | move var_r var_from var_to =>
      exact move_preserves_wf var_r var_from var_to s hwf hpre
  | pick var_r var_obj var_room var_g =>
      exact pick_preserves_wf var_r var_obj var_room var_g s hwf hpre
  | drop var_r var_obj var_room var_g =>
      exact drop_preserves_wf var_r var_obj var_room var_g s hwf hpre

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

lemma gpFind?_sound
    {p : Obj → Bool} {xs : List Obj} {x : Obj}
    (h : gpFind? p xs = some x) :
    x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [gpFind?] at h
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [gpFind?, hy] at h
        subst x
        exact ⟨by simp, hy⟩
      · simp [gpFind?, hy] at h
        rcases ih h with ⟨hxmem, hpx⟩
        exact ⟨by simp [hxmem], hpx⟩

lemma gpFind?_complete
    {p : Obj → Bool} {xs : List Obj} {x : Obj}
    (hxmem : x ∈ xs)
    (hpx : p x = true) :
    ∃ y, gpFind? p xs = some y := by
  induction xs with
  | nil =>
      simp at hxmem
  | cons y ys ih =>
      by_cases hy : p y = true
      · exact ⟨y, by simp [gpFind?, hy]⟩
      · have hxy : x ≠ y := by
          intro h
          subst x
          exact hy hpx
        have hxmem' : x ∈ ys := by
          simpa [hxy] using hxmem
        rcases ih hxmem' with ⟨z, hz⟩
        exact ⟨z, by simp [gpFind?, hy, hz]⟩

lemma room_mem_of_type
    {st : StaticState} (hstatic : WellFormedStatic st)
    {room : Obj} (hroom : st.room_t room = true) :
    room ∈ st.objects := by
  rcases hstatic with ⟨_, htypes, _, _⟩
  exact htypes.1 room hroom

lemma object_mem_of_type
    {st : StaticState} (hstatic : WellFormedStatic st)
    {o : Obj} (ho : st.obj_t o = true) :
    o ∈ st.objects := by
  rcases hstatic with ⟨_, htypes, _, _⟩
  exact htypes.2.1 o ho

lemma robot_mem_of_type
    {st : StaticState} (hstatic : WellFormedStatic st)
    {r : Obj} (hr : st.robot_t r = true) :
    r ∈ st.objects := by
  rcases hstatic with ⟨_, htypes, _, _⟩
  exact htypes.2.2.1 r hr

lemma gripper_mem_of_type
    {st : StaticState} (hstatic : WellFormedStatic st)
    {gr : Obj} (hgr : st.gripper_t gr = true) :
    gr ∈ st.objects := by
  rcases hstatic with ⟨_, htypes, _, _⟩
  exact htypes.2.2.2.1 gr hgr

lemma gpObjectRoom?_sound
    {s : State} {o room : Obj}
    (h : gpObjectRoom? s o = some room) :
    s.statics.room_t room = true ∧
    s.dynamic.at_p o room = true := by
  unfold gpObjectRoom? at h
  rcases gpFind?_sound h with ⟨_, hp⟩
  simpa only [Bool.and_eq_true] using hp

lemma gpGoalRoom?_sound
    {s : State} {g : Goal} {o room : Obj}
    (h : gpGoalRoom? s g o = some room) :
    s.statics.room_t room = true ∧
    g.dynamic.at_p o room = some true := by
  unfold gpGoalRoom? at h
  rcases gpFind?_sound h with ⟨_, hp⟩
  have hand :
      s.statics.room_t room = true ∧
        (match g.dynamic.at_p o room with
         | some true => true
         | _ => false) = true := by
    simpa only [Bool.and_eq_true] using hp
  refine ⟨hand.1, ?_⟩
  cases hopt : g.dynamic.at_p o room with
  | none =>
      simp [hopt] at hand
  | some b =>
      cases b with
      | false =>
          simp [hopt] at hand
      | true =>
          rfl

lemma gpRobot?_sound
    {s : State} {r : Obj}
    (h : gpRobot? s = some r) :
    s.statics.robot_t r = true := by
  unfold gpRobot? at h
  exact (gpFind?_sound h).2

lemma gpRobotRoom?_sound
    {s : State} {r room : Obj}
    (h : gpRobotRoom? s r = some room) :
    s.statics.room_t room = true ∧
    s.dynamic.at_robby_p r room = true := by
  unfold gpRobotRoom? at h
  rcases gpFind?_sound h with ⟨_, hp⟩
  simpa only [Bool.and_eq_true] using hp

lemma gpFreeGripper?_sound
    {s : State} {r gr : Obj}
    (h : gpFreeGripper? s r = some gr) :
    s.statics.gripper_t gr = true ∧
    s.dynamic.free_p r gr = true := by
  unfold gpFreeGripper? at h
  rcases gpFind?_sound h with ⟨_, hp⟩
  simpa only [Bool.and_eq_true] using hp

lemma no_carry_of_all_grippers_free
    {s : State}
    (hwf : WellFormed s)
    (hfree : InitAllGrippersFree s) :
    ∀ r o gr, s.dynamic.carry_p r o gr ≠ true := by
  intro r o gr hcarry
  rcases hwf with
    ⟨_, _, _, _, hvalidCarry, _, _, _, hfreeCarry,
      _, _, _, _, _⟩
  have htypes := hvalidCarry r o gr hcarry
  have hf : s.dynamic.free_p r gr = true :=
    hfree r gr htypes.1 htypes.2.2
  exact hfreeCarry r gr o ⟨hf, hcarry⟩

lemma gpObjectRoom?_exists
    {s : State} {o : Obj}
    (hwf : WellFormed s)
    (hfree : InitAllGrippersFree s)
    (ho : s.statics.obj_t o = true) :
    ∃ room, gpObjectRoom? s o = some room := by
  have hwf' := hwf
  rcases hwf' with
    ⟨hstatic, _, hvalidAt, _, _, _, _, _, _, _, _, _, hobjectLoc, _⟩
  rcases hobjectLoc o ho with hat | hcarry
  · rcases hat with ⟨room, hroom⟩
    have hroomType : s.statics.room_t room = true :=
      (hvalidAt o room hroom).2
    have hroomMem : room ∈ s.statics.objects :=
      room_mem_of_type hstatic hroomType
    unfold gpObjectRoom?
    apply gpFind?_complete hroomMem
    simp [hroomType, hroom]
  · rcases hcarry with ⟨r, gr, hcarry⟩
    exact False.elim
      (no_carry_of_all_grippers_free hwf hfree r o gr hcarry)

lemma gpGoalRoom?_exists
    {s : State} {g : Goal} {o : Obj}
    (hgoal : WellFormedGoal s g)
    (ho : s.statics.obj_t o = true) :
    ∃ room, gpGoalRoom? s g o = some room := by
  have hgoal' := hgoal
  rcases hgoal' with
    ⟨hstatic, _, hvalidAt, _, _, _, _, _, _, _, _, _, _, _, _,
      hevery⟩
  rcases hevery o ho with ⟨room, htarget⟩
  have hroomType : s.statics.room_t room = true :=
    (hvalidAt o room htarget).2
  have hroomMem : room ∈ s.statics.objects :=
    room_mem_of_type hstatic hroomType
  unfold gpGoalRoom?
  apply gpFind?_complete hroomMem
  simp [hroomType, htarget]

lemma gpRobot?_exists
    {s : State}
    (hstatic : WellFormedStatic s.statics) :
    ∃ r, gpRobot? s = some r := by
  rcases hstatic with ⟨_, htypes, _, hmin⟩
  rcases hmin.2.2.1 with ⟨r, hr⟩
  have hrmem : r ∈ s.statics.objects := htypes.2.2.1 r hr
  unfold gpRobot?
  exact gpFind?_complete hrmem hr

lemma gpRobotRoom?_exists
    {s : State} {r : Obj}
    (hwf : WellFormed s)
    (hr : s.statics.robot_t r = true) :
    ∃ room, gpRobotRoom? s r = some room := by
  have hwf' := hwf
  rcases hwf' with
    ⟨hstatic, hvalidAtRobby, _, _, _, _, _, _, _, _, _,
      hrobotLoc, _, _⟩
  rcases hrobotLoc r hr with ⟨room, hroom⟩
  have hroomType : s.statics.room_t room = true :=
    (hvalidAtRobby r room hroom).2
  have hroomMem : room ∈ s.statics.objects :=
    room_mem_of_type hstatic hroomType
  unfold gpRobotRoom?
  apply gpFind?_complete hroomMem
  simp [hroomType, hroom]

lemma gpFreeGripper?_exists
    {s : State} {r : Obj}
    (hwf : WellFormed s)
    (hfree : InitAllGrippersFree s)
    (hr : s.statics.robot_t r = true) :
    ∃ gr, gpFreeGripper? s r = some gr := by
  have hwf' := hwf
  rcases hwf' with ⟨hstatic, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  rcases hstatic with ⟨_, htypes, _, hmin⟩
  rcases hmin.2.2.2 with ⟨gr₁, gr₂, hgr₁, hgr₂, hne⟩
  have hgrMem : gr₁ ∈ s.statics.objects :=
    htypes.2.2.2.1 gr₁ hgr₁
  have hgrFree : s.dynamic.free_p r gr₁ = true :=
    hfree r gr₁ hr hgr₁
  unfold gpFreeGripper?
  apply gpFind?_complete hgrMem
  simp [hgr₁, hgrFree]

lemma wellFormedGoal_of_statics_eq
    {s s' : State} {g : Goal}
    (hstat : s'.statics = s.statics)
    (hgoal : WellFormedGoal s g) :
    WellFormedGoal s' g := by
  simpa [WellFormedGoal, GoalIgnoreAtRobby, GoalIgnoreFree,
    GoalIgnoreCarry, GoalAtOnlyPositive, GoalEveryObjectHasTarget,
    hstat] using hgoal

lemma gpPlanObject_correct
    (o : Obj) (s : State) (g : Goal)
    (hwf : WellFormed s)
    (hfree : InitAllGrippersFree s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (gpPlanObject o s g) s ∧
    WellFormed (runPlan (gpPlanObject o s g) s) ∧
    InitAllGrippersFree (runPlan (gpPlanObject o s g) s) ∧
    (∀ room,
      g.dynamic.at_p o room = some true →
      (runPlan (gpPlanObject o s g) s).dynamic.at_p o room = true) ∧
    (∀ o' room, o' ≠ o →
      (runPlan (gpPlanObject o s g) s).dynamic.at_p o' room =
        s.dynamic.at_p o' room) := by
  have hwf' := hwf
  rcases hwf' with
    ⟨hstatic, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hgoal' := hgoal
  rcases hgoal' with
    ⟨_, _, hgValidAt, _, _, _, hgAtUnique, _, _, _, _, _, _, _, _, _⟩
  by_cases ho : s.statics.obj_t o = true
  · rcases gpObjectRoom?_exists hwf hfree ho with
      ⟨objectRoom, hobjectRoom⟩
    rcases gpGoalRoom?_exists hgoal ho with
      ⟨goalRoom, hgoalRoom⟩
    rcases gpRobot?_exists hstatic with ⟨robot, hrobot⟩
    have hrType : s.statics.robot_t robot = true :=
      gpRobot?_sound hrobot
    rcases gpRobotRoom?_exists hwf hrType with
      ⟨robotRoom, hrobotRoom⟩
    rcases gpFreeGripper?_exists hwf hfree hrType with
      ⟨gripper, hgripper⟩

    rcases gpObjectRoom?_sound hobjectRoom with
      ⟨hobjectRoomType, hatObject⟩
    rcases gpGoalRoom?_sound hgoalRoom with
      ⟨hgoalRoomType, hgoalAt⟩
    rcases gpRobotRoom?_sound hrobotRoom with
      ⟨hrobotRoomType, hatRobot⟩
    rcases gpFreeGripper?_sound hgripper with
      ⟨hgripperType, hgripperFree⟩

    by_cases heq : objectRoom = goalRoom
    · have hplan :
          gpPlanObject o s g = [] := by
        simp [gpPlanObject, ho, hobjectRoom, hgoalRoom, hrobot, heq]
      rw [hplan]
      refine ⟨by simp [ValidPlan], hwf, hfree, ?_, ?_⟩
      · intro room htarget
        have hroomEq : room = goalRoom := by
          apply hgAtUnique o room goalRoom
          · exact htarget
          · exact hgoalAt
        subst room
        have hatGoal : s.dynamic.at_p o goalRoom = true := by
          simpa [heq] using hatObject
        simpa [runPlan] using hatGoal
      · intro o' room hne
        rfl
    · have hplan :
          gpPlanObject o s g =
            [ PlanAction.move robot robotRoom objectRoom,
              PlanAction.pick robot o objectRoom gripper,
              PlanAction.move robot objectRoom goalRoom,
              PlanAction.drop robot o goalRoom gripper ] := by
        simp [gpPlanObject, ho, hobjectRoom, hgoalRoom, hrobot,
          heq, hrobotRoom, hgripper]

      rw [hplan]

      have hvalid :
          ValidPlan
            [ PlanAction.move robot robotRoom objectRoom,
              PlanAction.pick robot o objectRoom gripper,
              PlanAction.move robot objectRoom goalRoom,
              PlanAction.drop robot o goalRoom gripper ] s := by
        simp only [ValidPlan, actionPre, actionApply]
        refine ⟨⟨hrType, hrobotRoomType, hobjectRoomType, hatRobot⟩, ?_⟩
        refine ⟨?_, ?_⟩
        · refine
            ⟨hrType, ho, hobjectRoomType, hgripperType, ?_, ?_, ?_⟩
          · rw [move_at_p]
            exact hatObject
          · exact move_at_robby_p_eq1 robot robotRoom objectRoom s
          · rw [move_free_p]
            exact hgripperFree
        · refine ⟨?_, ?_⟩
          · refine ⟨hrType, hobjectRoomType, hgoalRoomType, ?_⟩
            rw [pick_at_robby_p]
            exact move_at_robby_p_eq1 robot robotRoom objectRoom s
          · refine ⟨?_, trivial⟩
            refine
              ⟨hrType, ho, hgoalRoomType, hgripperType, ?_, ?_⟩
            · rw [move_carry_p]
              exact pick_carry_p_eq1 robot o objectRoom gripper
                (move robot robotRoom objectRoom s)
            · exact move_at_robby_p_eq1 robot objectRoom goalRoom
                (pick robot o objectRoom gripper
                  (move robot robotRoom objectRoom s))

      refine
        ⟨hvalid, validPlan_preserves_wf hvalid hwf, ?_, ?_, ?_⟩
      · intro r' gr' hr' hgr'
        change s.statics.robot_t r' = true at hr'
        change s.statics.gripper_t gr' = true at hgr'
        have hold : s.dynamic.free_p r' gr' = true :=
          hfree r' gr' hr' hgr'
        by_cases hrEq : r' = robot
        · subst r'
          by_cases hgEq : gr' = gripper
          · subst gr'
            simp [runPlan, actionApply, move, pick, drop]
          · simp [runPlan, actionApply, move, pick, drop, hgEq, hold]
        · simp [runPlan, actionApply, move, pick, drop, hrEq, hold]
      · intro room htarget
        have hroomEq : room = goalRoom := by
          apply hgAtUnique o room goalRoom
          · exact htarget
          · exact hgoalAt
        subst room
        change
          (drop robot o goalRoom gripper
            (move robot objectRoom goalRoom
              (pick robot o objectRoom gripper
                (move robot robotRoom objectRoom s)))).dynamic.at_p
              o goalRoom = true
        exact drop_at_p_eq1 robot o goalRoom gripper
          (move robot objectRoom goalRoom
            (pick robot o objectRoom gripper
              (move robot robotRoom objectRoom s)))
      · intro o' room hne
        simp [runPlan, actionApply, move, pick, drop, hne]
  · have hplan : gpPlanObject o s g = [] := by
      simp [gpPlanObject, ho]
    rw [hplan]
    refine ⟨by simp [ValidPlan], hwf, hfree, ?_, ?_⟩
    · intro room htarget
      have htypes := hgValidAt o room htarget
      exact (ho htypes.1).elim
    · intro o' room hne
      rfl

lemma gpSolveAux_correct
    (g : Goal) (xs : List Obj) (s : State)
    (hwf : WellFormed s)
    (hfree : InitAllGrippersFree s)
    (hgoal : WellFormedGoal s g)
    (hnodup : xs.Nodup) :
    ValidPlan (gpSolveAux g xs s) s ∧
    WellFormed (runPlan (gpSolveAux g xs s) s) ∧
    InitAllGrippersFree (runPlan (gpSolveAux g xs s) s) ∧
    (∀ o, o ∈ xs → s.statics.obj_t o = true →
      ∀ room, g.dynamic.at_p o room = some true →
        (runPlan (gpSolveAux g xs s) s).dynamic.at_p o room = true) ∧
    (∀ o room, o ∉ xs →
      (runPlan (gpSolveAux g xs s) s).dynamic.at_p o room =
        s.dynamic.at_p o room) := by
  induction xs generalizing s with
  | nil =>
      simp [gpSolveAux, runPlan, ValidPlan, hwf, hfree]
  | cons head tail ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hheadNotMem : head ∉ tail := hnodupParts.1
      have htailNodup : tail.Nodup := hnodupParts.2

      let p := gpPlanObject head s g
      let s₁ := runPlan p s

      have hp := gpPlanObject_correct head s g hwf hfree hgoal
      have hpValid : ValidPlan p s := by
        simpa [p] using hp.1
      have hpWf : WellFormed s₁ := by
        simpa [p, s₁] using hp.2.1
      have hpFree : InitAllGrippersFree s₁ := by
        simpa [p, s₁] using hp.2.2.1
      have hpTarget :
          ∀ room, g.dynamic.at_p head room = some true →
            s₁.dynamic.at_p head room = true := by
        simpa [p, s₁] using hp.2.2.2.1
      have hpPreserve :
          ∀ o' room, o' ≠ head →
            s₁.dynamic.at_p o' room = s.dynamic.at_p o' room := by
        simpa [p, s₁] using hp.2.2.2.2

      have hstat₁ : s₁.statics = s.statics := by
        simpa [p, s₁] using runPlan_statics p s
      have hgoal₁ : WellFormedGoal s₁ g :=
        wellFormedGoal_of_statics_eq hstat₁ hgoal

      have hi := ih s₁ hpWf hpFree hgoal₁ htailNodup

      have hvalid :
          ValidPlan (p ++ gpSolveAux g tail s₁) s := by
        apply (validPlan_append p (gpSolveAux g tail s₁) s).2
        exact ⟨hpValid, hi.1⟩

      have hfinalWf :
          WellFormed
            (runPlan (gpSolveAux g tail s₁) s₁) :=
        hi.2.1
      have hfinalFree :
          InitAllGrippersFree
            (runPlan (gpSolveAux g tail s₁) s₁) :=
        hi.2.2.1

      have htargets :
          ∀ x, x ∈ head :: tail → s.statics.obj_t x = true →
            ∀ room, g.dynamic.at_p x room = some true →
              (runPlan (gpSolveAux g tail s₁) s₁).dynamic.at_p
                x room = true := by
        intro x hx hxType room htarget
        rcases List.mem_cons.mp hx with hxHead | hxTail
        · subst x
          have hpres :=
            hi.2.2.2.2 head room hheadNotMem
          rw [hpres]
          exact hpTarget room htarget
        · have hxType₁ : s₁.statics.obj_t x = true := by
            rw [hstat₁]
            exact hxType
          exact hi.2.2.2.1 x hxTail hxType₁ room htarget

      have hpreserves :
          ∀ x room, x ∉ head :: tail →
            (runPlan (gpSolveAux g tail s₁) s₁).dynamic.at_p x room =
              s.dynamic.at_p x room := by
        intro x room hx
        have hxne : x ≠ head := by
          intro hxh
          apply hx
          simp [hxh]
        have hxnotTail : x ∉ tail := by
          intro hxTail
          apply hx
          simp [hxTail]
        rw [hi.2.2.2.2 x room hxnotTail]
        exact hpPreserve x room hxne

      have hresult :
          ValidPlan (p ++ gpSolveAux g tail s₁) s ∧
          WellFormed
            (runPlan (gpSolveAux g tail s₁) s₁) ∧
          InitAllGrippersFree
            (runPlan (gpSolveAux g tail s₁) s₁) ∧
          (∀ x, x ∈ head :: tail → s.statics.obj_t x = true →
            ∀ room, g.dynamic.at_p x room = some true →
              (runPlan (gpSolveAux g tail s₁) s₁).dynamic.at_p
                x room = true) ∧
          (∀ x room, x ∉ head :: tail →
            (runPlan (gpSolveAux g tail s₁) s₁).dynamic.at_p x room =
              s.dynamic.at_p x room) :=
        ⟨hvalid, hfinalWf, hfinalFree, htargets, hpreserves⟩

      simpa [gpSolveAux, p, s₁, runPlan_append] using hresult


-- Main correctness proof

theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  have hwf : WellFormed s := hinit.1
  have hfree : InitAllGrippersFree s := hinit.2.1
  have haux :=
    gpSolveAux_correct g s.statics.objects s
      hwf hfree hgoal hstatic.1

  have hgoal' := hgoal
  rcases hgoal' with
    ⟨_, _, hvalidGoalAt, _, _, _, _, _, _, _, _, hignoreAtRobby,
      hignoreFree, hignoreCarry, hpositive, _⟩

  refine ⟨?_, ?_⟩
  · simpa [solve] using haux.1
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro r room
      simp [hignoreAtRobby r room]
    · intro o room
      cases hopt : g.dynamic.at_p o room with
      | none =>
          simp [hopt]
      | some b =>
          cases b with
          | false =>
              exact False.elim (hpositive o room hopt)
          | true =>
              have htypes := hvalidGoalAt o room hopt
              have hoType : s.statics.obj_t o = true := htypes.1
              have hoMem : o ∈ s.statics.objects :=
                object_mem_of_type hstatic hoType
              have htarget :=
                haux.2.2.2.1 o hoMem hoType room hopt
              simpa [solve, hopt] using htarget
    · intro r gr
      simp [hignoreFree r gr]
    · intro r o gr
      simp [hignoreCarry r o gr]

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

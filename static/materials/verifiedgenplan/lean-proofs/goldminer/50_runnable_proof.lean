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
  bomb_at_p : Obj → Bool
  connected_p : Obj → Obj → Bool
  loc_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  robot_at_p : Obj → α
  laser_at_p : Obj → α
  soft_rock_at_p : Obj → α
  hard_rock_at_p : Obj → α
  gold_at_p : Obj → α
  arm_empty_p : α
  holds_bomb_p : α
  holds_laser_p : α
  holds_gold_p : α
  clear_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidBombAtParam (s : StaticState) : Prop :=
  ∀ var_x, s.bomb_at_p var_x = true → s.loc_t var_x = true

def ValidConnectedParam (s : StaticState) : Prop :=
  ∀ var_x var_y, s.connected_p var_x var_y = true → s.loc_t var_x = true ∧ s.loc_t var_y = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.loc_t x = true → x ∈ s.objects)

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects → s.loc_t x = true

def ConnectedSymmetric (s : StaticState) : Prop :=
  ∀ x y, s.connected_p x y = true → s.connected_p y x = true

def ConnectedGraphConnected (s : StaticState) : Prop :=
  ∀ x y, s.loc_t x = true → s.loc_t y = true →
    Relation.ReflTransGen (fun a b => s.connected_p a b = true) x y

def MinLoc (s : StaticState) : Prop :=
  ∃ x, s.loc_t x = true

def BombAtUnique (s : StaticState) : Prop :=
  ∀ x y, s.bomb_at_p x = true → s.bomb_at_p y = true → x = y

def BombAtExists (s : StaticState) : Prop :=
  ∃ x, s.bomb_at_p x = true

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidBombAtParam s ∧
  ValidConnectedParam s ∧
  ValidTypeHierarchy s ∧
  TypeCoverage s ∧
  ConnectedSymmetric s ∧
  ConnectedGraphConnected s ∧
  MinLoc s ∧
  BombAtUnique s ∧
  BombAtExists s

def ValidRobotAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.robot_at_p var_x) → s.loc_t var_x = true

def ValidLaserAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.laser_at_p var_x) → s.loc_t var_x = true

def ValidSoftRockAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.soft_rock_at_p var_x) → s.loc_t var_x = true

def ValidHardRockAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.hard_rock_at_p var_x) → s.loc_t var_x = true

def ValidGoldAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.gold_at_p var_x) → s.loc_t var_x = true

def ValidClearParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.clear_p var_x) → s.loc_t var_x = true

def RobotAtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y, Truthy.isTrue (d.robot_at_p x) → Truthy.isTrue (d.robot_at_p y) → x = y

def LaserAtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y, Truthy.isTrue (d.laser_at_p x) → Truthy.isTrue (d.laser_at_p y) → x = y

def GoldAtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y, Truthy.isTrue (d.gold_at_p x) → Truthy.isTrue (d.gold_at_p y) → x = y

def ClearImpliesNoRock {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, Truthy.isTrue (d.clear_p x) →
    ¬ Truthy.isTrue (d.soft_rock_at_p x) ∧ ¬ Truthy.isTrue (d.hard_rock_at_p x)

def SoftHardRockExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, ¬ (Truthy.isTrue (d.soft_rock_at_p x) ∧ Truthy.isTrue (d.hard_rock_at_p x))

def RobotAtImpliesClear {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, Truthy.isTrue (d.robot_at_p x) → Truthy.isTrue (d.clear_p x)

def ArmEmptyIffNoneHeld (s : State) : Prop :=
  s.dynamic.arm_empty_p = true ↔
    ¬ (s.dynamic.holds_bomb_p = true ∨ s.dynamic.holds_laser_p = true ∨ s.dynamic.holds_gold_p = true)

def HeldAtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ¬ (Truthy.isTrue d.holds_bomb_p ∧ Truthy.isTrue d.holds_laser_p) ∧
  ¬ (Truthy.isTrue d.holds_bomb_p ∧ Truthy.isTrue d.holds_gold_p) ∧
  ¬ (Truthy.isTrue d.holds_laser_p ∧ Truthy.isTrue d.holds_gold_p)

def LaserAtXorHeld (s : State) : Prop :=
  (∃ x, s.dynamic.laser_at_p x = true) ↔ ¬ s.dynamic.holds_laser_p = true

def RobotAtExists (s : State) : Prop :=
  ∃ x, s.dynamic.robot_at_p x = true

def TerrainCoverage (s : State) : Prop :=
  ∀ x, s.statics.loc_t x = true →
    s.dynamic.clear_p x = true ∨ s.dynamic.soft_rock_at_p x = true ∨ s.dynamic.hard_rock_at_p x = true

def InitTerrainPartition (s : State) : Prop :=
  ∀ x, s.statics.loc_t x = true →
    (s.dynamic.clear_p x = true ∨ s.dynamic.soft_rock_at_p x = true ∨ s.dynamic.hard_rock_at_p x = true) ∧
    ¬ (s.dynamic.clear_p x = true ∧ s.dynamic.soft_rock_at_p x = true) ∧
    ¬ (s.dynamic.clear_p x = true ∧ s.dynamic.hard_rock_at_p x = true) ∧
    ¬ (s.dynamic.soft_rock_at_p x = true ∧ s.dynamic.hard_rock_at_p x = true)

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidRobotAtParam s.statics s.dynamic ∧
  ValidLaserAtParam s.statics s.dynamic ∧
  ValidSoftRockAtParam s.statics s.dynamic ∧
  ValidHardRockAtParam s.statics s.dynamic ∧
  ValidGoldAtParam s.statics s.dynamic ∧
  ValidClearParam s.statics s.dynamic ∧
  RobotAtMostOne s.statics s.dynamic ∧
  LaserAtMostOne s.statics s.dynamic ∧
  GoldAtMostOne s.statics s.dynamic ∧
  ClearImpliesNoRock s.statics s.dynamic ∧
  SoftHardRockExclusive s.statics s.dynamic ∧
  RobotAtImpliesClear s.statics s.dynamic ∧
  HeldAtMostOne s.statics s.dynamic ∧
  ArmEmptyIffNoneHeld s ∧
  LaserAtXorHeld s ∧
  RobotAtExists s ∧
  TerrainCoverage s ∧
  InitTerrainPartition s

def InitArmEmpty (s : State) : Prop :=
  s.dynamic.arm_empty_p = true

def InitRobotAtClear (s : State) : Prop :=
  ∀ x, s.dynamic.robot_at_p x = true → s.dynamic.clear_p x = true

def InitLaserAtBombLocation (s : State) : Prop :=
  ∀ x, s.dynamic.laser_at_p x = true ↔ s.statics.bomb_at_p x = true

def InitGoldNotAtHardRock (s : State) : Prop :=
  ∀ x, s.dynamic.gold_at_p x = true → s.dynamic.hard_rock_at_p x = false

def InitClearPathToBombLaser (s : State) : Prop :=
  ∀ r bl, s.dynamic.robot_at_p r = true → s.statics.bomb_at_p bl = true →
    Relation.ReflTransGen (fun a b => s.statics.connected_p a b = true ∧ s.dynamic.clear_p b = true) r bl

def InitGoldExists (s : State) : Prop :=
  ∃ x, s.dynamic.gold_at_p x = true

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitArmEmpty s ∧
  InitRobotAtClear s ∧
  InitLaserAtBombLocation s ∧
  InitGoldNotAtHardRock s ∧
  InitClearPathToBombLaser s ∧
  InitGoldExists s

def GoalIgnoreRobotAt (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.robot_at_p x = none

def GoalIgnoreLaserAt (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.laser_at_p x = none

def GoalIgnoreSoftRockAt (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.soft_rock_at_p x = none

def GoalIgnoreHardRockAt (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.hard_rock_at_p x = none

def GoalIgnoreGoldAt (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.gold_at_p x = none

def GoalIgnoreArmEmpty (initial : State) (g : Goal) : Prop :=
  g.dynamic.arm_empty_p = none

def GoalIgnoreHoldsBomb (initial : State) (g : Goal) : Prop :=
  g.dynamic.holds_bomb_p = none

def GoalIgnoreHoldsLaser (initial : State) (g : Goal) : Prop :=
  g.dynamic.holds_laser_p = none

def GoalIgnoreClear (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.clear_p x = none

def GoalHoldsGoldRequired (initial : State) (g : Goal) : Prop :=
  g.dynamic.holds_gold_p = some true

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidRobotAtParam initial.statics g.dynamic ∧
  ValidLaserAtParam initial.statics g.dynamic ∧
  ValidSoftRockAtParam initial.statics g.dynamic ∧
  ValidHardRockAtParam initial.statics g.dynamic ∧
  ValidGoldAtParam initial.statics g.dynamic ∧
  ValidClearParam initial.statics g.dynamic ∧
  RobotAtMostOne initial.statics g.dynamic ∧
  LaserAtMostOne initial.statics g.dynamic ∧
  GoldAtMostOne initial.statics g.dynamic ∧
  ClearImpliesNoRock initial.statics g.dynamic ∧
  SoftHardRockExclusive initial.statics g.dynamic ∧
  RobotAtImpliesClear initial.statics g.dynamic ∧
  HeldAtMostOne initial.statics g.dynamic ∧
  GoalIgnoreRobotAt initial g ∧
  GoalIgnoreLaserAt initial g ∧
  GoalIgnoreSoftRockAt initial g ∧
  GoalIgnoreHardRockAt initial g ∧
  GoalIgnoreGoldAt initial g ∧
  GoalIgnoreArmEmpty initial g ∧
  GoalIgnoreHoldsBomb initial g ∧
  GoalIgnoreHoldsLaser initial g ∧
  GoalIgnoreClear initial g ∧
  GoalHoldsGoldRequired initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_x,
    match g.dynamic.robot_at_p var_x with
    | none => True
    | some b => s.dynamic.robot_at_p var_x = b) ∧
  (∀ var_x,
    match g.dynamic.laser_at_p var_x with
    | none => True
    | some b => s.dynamic.laser_at_p var_x = b) ∧
  (∀ var_x,
    match g.dynamic.soft_rock_at_p var_x with
    | none => True
    | some b => s.dynamic.soft_rock_at_p var_x = b) ∧
  (∀ var_x,
    match g.dynamic.hard_rock_at_p var_x with
    | none => True
    | some b => s.dynamic.hard_rock_at_p var_x = b) ∧
  (∀ var_x,
    match g.dynamic.gold_at_p var_x with
    | none => True
    | some b => s.dynamic.gold_at_p var_x = b) ∧
  (match g.dynamic.arm_empty_p with
  | none => True
  | some b => s.dynamic.arm_empty_p = b) ∧
  (match g.dynamic.holds_bomb_p with
  | none => True
  | some b => s.dynamic.holds_bomb_p = b) ∧
  (match g.dynamic.holds_laser_p with
  | none => True
  | some b => s.dynamic.holds_laser_p = b) ∧
  (match g.dynamic.holds_gold_p with
  | none => True
  | some b => s.dynamic.holds_gold_p = b) ∧
  (∀ var_x,
    match g.dynamic.clear_p var_x with
    | none => True
    | some b => s.dynamic.clear_p var_x = b)

def movePre (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.statics.loc_t var_y = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.statics.connected_p var_x var_y = true ∧
  s.dynamic.clear_p var_y = true

def pickup_laserPre (var_x : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.dynamic.laser_at_p var_x = true ∧
  s.dynamic.arm_empty_p = true

def pickup_bombPre (var_x : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.statics.bomb_at_p var_x = true ∧
  s.dynamic.arm_empty_p = true

def putdown_laserPre (var_x : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.dynamic.holds_laser_p = true

def detonate_bombPre (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.statics.loc_t var_y = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.dynamic.holds_bomb_p = true ∧
  s.statics.connected_p var_x var_y = true ∧
  s.dynamic.soft_rock_at_p var_y = true

def fire_laserPre (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.statics.loc_t var_y = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.dynamic.holds_laser_p = true ∧
  s.statics.connected_p var_x var_y = true

def pick_goldPre (var_x : Obj) (s : State) : Prop :=
  s.statics.loc_t var_x = true ∧
  s.dynamic.robot_at_p var_x = true ∧
  s.dynamic.arm_empty_p = true ∧
  s.dynamic.gold_at_p var_x = true

def move (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    robot_at_p :=
      fun var_y' =>
        if var_y' = var_y then
          true
        else if var_y' = var_x then
          false
        else
          s.dynamic.robot_at_p var_y'
  }
}

def pickup_laser (var_x : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    laser_at_p :=
      fun var_x' =>
        if var_x' = var_x then
          false
        else
          s.dynamic.laser_at_p var_x',
    arm_empty_p := false,
    holds_laser_p := true
  }
}

def pickup_bomb (var_x : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    arm_empty_p := false,
    holds_bomb_p := true
  }
}

def putdown_laser (var_x : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    laser_at_p :=
      fun var_x' =>
        if var_x' = var_x then
          true
        else
          s.dynamic.laser_at_p var_x',
    arm_empty_p := true,
    holds_laser_p := false
  }
}

def detonate_bomb (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    soft_rock_at_p :=
      fun var_y' =>
        if var_y' = var_y then
          false
        else
          s.dynamic.soft_rock_at_p var_y',
    arm_empty_p := true,
    holds_bomb_p := false,
    clear_p :=
      fun var_y' =>
        if var_y' = var_y then
          true
        else
          s.dynamic.clear_p var_y'
  }
}

def fire_laser (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    soft_rock_at_p :=
      fun var_y' =>
        if var_y' = var_y then
          false
        else
          s.dynamic.soft_rock_at_p var_y',
    hard_rock_at_p :=
      fun var_y' =>
        if var_y' = var_y then
          false
        else
          s.dynamic.hard_rock_at_p var_y',
    gold_at_p :=
      fun var_y' =>
        if var_y' = var_y then
          false
        else
          s.dynamic.gold_at_p var_y',
    clear_p :=
      fun var_y' =>
        if var_y' = var_y then
          true
        else
          s.dynamic.clear_p var_y'
  }
}

def pick_gold (var_x : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    arm_empty_p := false,
    holds_gold_p := true
  }
}

inductive PlanAction where
  | move          (var_x : Obj) (var_y : Obj)
  | pickup_laser  (var_x : Obj)
  | pickup_bomb   (var_x : Obj)
  | putdown_laser (var_x : Obj)
  | detonate_bomb (var_x : Obj) (var_y : Obj)
  | fire_laser    (var_x : Obj) (var_y : Obj)
  | pick_gold     (var_x : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .move          var_x var_y, s => movePre var_x var_y s
  | .pickup_laser  var_x      , s => pickup_laserPre var_x s
  | .pickup_bomb   var_x      , s => pickup_bombPre var_x s
  | .putdown_laser var_x      , s => putdown_laserPre var_x s
  | .detonate_bomb var_x var_y, s => detonate_bombPre var_x var_y s
  | .fire_laser    var_x var_y, s => fire_laserPre var_x var_y s
  | .pick_gold     var_x      , s => pick_goldPre var_x s

def actionApply : PlanAction → State → State
  | .move          var_x var_y, s => move var_x var_y s
  | .pickup_laser  var_x      , s => pickup_laser var_x s
  | .pickup_bomb   var_x      , s => pickup_bomb var_x s
  | .putdown_laser var_x      , s => putdown_laser var_x s
  | .detonate_bomb var_x var_y, s => detonate_bomb var_x var_y s
  | .fire_laser    var_x var_y, s => fire_laser var_x var_y s
  | .pick_gold     var_x      , s => pick_gold var_x s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Find the first object satisfying a Boolean predicate.
def gpFindObj? : List Obj → (Obj → Bool) → Option Obj
  | [], _ => none
  | x :: xs, p =>
      if p x then
        some x
      else
        gpFindObj? xs p

def gpFindRobot? (s : State) : Option Obj :=
  gpFindObj? s.statics.objects s.dynamic.robot_at_p

def gpFindGold? (s : State) : Option Obj :=
  gpFindObj? s.statics.objects s.dynamic.gold_at_p

def gpFindBomb? (s : State) : Option Obj :=
  gpFindObj? s.statics.objects s.statics.bomb_at_p

-- Convert a path [x₀, x₁, ..., xₙ] into move actions.
def gpPathMovesFrom (x : Obj) : List Obj → List PlanAction
  | [] => []
  | y :: ys =>
      PlanAction.move x y :: gpPathMovesFrom y ys

def gpPathMoves : List Obj → List PlanAction
  | [] => []
  | x :: xs => gpPathMovesFrom x xs

-- Return the unvisited clear neighbors of a location.
def gpFreshClearNeighbors
    (s : State)
    (current : Obj)
    (visited : List Obj) : List Obj :=
  s.statics.objects.filter (fun next =>
    s.statics.connected_p current next &&
    s.dynamic.clear_p next &&
    !(visited.contains next))

-- Breadth-first search for a clear path.
-- Paths stored in the queue are reversed.
def gpClearPathBfs
    (s : State)
    (goal : Obj)
    (fuel : Nat)
    (queue : List (Obj × List Obj))
    (visited : List Obj) : Option (List Obj) :=
  match fuel with
  | 0 => none
  | Nat.succ fuel' =>
      match queue with
      | [] => none
      | (current, reversePath) :: rest =>
          if current == goal then
            some reversePath.reverse
          else
            let neighbors :=
              gpFreshClearNeighbors s current visited
            let newEntries :=
              neighbors.map (fun next => (next, next :: reversePath))
            gpClearPathBfs
              s
              goal
              fuel'
              (rest ++ newEntries)
              (visited ++ neighbors)
termination_by fuel

def gpFindClearPath
    (s : State)
    (start goal : Obj) : Option (List Obj) :=
  gpClearPathBfs
    s
    goal
    (s.statics.objects.length + 1)
    [(start, [start])]
    [start]

-- Find a reachable clear location adjacent to a target.
def gpFindReachableNeighborAux
    (s : State)
    (start target : Obj) :
    List Obj → Option (Obj × List Obj)
  | [] => none
  | candidate :: rest =>
      if s.dynamic.clear_p candidate &&
          s.statics.connected_p candidate target then
        match gpFindClearPath s start candidate with
        | some path => some (candidate, path)
        | none =>
            gpFindReachableNeighborAux s start target rest
      else
        gpFindReachableNeighborAux s start target rest

def gpFindReachableNeighbor
    (s : State)
    (start target : Obj) : Option (Obj × List Obj) :=
  gpFindReachableNeighborAux
    s
    start
    target
    s.statics.objects

structure GPFrontier where
  target : Obj
  neighbor : Obj
  path : List Obj

-- Find a non-gold obstacle adjacent to the reachable clear region.
def gpFindLaserTargetAux
    (s : State)
    (start gold : Obj) :
    List Obj → Option GPFrontier
  | [] => none
  | target :: rest =>
      if (!(target == gold)) &&
          (s.dynamic.soft_rock_at_p target ||
           s.dynamic.hard_rock_at_p target) then
        match gpFindReachableNeighbor s start target with
        | some (neighbor, path) =>
            some {
              target := target
              neighbor := neighbor
              path := path
            }
        | none =>
            gpFindLaserTargetAux s start gold rest
      else
        gpFindLaserTargetAux s start gold rest

def gpFindLaserTarget
    (s : State)
    (start gold : Obj) : Option GPFrontier :=
  gpFindLaserTargetAux
    s
    start
    gold
    s.statics.objects

-- Fetch and detonate the bomb at a soft-rock gold location.
def gpBombFinishPlan
    (s : State)
    (bomb gold neighbor : Obj) : List PlanAction :=
  match gpFindRobot? s with
  | none => []
  | some robot =>
      match gpFindClearPath s robot bomb with
      | none => []
      | some pathToBomb =>
          let toBomb := gpPathMoves pathToBomb
          let pickupAction := PlanAction.pickup_bomb bomb
          let initialActions := toBomb ++ [pickupAction]
          let afterPickup := runPlan initialActions s
          match gpFindClearPath afterPickup bomb neighbor with
          | none => []
          | some pathToNeighbor =>
              initialActions ++
              gpPathMoves pathToNeighbor ++
              [ PlanAction.detonate_bomb neighbor gold
              , PlanAction.move neighbor gold
              , PlanAction.pick_gold gold
              ]

-- Repeatedly expand the reachable clear region using the laser.
def gpLaserLoop
    (bomb gold : Obj)
    (fuel : Nat)
    (s : State) : List PlanAction :=
  match fuel with
  | 0 => []
  | Nat.succ fuel' =>
      match gpFindRobot? s with
      | none => []
      | some robot =>
          match gpFindClearPath s robot gold with
          | some pathToGold =>
              [PlanAction.putdown_laser robot] ++
              gpPathMoves pathToGold ++
              [PlanAction.pick_gold gold]
          | none =>
              if s.dynamic.soft_rock_at_p gold then
                match gpFindReachableNeighbor s robot gold with
                | some (neighbor, _) =>
                    let putdownAction :=
                      PlanAction.putdown_laser robot
                    let afterPutdown :=
                      actionApply putdownAction s
                    [putdownAction] ++
                    gpBombFinishPlan
                      afterPutdown
                      bomb
                      gold
                      neighbor
                | none =>
                    match gpFindLaserTarget s robot gold with
                    | none => []
                    | some frontier =>
                        let laserActions :=
                          gpPathMoves frontier.path ++
                          [PlanAction.fire_laser
                            frontier.neighbor
                            frontier.target]
                        let nextState :=
                          runPlan laserActions s
                        laserActions ++
                        gpLaserLoop
                          bomb
                          gold
                          fuel'
                          nextState
              else
                match gpFindLaserTarget s robot gold with
                | none => []
                | some frontier =>
                    let laserActions :=
                      gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target]
                    let nextState :=
                      runPlan laserActions s
                    laserActions ++
                    gpLaserLoop
                      bomb
                      gold
                      fuel'
                      nextState
termination_by fuel

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  match gpFindRobot? s, gpFindBomb? s, gpFindGold? s with
  | some robot, some bomb, some gold =>
      match gpFindClearPath s robot gold with
      | some pathToGold =>
          gpPathMoves pathToGold ++
          [PlanAction.pick_gold gold]
      | none =>
          if s.dynamic.soft_rock_at_p gold then
            match gpFindReachableNeighbor s robot gold with
            | some (neighbor, _) =>
                gpBombFinishPlan s bomb gold neighbor
            | none =>
                match gpFindClearPath s robot bomb with
                | none => []
                | some pathToBomb =>
                    let initialActions :=
                      gpPathMoves pathToBomb ++
                      [PlanAction.pickup_laser bomb]
                    let afterPickup :=
                      runPlan initialActions s
                    initialActions ++
                    gpLaserLoop
                      bomb
                      gold
                      (s.statics.objects.length + 1)
                      afterPickup
          else
            match gpFindClearPath s robot bomb with
            | none => []
            | some pathToBomb =>
                let initialActions :=
                  gpPathMoves pathToBomb ++
                  [PlanAction.pickup_laser bomb]
                let afterPickup :=
                  runPlan initialActions s
                initialActions ++
                gpLaserLoop
                  bomb
                  gold
                  (s.statics.objects.length + 1)
                  afterPickup
  | _, _, _ => []

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

lemma move_statics (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).statics = s.statics := rfl

lemma pickup_laser_statics (var_x : Obj) (s : State) :
    (pickup_laser var_x s).statics = s.statics := rfl

lemma pickup_bomb_statics (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).statics = s.statics := rfl

lemma putdown_laser_statics (var_x : Obj) (s : State) :
    (putdown_laser var_x s).statics = s.statics := rfl

lemma detonate_bomb_statics (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).statics = s.statics := rfl

lemma fire_laser_statics (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).statics = s.statics := rfl

lemma pick_gold_statics (var_x : Obj) (s : State) :
    (pick_gold var_x s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | move var_x var_y          => exact move_statics var_x var_y s
      | pickup_laser var_x        => exact pickup_laser_statics var_x s
      | pickup_bomb var_x         => exact pickup_bomb_statics var_x s
      | putdown_laser var_x       => exact putdown_laser_statics var_x s
      | detonate_bomb var_x var_y => exact detonate_bomb_statics var_x var_y s
      | fire_laser var_x var_y    => exact fire_laser_statics var_x var_y s
      | pick_gold var_x           => exact pick_gold_statics var_x s

-- move only touches robot_at_p
lemma move_robot_at_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) (h2 : var_y' ≠ var_x) :
    (move var_x var_y s).dynamic.robot_at_p var_y' = s.dynamic.robot_at_p var_y' := by
  unfold move
  simp [h1, h2]

-- move never touches laser_at_p
lemma move_laser_at_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.laser_at_p = s.dynamic.laser_at_p := rfl

-- move never touches soft_rock_at_p
lemma move_soft_rock_at_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p := rfl

-- move never touches hard_rock_at_p
lemma move_hard_rock_at_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- move never touches gold_at_p
lemma move_gold_at_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- move never touches arm_empty_p
lemma move_arm_empty_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.arm_empty_p = s.dynamic.arm_empty_p := rfl

-- move never touches holds_bomb_p
lemma move_holds_bomb_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.holds_bomb_p = s.dynamic.holds_bomb_p := rfl

-- move never touches holds_laser_p
lemma move_holds_laser_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.holds_laser_p = s.dynamic.holds_laser_p := rfl

-- move never touches holds_gold_p
lemma move_holds_gold_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- move never touches clear_p
lemma move_clear_p (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.clear_p = s.dynamic.clear_p := rfl

-- pickup_laser only touches laser_at_p
lemma pickup_laser_laser_at_p_ne (var_x : Obj) (s : State) {var_x' : Obj} (h1 : var_x' ≠ var_x) :
    (pickup_laser var_x s).dynamic.laser_at_p var_x' = s.dynamic.laser_at_p var_x' := by
  unfold pickup_laser
  simp [h1]

-- pickup_laser never touches robot_at_p
lemma pickup_laser_robot_at_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- pickup_laser never touches soft_rock_at_p
lemma pickup_laser_soft_rock_at_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p := rfl

-- pickup_laser never touches hard_rock_at_p
lemma pickup_laser_hard_rock_at_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- pickup_laser never touches gold_at_p
lemma pickup_laser_gold_at_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- pickup_laser never touches holds_bomb_p
lemma pickup_laser_holds_bomb_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.holds_bomb_p = s.dynamic.holds_bomb_p := rfl

-- pickup_laser never touches holds_gold_p
lemma pickup_laser_holds_gold_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- pickup_laser never touches clear_p
lemma pickup_laser_clear_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.clear_p = s.dynamic.clear_p := rfl

-- pickup_bomb never touches robot_at_p
lemma pickup_bomb_robot_at_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- pickup_bomb never touches laser_at_p
lemma pickup_bomb_laser_at_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.laser_at_p = s.dynamic.laser_at_p := rfl

-- pickup_bomb never touches soft_rock_at_p
lemma pickup_bomb_soft_rock_at_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p := rfl

-- pickup_bomb never touches hard_rock_at_p
lemma pickup_bomb_hard_rock_at_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- pickup_bomb never touches gold_at_p
lemma pickup_bomb_gold_at_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- pickup_bomb never touches holds_laser_p
lemma pickup_bomb_holds_laser_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.holds_laser_p = s.dynamic.holds_laser_p := rfl

-- pickup_bomb never touches holds_gold_p
lemma pickup_bomb_holds_gold_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- pickup_bomb never touches clear_p
lemma pickup_bomb_clear_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.clear_p = s.dynamic.clear_p := rfl

-- putdown_laser only touches laser_at_p
lemma putdown_laser_laser_at_p_ne (var_x : Obj) (s : State) {var_x' : Obj} (h1 : var_x' ≠ var_x) :
    (putdown_laser var_x s).dynamic.laser_at_p var_x' = s.dynamic.laser_at_p var_x' := by
  unfold putdown_laser
  simp [h1]

-- putdown_laser never touches robot_at_p
lemma putdown_laser_robot_at_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- putdown_laser never touches soft_rock_at_p
lemma putdown_laser_soft_rock_at_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p := rfl

-- putdown_laser never touches hard_rock_at_p
lemma putdown_laser_hard_rock_at_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- putdown_laser never touches gold_at_p
lemma putdown_laser_gold_at_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- putdown_laser never touches holds_bomb_p
lemma putdown_laser_holds_bomb_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.holds_bomb_p = s.dynamic.holds_bomb_p := rfl

-- putdown_laser never touches holds_gold_p
lemma putdown_laser_holds_gold_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- putdown_laser never touches clear_p
lemma putdown_laser_clear_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.clear_p = s.dynamic.clear_p := rfl

-- detonate_bomb only touches clear_p, soft_rock_at_p
lemma detonate_bomb_soft_rock_at_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (detonate_bomb var_x var_y s).dynamic.soft_rock_at_p var_y' = s.dynamic.soft_rock_at_p var_y' := by
  unfold detonate_bomb
  simp [h1]

lemma detonate_bomb_clear_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (detonate_bomb var_x var_y s).dynamic.clear_p var_y' = s.dynamic.clear_p var_y' := by
  unfold detonate_bomb
  simp [h1]

-- detonate_bomb never touches robot_at_p
lemma detonate_bomb_robot_at_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- detonate_bomb never touches laser_at_p
lemma detonate_bomb_laser_at_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.laser_at_p = s.dynamic.laser_at_p := rfl

-- detonate_bomb never touches hard_rock_at_p
lemma detonate_bomb_hard_rock_at_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- detonate_bomb never touches gold_at_p
lemma detonate_bomb_gold_at_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- detonate_bomb never touches holds_laser_p
lemma detonate_bomb_holds_laser_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.holds_laser_p = s.dynamic.holds_laser_p := rfl

-- detonate_bomb never touches holds_gold_p
lemma detonate_bomb_holds_gold_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- fire_laser only touches clear_p, soft_rock_at_p, gold_at_p, hard_rock_at_p
lemma fire_laser_soft_rock_at_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (fire_laser var_x var_y s).dynamic.soft_rock_at_p var_y' = s.dynamic.soft_rock_at_p var_y' := by
  unfold fire_laser
  simp [h1]

lemma fire_laser_hard_rock_at_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (fire_laser var_x var_y s).dynamic.hard_rock_at_p var_y' = s.dynamic.hard_rock_at_p var_y' := by
  unfold fire_laser
  simp [h1]

lemma fire_laser_gold_at_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (fire_laser var_x var_y s).dynamic.gold_at_p var_y' = s.dynamic.gold_at_p var_y' := by
  unfold fire_laser
  simp [h1]

lemma fire_laser_clear_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (fire_laser var_x var_y s).dynamic.clear_p var_y' = s.dynamic.clear_p var_y' := by
  unfold fire_laser
  simp [h1]

-- fire_laser never touches robot_at_p
lemma fire_laser_robot_at_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- fire_laser never touches laser_at_p
lemma fire_laser_laser_at_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.laser_at_p = s.dynamic.laser_at_p := rfl

-- fire_laser never touches arm_empty_p
lemma fire_laser_arm_empty_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.arm_empty_p = s.dynamic.arm_empty_p := rfl

-- fire_laser never touches holds_bomb_p
lemma fire_laser_holds_bomb_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.holds_bomb_p = s.dynamic.holds_bomb_p := rfl

-- fire_laser never touches holds_laser_p
lemma fire_laser_holds_laser_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.holds_laser_p = s.dynamic.holds_laser_p := rfl

-- fire_laser never touches holds_gold_p
lemma fire_laser_holds_gold_p (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.holds_gold_p = s.dynamic.holds_gold_p := rfl

-- pick_gold never touches robot_at_p
lemma pick_gold_robot_at_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.robot_at_p = s.dynamic.robot_at_p := rfl

-- pick_gold never touches laser_at_p
lemma pick_gold_laser_at_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.laser_at_p = s.dynamic.laser_at_p := rfl

-- pick_gold never touches soft_rock_at_p
lemma pick_gold_soft_rock_at_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p := rfl

-- pick_gold never touches hard_rock_at_p
lemma pick_gold_hard_rock_at_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p := rfl

-- pick_gold never touches gold_at_p
lemma pick_gold_gold_at_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.gold_at_p = s.dynamic.gold_at_p := rfl

-- pick_gold never touches holds_bomb_p
lemma pick_gold_holds_bomb_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.holds_bomb_p = s.dynamic.holds_bomb_p := rfl

-- pick_gold never touches holds_laser_p
lemma pick_gold_holds_laser_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.holds_laser_p = s.dynamic.holds_laser_p := rfl

-- pick_gold never touches clear_p
lemma pick_gold_clear_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.clear_p = s.dynamic.clear_p := rfl

lemma move_robot_at_p_eq1 (var_x var_y : Obj) (s : State) :
    (move var_x var_y s).dynamic.robot_at_p var_y = true := by
  unfold move
  simp

lemma move_robot_at_p_eq2 (var_x var_y : Obj) (s : State) (h1 : var_x ≠ var_y) :
    (move var_x var_y s).dynamic.robot_at_p var_x = false := by
  unfold move
  simp [h1]

lemma pickup_laser_laser_at_p_eq1 (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.laser_at_p var_x = false := by
  unfold pickup_laser
  simp

lemma pickup_laser_arm_empty_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.arm_empty_p = false := by
  unfold pickup_laser
  simp

lemma pickup_laser_holds_laser_p (var_x : Obj) (s : State) :
    (pickup_laser var_x s).dynamic.holds_laser_p = true := by
  unfold pickup_laser
  simp

lemma pickup_bomb_arm_empty_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.arm_empty_p = false := by
  unfold pickup_bomb
  simp

lemma pickup_bomb_holds_bomb_p (var_x : Obj) (s : State) :
    (pickup_bomb var_x s).dynamic.holds_bomb_p = true := by
  unfold pickup_bomb
  simp

lemma putdown_laser_laser_at_p_eq1 (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.laser_at_p var_x = true := by
  unfold putdown_laser
  simp

lemma putdown_laser_arm_empty_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.arm_empty_p = true := by
  unfold putdown_laser
  simp

lemma putdown_laser_holds_laser_p (var_x : Obj) (s : State) :
    (putdown_laser var_x s).dynamic.holds_laser_p = false := by
  unfold putdown_laser
  simp

lemma detonate_bomb_soft_rock_at_p_eq1 (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.soft_rock_at_p var_y = false := by
  unfold detonate_bomb
  simp

lemma detonate_bomb_arm_empty_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.arm_empty_p = true := by
  unfold detonate_bomb
  simp

lemma detonate_bomb_holds_bomb_p (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.holds_bomb_p = false := by
  unfold detonate_bomb
  simp

lemma detonate_bomb_clear_p_eq1 (var_x var_y : Obj) (s : State) :
    (detonate_bomb var_x var_y s).dynamic.clear_p var_y = true := by
  unfold detonate_bomb
  simp

lemma fire_laser_soft_rock_at_p_eq1 (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.soft_rock_at_p var_y = false := by
  unfold fire_laser
  simp

lemma fire_laser_hard_rock_at_p_eq1 (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.hard_rock_at_p var_y = false := by
  unfold fire_laser
  simp

lemma fire_laser_gold_at_p_eq1 (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.gold_at_p var_y = false := by
  unfold fire_laser
  simp

lemma fire_laser_clear_p_eq1 (var_x var_y : Obj) (s : State) :
    (fire_laser var_x var_y s).dynamic.clear_p var_y = true := by
  unfold fire_laser
  simp

lemma pick_gold_arm_empty_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.arm_empty_p = false := by
  unfold pick_gold
  simp

lemma pick_gold_holds_gold_p (var_x : Obj) (s : State) :
    (pick_gold var_x s).dynamic.holds_gold_p = true := by
  unfold pick_gold
  simp

lemma truthy_bool_iff_eq_true (b : Bool) :
    Truthy.isTrue b ↔ b = true := by
  rfl

lemma move_preserves_wf
    (var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre : movePre var_x var_y s) :
    WellFormed (move var_x var_y s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with ⟨hlocX, hlocY, hrobotX, hconn, hclearY⟩

  have hnewRobot :
      ∀ z, (move var_x var_y s).dynamic.robot_at_p z = true → z = var_y := by
    intro z hz
    by_contra hzy
    have hzx : z ≠ var_x := by
      intro h
      subst z
      simp [move, hzy] at hz
    have hzold : s.dynamic.robot_at_p z = true := by
      simpa [move, hzy, hzx] using hz
    exact hzx (hR1 z var_x hzold hrobotX)

  refine
    ⟨hstatic, ?_, hVL, hVS, hVH, hVG, hVC,
     ?_, hL1, hG1, hClear, hSH, ?_, hHeld,
     hArm, hLX, ?_, hTerrain, hPartition⟩
  · intro z hz
    rw [hnewRobot z hz]
    exact hlocY
  · intro a b ha hb
    rw [hnewRobot a ha, hnewRobot b hb]
  · intro z hz
    rw [hnewRobot z hz]
    exact hclearY
  · exact ⟨var_y, move_robot_at_p_eq1 var_x var_y s⟩

lemma pickup_laser_preserves_wf
    (var_x)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pickup_laserPre var_x s) :
    WellFormed (pickup_laser var_x s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with ⟨hlocX, hrobotX, hlaserX, harmEmpty⟩

  have hnoneHeld :
      ¬ (s.dynamic.holds_bomb_p = true ∨
         s.dynamic.holds_laser_p = true ∨
         s.dynamic.holds_gold_p = true) :=
    hArm.mp harmEmpty
  have hnoBomb : ¬ s.dynamic.holds_bomb_p = true := by
    intro h
    exact hnoneHeld (Or.inl h)
  have hnoLaserHeld : ¬ s.dynamic.holds_laser_p = true := by
    intro h
    exact hnoneHeld (Or.inr (Or.inl h))
  have hnoGold : ¬ s.dynamic.holds_gold_p = true := by
    intro h
    exact hnoneHeld (Or.inr (Or.inr h))

  have laser_old_of_new :
      ∀ z,
        (pickup_laser var_x s).dynamic.laser_at_p z = true →
        s.dynamic.laser_at_p z = true := by
    intro z hz
    by_cases hzx : z = var_x
    · subst z
      simp [pickup_laser] at hz
    · simpa [pickup_laser, hzx] using hz

  have hnoNewLaser :
      ¬ ∃ z, (pickup_laser var_x s).dynamic.laser_at_p z = true := by
    rintro ⟨z, hz⟩
    have hzold := laser_old_of_new z hz
    have hzx : z = var_x := hL1 z var_x hzold hlaserX
    subst z
    simpa [pickup_laser] using hz

  refine
    ⟨hstatic, hVR, ?_, hVS, hVH, hVG, hVC,
     hR1, ?_, hG1, hClear, hSH, hRC, ?_,
     ?_, ?_, hRExists, hTerrain, hPartition⟩
  · intro z hz
    exact hVL z (laser_old_of_new z hz)
  · intro a b ha hb
    exact hL1 a b (laser_old_of_new a ha) (laser_old_of_new b hb)
  · simp [HeldAtMostOne, pickup_laser, truthy_bool_iff_eq_true,
      hnoBomb, hnoGold]
  · simp [ArmEmptyIffNoneHeld, pickup_laser]
  · unfold LaserAtXorHeld
    constructor
    · intro hex
      exact (hnoNewLaser hex).elim
    · intro h
      exfalso
      apply h
      simp [pickup_laser]

lemma pickup_bomb_preserves_wf
    (var_x)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pickup_bombPre var_x s) :
    WellFormed (pickup_bomb var_x s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with ⟨hlocX, hrobotX, hbombAtX, harmEmpty⟩

  have hnoneHeld :
      ¬ (s.dynamic.holds_bomb_p = true ∨
         s.dynamic.holds_laser_p = true ∨
         s.dynamic.holds_gold_p = true) :=
    hArm.mp harmEmpty
  have hnoLaser : ¬ s.dynamic.holds_laser_p = true := by
    intro h
    exact hnoneHeld (Or.inr (Or.inl h))
  have hnoGold : ¬ s.dynamic.holds_gold_p = true := by
    intro h
    exact hnoneHeld (Or.inr (Or.inr h))

  refine
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, ?_,
     ?_, hLX, hRExists, hTerrain, hPartition⟩
  · simp [HeldAtMostOne, pickup_bomb, truthy_bool_iff_eq_true,
      hnoLaser, hnoGold]
  · simp [ArmEmptyIffNoneHeld, pickup_bomb]

lemma putdown_laser_preserves_wf
    (var_x)
    (s : State)
    (hwf : WellFormed s)
    (hpre : putdown_laserPre var_x s) :
    WellFormed (putdown_laser var_x s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with ⟨hlocX, hrobotX, hholdsLaser⟩

  have hnoBomb : ¬ s.dynamic.holds_bomb_p = true := by
    intro hb
    exact hHeld.1 ⟨hb, hholdsLaser⟩
  have hnoGold : ¬ s.dynamic.holds_gold_p = true := by
    intro hg
    exact hHeld.2.2 ⟨hholdsLaser, hg⟩
  have hnoOldLaser :
      ¬ ∃ z, s.dynamic.laser_at_p z = true := by
    intro hex
    exact (hLX.mp hex) hholdsLaser

  have hnewLaser :
      ∀ z, (putdown_laser var_x s).dynamic.laser_at_p z = true →
        z = var_x := by
    intro z hz
    by_contra hzx
    have hzold : s.dynamic.laser_at_p z = true := by
      simpa [putdown_laser, hzx] using hz
    exact hnoOldLaser ⟨z, hzold⟩

  refine
    ⟨hstatic, hVR, ?_, hVS, hVH, hVG, hVC,
     hR1, ?_, hG1, hClear, hSH, hRC, ?_,
     ?_, ?_, hRExists, hTerrain, hPartition⟩
  · intro z hz
    rw [hnewLaser z hz]
    exact hlocX
  · intro a b ha hb
    rw [hnewLaser a ha, hnewLaser b hb]
  · simp [HeldAtMostOne, putdown_laser, truthy_bool_iff_eq_true,
      hnoBomb, hnoGold]
  · simp [ArmEmptyIffNoneHeld, putdown_laser, hnoBomb, hnoGold]
  · unfold LaserAtXorHeld
    constructor
    · intro _
      simp [putdown_laser]
    · intro _
      exact ⟨var_x, by simp [putdown_laser]⟩

lemma detonate_bomb_preserves_wf
    (var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre : detonate_bombPre var_x var_y s) :
    WellFormed (detonate_bomb var_x var_y s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with
    ⟨hlocX, hlocY, hrobotX, hholdsBomb, hconn, hsoftY⟩

  have hnoLaser : ¬ s.dynamic.holds_laser_p = true := by
    intro hl
    exact hHeld.1 ⟨hholdsBomb, hl⟩
  have hnoGold : ¬ s.dynamic.holds_gold_p = true := by
    intro hg
    exact hHeld.2.1 ⟨hholdsBomb, hg⟩
  have hnoHardY : ¬ s.dynamic.hard_rock_at_p var_y = true := by
    intro hh
    exact hSH var_y ⟨hsoftY, hh⟩

  have soft_old_of_new :
      ∀ z,
        (detonate_bomb var_x var_y s).dynamic.soft_rock_at_p z = true →
        s.dynamic.soft_rock_at_p z = true := by
    intro z hz
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb] at hz
    · simpa [detonate_bomb, hzy] using hz

  refine
    ⟨hstatic, hVR, hVL, ?_, hVH, hVG, ?_,
     hR1, hL1, hG1, ?_, ?_, ?_, ?_,
     ?_, hLX, hRExists, ?_, ?_⟩
  · intro z hz
    exact hVS z (soft_old_of_new z hz)
  · intro z hz
    by_cases hzy : z = var_y
    · subst z
      exact hlocY
    · apply hVC z
      simpa [detonate_bomb, hzy] using hz
  · intro z hclear
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb, truthy_bool_iff_eq_true, hnoHardY]
    · have holdClear : s.dynamic.clear_p z = true := by
        simpa [detonate_bomb, hzy, truthy_bool_iff_eq_true] using hclear
      simpa [detonate_bomb, hzy, truthy_bool_iff_eq_true] using
        hClear z holdClear
  · intro z hrocks
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb, truthy_bool_iff_eq_true] at hrocks
    · apply hSH z
      simpa [detonate_bomb, hzy, truthy_bool_iff_eq_true] using hrocks
  · intro z hrobot
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb, truthy_bool_iff_eq_true]
    · have holdRobot : s.dynamic.robot_at_p z = true := by
        simpa [detonate_bomb, truthy_bool_iff_eq_true] using hrobot
      have holdClear := hRC z holdRobot
      simpa [detonate_bomb, hzy, truthy_bool_iff_eq_true] using holdClear
  · simp [HeldAtMostOne, detonate_bomb, truthy_bool_iff_eq_true,
      hnoLaser, hnoGold]
  · simp [ArmEmptyIffNoneHeld, detonate_bomb, hnoLaser, hnoGold]
  · intro z hloc
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb]
    · simpa [detonate_bomb, hzy] using hTerrain z hloc
  · intro z hloc
    by_cases hzy : z = var_y
    · subst z
      simp [detonate_bomb, hnoHardY]
    · simpa [detonate_bomb, hzy] using hPartition z hloc

lemma fire_laser_preserves_wf
    (var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre : fire_laserPre var_x var_y s) :
    WellFormed (fire_laser var_x var_y s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with
    ⟨hlocX, hlocY, hrobotX, hholdsLaser, hconn⟩

  have soft_old_of_new :
      ∀ z,
        (fire_laser var_x var_y s).dynamic.soft_rock_at_p z = true →
        s.dynamic.soft_rock_at_p z = true := by
    intro z hz
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser] at hz
    · simpa [fire_laser, hzy] using hz

  have hard_old_of_new :
      ∀ z,
        (fire_laser var_x var_y s).dynamic.hard_rock_at_p z = true →
        s.dynamic.hard_rock_at_p z = true := by
    intro z hz
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser] at hz
    · simpa [fire_laser, hzy] using hz

  have gold_old_of_new :
      ∀ z,
        (fire_laser var_x var_y s).dynamic.gold_at_p z = true →
        s.dynamic.gold_at_p z = true := by
    intro z hz
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser] at hz
    · simpa [fire_laser, hzy] using hz

  refine
    ⟨hstatic, hVR, hVL, ?_, ?_, ?_, ?_,
     hR1, hL1, ?_, ?_, ?_, ?_, hHeld,
     hArm, hLX, hRExists, ?_, ?_⟩
  · intro z hz
    exact hVS z (soft_old_of_new z hz)
  · intro z hz
    exact hVH z (hard_old_of_new z hz)
  · intro z hz
    exact hVG z (gold_old_of_new z hz)
  · intro z hz
    by_cases hzy : z = var_y
    · subst z
      exact hlocY
    · apply hVC z
      simpa [fire_laser, hzy] using hz
  · intro a b ha hb
    exact hG1 a b (gold_old_of_new a ha) (gold_old_of_new b hb)
  · intro z hclear
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser, truthy_bool_iff_eq_true]
    · have holdClear : s.dynamic.clear_p z = true := by
        simpa [fire_laser, hzy, truthy_bool_iff_eq_true] using hclear
      simpa [fire_laser, hzy, truthy_bool_iff_eq_true] using
        hClear z holdClear
  · intro z hrocks
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser, truthy_bool_iff_eq_true] at hrocks
    · apply hSH z
      simpa [fire_laser, hzy, truthy_bool_iff_eq_true] using hrocks
  · intro z hrobot
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser, truthy_bool_iff_eq_true]
    · have holdRobot : s.dynamic.robot_at_p z = true := by
        simpa [fire_laser, truthy_bool_iff_eq_true] using hrobot
      have holdClear := hRC z holdRobot
      simpa [fire_laser, hzy, truthy_bool_iff_eq_true] using holdClear
  · intro z hloc
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser]
    · simpa [fire_laser, hzy] using hTerrain z hloc
  · intro z hloc
    by_cases hzy : z = var_y
    · subst z
      simp [fire_laser]
    · simpa [fire_laser, hzy] using hPartition z hloc

lemma pick_gold_preserves_wf
    (var_x)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pick_goldPre var_x s) :
    WellFormed (pick_gold var_x s) := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hpre with ⟨hlocX, hrobotX, harmEmpty, hgoldX⟩

  have hnoneHeld :
      ¬ (s.dynamic.holds_bomb_p = true ∨
         s.dynamic.holds_laser_p = true ∨
         s.dynamic.holds_gold_p = true) :=
    hArm.mp harmEmpty
  have hnoBomb : ¬ s.dynamic.holds_bomb_p = true := by
    intro h
    exact hnoneHeld (Or.inl h)
  have hnoLaser : ¬ s.dynamic.holds_laser_p = true := by
    intro h
    exact hnoneHeld (Or.inr (Or.inl h))

  refine
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, ?_,
     ?_, hLX, hRExists, hTerrain, hPartition⟩
  · simp [HeldAtMostOne, pick_gold, truthy_bool_iff_eq_true,
      hnoBomb, hnoLaser]
  · simp [ArmEmptyIffNoneHeld, pick_gold]

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | move var_x var_y =>
      exact move_preserves_wf var_x var_y s hwf hpre
  | pickup_laser var_x =>
      exact pickup_laser_preserves_wf var_x s hwf hpre
  | pickup_bomb var_x =>
      exact pickup_bomb_preserves_wf var_x s hwf hpre
  | putdown_laser var_x =>
      exact putdown_laser_preserves_wf var_x s hwf hpre
  | detonate_bomb var_x var_y =>
      exact detonate_bomb_preserves_wf var_x var_y s hwf hpre
  | fire_laser var_x var_y =>
      exact fire_laser_preserves_wf var_x var_y s hwf hpre
  | pick_gold var_x =>
      exact pick_gold_preserves_wf var_x s hwf hpre

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

-- Part 4) Generated Proof (up to first failure if any)

/-!
## Auxiliary notions used by the correctness proof
-/

/--
A clear transition is a connected transition whose destination is clear.

This is the same transition relation used by `InitClearPathToBombLaser`.
-/
def GPClearStep (s : State) (x y : Obj) : Prop :=
  s.statics.connected_p x y = true ∧
  s.dynamic.clear_p y = true

/--
There is a clear path from `x` to `y`.

The reflexive case is useful when the robot is already at the destination.
-/
def GPClearReachable (s : State) (x y : Obj) : Prop :=
  Relation.ReflTransGen (GPClearStep s) x y

/--
Structural characterization of the tail of a clear path.

`GPPathFrom s current rest goal` says that starting at `current`, the
locations in `rest` form connected clear steps ending at `goal`.
Every location occurring in the path is required to be a typed location
and clear.
-/
def GPPathFrom (s : State) : Obj → List Obj → Obj → Prop
  | current, [], goal =>
      current = goal ∧
      s.statics.loc_t current = true ∧
      s.dynamic.clear_p current = true
  | current, next :: rest, goal =>
      s.statics.loc_t current = true ∧
      s.dynamic.clear_p current = true ∧
      s.statics.connected_p current next = true ∧
      s.dynamic.clear_p next = true ∧
      GPPathFrom s next rest goal

/--
`path` is a nonempty clear path beginning at `start` and ending at `goal`.
-/
def GPClearPath
    (s : State)
    (start goal : Obj)
    (path : List Obj) : Prop :=
  ∃ rest,
    path = start :: rest ∧
    GPPathFrom s start rest goal

/--
Two states agree on everything except, potentially, the robot position.

This is the frame condition needed for plans consisting entirely of moves.
-/
def GPSameExceptRobot (s t : State) : Prop :=
  t.statics = s.statics ∧
  t.dynamic.laser_at_p = s.dynamic.laser_at_p ∧
  t.dynamic.soft_rock_at_p = s.dynamic.soft_rock_at_p ∧
  t.dynamic.hard_rock_at_p = s.dynamic.hard_rock_at_p ∧
  t.dynamic.gold_at_p = s.dynamic.gold_at_p ∧
  t.dynamic.arm_empty_p = s.dynamic.arm_empty_p ∧
  t.dynamic.holds_bomb_p = s.dynamic.holds_bomb_p ∧
  t.dynamic.holds_laser_p = s.dynamic.holds_laser_p ∧
  t.dynamic.holds_gold_p = s.dynamic.holds_gold_p ∧
  t.dynamic.clear_p = s.dynamic.clear_p

/--
The number of non-gold obstacles still present in the state.

Every successful recursive laser iteration clears one such object. This is
the progress measure used for `gpLaserLoop`.
-/
def gpObstacleCount (s : State) (gold : Obj) : Nat :=
  (s.statics.objects.filter (fun x =>
    (x != gold) &&
    (s.dynamic.soft_rock_at_p x ||
     s.dynamic.hard_rock_at_p x))).length

/--
Invariant maintained by `gpLaserLoop`.

It records that:

* the state remains well formed;
* `bomb` is the static bomb location;
* the gold is still at `gold`;
* the laser is held;
* the robot can return to the bomb through the clear region; and
* the gold is not hidden under hard rock.

The gold is excluded from laser targets, so `gold_at_p gold` remains true
throughout the loop.
-/
def GPLaserLoopInv (bomb gold : Obj) (s : State) : Prop :=
  WellFormed s ∧
  s.statics.bomb_at_p bomb = true ∧
  s.dynamic.gold_at_p gold = true ∧
  s.dynamic.holds_laser_p = true ∧
  (∃ robot,
    s.dynamic.robot_at_p robot = true ∧
    GPClearReachable s robot bomb) ∧
  s.dynamic.hard_rock_at_p gold = false

/-!
## Object lookup
-/

/--
Soundness of `gpFindObj?`: a returned object belongs to the searched list
and satisfies the Boolean predicate.
-/
lemma gpFindObj?_sound
    {xs : List Obj}
    {p : Obj → Bool}
    {x : Obj}
    (hfind : gpFindObj? xs p = some x) :
    x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [gpFindObj?] at hfind
  | cons a xs ih =>
      cases hpa : p a with
      | false =>
          have htail : gpFindObj? xs p = some x := by
            simpa [gpFindObj?, hpa] using hfind
          rcases ih htail with ⟨hmem, hp⟩
          exact ⟨List.mem_cons_of_mem a hmem, hp⟩
      | true =>
          have hax : a = x := by
            simpa [gpFindObj?, hpa] using hfind
          subst x
          exact ⟨by simp, hpa⟩

/--
Completeness of `gpFindObj?`: if some list member satisfies the predicate,
then the search returns some satisfying member.
-/
lemma gpFindObj?_complete
    {xs : List Obj}
    {p : Obj → Bool}
    {x : Obj}
    (hmem : x ∈ xs)
    (hp : p x = true) :
    ∃ y, gpFindObj? xs p = some y ∧ y ∈ xs ∧ p y = true := by
  induction xs generalizing x with
  | nil =>
      simp at hmem
  | cons a xs ih =>
      cases hpa : p a with
      | true =>
          refine ⟨a, ?_, ?_, ?_⟩
          · simp [gpFindObj?, hpa]
          · simp
          · exact hpa
      | false =>
          have hmemtail : x ∈ xs := by
            rcases List.mem_cons.mp hmem with hxa | hxmem
            · subst x
              simp [hpa] at hp
            · exact hxmem
          rcases ih hmemtail hp with ⟨y, hyfind, hymem, hyp⟩
          refine ⟨y, ?_, ?_, ?_⟩
          · simpa [gpFindObj?, hpa] using hyfind
          · exact List.mem_cons_of_mem a hymem
          · exact hyp

/--
A well-formed state contains a robot that can be found by `gpFindRobot?`.
-/
lemma gpFindRobot?_exists
    (s : State)
    (hwf : WellFormed s) :
    ∃ robot,
      gpFindRobot? s = some robot ∧
      s.dynamic.robot_at_p robot = true ∧
      s.statics.loc_t robot = true := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hRExists with ⟨x, hxRobot⟩
  have hxLoc : s.statics.loc_t x = true :=
    hVR x hxRobot
  have hxMem : x ∈ s.statics.objects :=
    hstatic.2.2.2.1 x hxLoc
  rcases gpFindObj?_complete hxMem hxRobot with
    ⟨robot, hfind, hrobotMem, hrobotAt⟩
  have hrobotLoc : s.statics.loc_t robot = true :=
    hVR robot hrobotAt
  exact ⟨robot, by simpa [gpFindRobot?] using hfind, hrobotAt, hrobotLoc⟩

/--
If initial gold exists, `gpFindGold?` returns its unique location.
-/
lemma gpFindGold?_exists
    (s : State)
    (hwf : WellFormed s)
    (hgoldExists : InitGoldExists s) :
    ∃ gold,
      gpFindGold? s = some gold ∧
      s.dynamic.gold_at_p gold = true ∧
      s.statics.loc_t gold = true := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  rcases hgoldExists with ⟨x, hxGold⟩
  have hxLoc : s.statics.loc_t x = true :=
    hVG x hxGold
  have hxMem : x ∈ s.statics.objects :=
    hstatic.2.2.2.1 x hxLoc
  rcases gpFindObj?_complete hxMem hxGold with
    ⟨gold, hfind, hgoldMem, hgoldAt⟩
  have hgoldLoc : s.statics.loc_t gold = true :=
    hVG gold hgoldAt
  exact
    ⟨gold, by simpa [gpFindGold?] using hfind, hgoldAt, hgoldLoc⟩

/--
A well-formed static state contains a bomb location that is returned by
`gpFindBomb?`.
-/
lemma gpFindBomb?_exists
    (s : State)
    (hstatic : WellFormedStatic s.statics) :
    ∃ bomb,
      gpFindBomb? s = some bomb ∧
      s.statics.bomb_at_p bomb = true ∧
      s.statics.loc_t bomb = true := by
  rcases hstatic with
    ⟨hUnique, hValidBomb, hValidConnected, hTypeHierarchy,
     hTypeCoverage, hSymmetric, hGraphConnected, hMinLoc,
     hBombUnique, hBombExists⟩
  rcases hBombExists with ⟨x, hxBomb⟩
  have hxLoc : s.statics.loc_t x = true :=
    hValidBomb x hxBomb
  have hxMem : x ∈ s.statics.objects :=
    hTypeHierarchy x hxLoc
  rcases gpFindObj?_complete hxMem hxBomb with
    ⟨bomb, hfind, hbombMem, hbombAt⟩
  have hbombLoc : s.statics.loc_t bomb = true :=
    hValidBomb bomb hbombAt
  exact
    ⟨bomb, by simpa [gpFindBomb?] using hfind, hbombAt, hbombLoc⟩

/--
The robot returned by `gpFindRobot?` is the unique true robot location.
-/
lemma gpFindRobot?_unique
    (s : State)
    (hwf : WellFormed s)
    {robot actual : Obj}
    (hfind : gpFindRobot? s = some robot)
    (hactual : s.dynamic.robot_at_p actual = true) :
    robot = actual := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  have hfind' :
      gpFindObj? s.statics.objects s.dynamic.robot_at_p = some robot := by
    simpa [gpFindRobot?] using hfind
  have hrobotAt : s.dynamic.robot_at_p robot = true :=
    (gpFindObj?_sound hfind').2
  exact hR1 robot actual hrobotAt hactual

/--
The gold returned by `gpFindGold?` is the unique true gold location.
-/
lemma gpFindGold?_unique
    (s : State)
    (hwf : WellFormed s)
    {gold actual : Obj}
    (hfind : gpFindGold? s = some gold)
    (hactual : s.dynamic.gold_at_p actual = true) :
    gold = actual := by
  rcases hwf with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩
  have hfind' :
      gpFindObj? s.statics.objects s.dynamic.gold_at_p = some gold := by
    simpa [gpFindGold?] using hfind
  have hgoldAt : s.dynamic.gold_at_p gold = true :=
    (gpFindObj?_sound hfind').2
  exact hG1 gold actual hgoldAt hactual

/-!
## Abstract clear paths
-/

/--
A clear path in a well-formed state can be traversed in reverse.

The additional assumption that the start is clear is necessary because
`GPClearStep` only explicitly requires the destination to be clear.
-/
lemma gpClearReachable_symm
    (s : State)
    (hwf : WellFormed s)
    {x y : Obj}
    (hclearX : s.dynamic.clear_p x = true)
    (hreach : GPClearReachable s x y) :
    GPClearReachable s y x := by
  have hstatic : WellFormedStatic s.statics := hwf.1
  have hsymm : ConnectedSymmetric s.statics :=
    hstatic.2.2.2.2.2.1

  have aux :
      ∀ {z : Obj},
        Relation.ReflTransGen (GPClearStep s) x z →
          s.dynamic.clear_p z = true ∧
          Relation.ReflTransGen (GPClearStep s) z x := by
    intro z hz
    induction hz with
    | refl =>
        exact ⟨hclearX, Relation.ReflTransGen.refl⟩
    | tail hprefix hstep ih =>
        rcases ih with ⟨hclearPrevious, hreversePrefix⟩
        rcases hstep with ⟨hconnected, hclearCurrent⟩
        have hreverseStep : GPClearStep s _ _ :=
          ⟨hsymm _ _ hconnected, hclearPrevious⟩
        exact
          ⟨hclearCurrent,
           Relation.ReflTransGen.head hreverseStep hreversePrefix⟩

  exact (aux hreach).2

/--
Clear reachability is transitive.
-/
lemma gpClearReachable_trans
    (s : State)
    {x y z : Obj}
    (hxy : GPClearReachable s x y)
    (hyz : GPClearReachable s y z) :
    GPClearReachable s x z := by
  unfold GPClearReachable at *
  exact Relation.ReflTransGen.trans hxy hyz

/--
A structural clear path induces relational clear reachability.
-/
lemma gpClearPath_reachable
    {s : State}
    {start goal : Obj}
    {path : List Obj}
    (hpath : GPClearPath s start goal path) :
    GPClearReachable s start goal := by
  rcases hpath with ⟨rest, rfl, hfrom⟩
  induction rest generalizing start with
  | nil =>
      change
        start = goal ∧
        s.statics.loc_t start = true ∧
        s.dynamic.clear_p start = true
        at hfrom
      rw [hfrom.1]
      exact Relation.ReflTransGen.refl
  | cons next rest ih =>
      change
        s.statics.loc_t start = true ∧
        s.dynamic.clear_p start = true ∧
        s.statics.connected_p start next = true ∧
        s.dynamic.clear_p next = true ∧
        GPPathFrom s next rest goal
        at hfrom
      rcases hfrom with
        ⟨_hstartLoc, _hstartClear, hconnected, hnextClear, hrest⟩
      exact Relation.ReflTransGen.head
        ⟨hconnected, hnextClear⟩
        (ih hrest)

/--
Relational clear reachability can be represented by a concrete path list.
-/
lemma gpClearReachable_has_path
    (s : State)
    (hwf : WellFormed s)
    {start goal : Obj}
    (hstartLoc : s.statics.loc_t start = true)
    (hstartClear : s.dynamic.clear_p start = true)
    (hreach : GPClearReachable s start goal) :
    ∃ path, GPClearPath s start goal path := by
  have hvalidConnected : ValidConnectedParam s.statics :=
    hwf.1.2.2.1

  have extend :
      ∀ {current endpoint next : Obj} {rest : List Obj},
        GPPathFrom s current rest endpoint →
        s.statics.connected_p endpoint next = true →
        s.dynamic.clear_p next = true →
        s.statics.loc_t next = true →
        GPPathFrom s current (rest ++ [next]) next := by
    intro current endpoint next rest hfrom hconnected hnextClear hnextLoc
    induction rest generalizing current with
    | nil =>
        change
          current = endpoint ∧
          s.statics.loc_t current = true ∧
          s.dynamic.clear_p current = true
          at hfrom
        rcases hfrom with
          ⟨hcurrentEndpoint, hcurrentLoc, hcurrentClear⟩
        subst endpoint
        change
          s.statics.loc_t current = true ∧
          s.dynamic.clear_p current = true ∧
          s.statics.connected_p current next = true ∧
          s.dynamic.clear_p next = true ∧
          GPPathFrom s next [] next
        refine
          ⟨hcurrentLoc, hcurrentClear, hconnected, hnextClear, ?_⟩
        exact ⟨rfl, hnextLoc, hnextClear⟩
    | cons first rest ih =>
        change
          s.statics.loc_t current = true ∧
          s.dynamic.clear_p current = true ∧
          s.statics.connected_p current first = true ∧
          s.dynamic.clear_p first = true ∧
          GPPathFrom s first rest endpoint
          at hfrom
        rcases hfrom with
          ⟨hcurrentLoc, hcurrentClear, hcurrentFirst,
           hfirstClear, hrest⟩
        change
          s.statics.loc_t current = true ∧
          s.dynamic.clear_p current = true ∧
          s.statics.connected_p current first = true ∧
          s.dynamic.clear_p first = true ∧
          GPPathFrom s first (rest ++ [next]) next
        refine
          ⟨hcurrentLoc, hcurrentClear, hcurrentFirst,
           hfirstClear, ?_⟩
        exact ih hrest

  have extendExists :
      ∀ {current endpoint next : Obj},
        (∃ rest, GPPathFrom s current rest endpoint) →
        s.statics.connected_p endpoint next = true →
        s.dynamic.clear_p next = true →
        s.statics.loc_t next = true →
        ∃ rest, GPPathFrom s current rest next := by
    intro current endpoint next hpath hconnected hnextClear hnextLoc
    rcases hpath with ⟨rest, hrest⟩
    exact
      ⟨rest ++ [next],
       extend hrest hconnected hnextClear hnextLoc⟩

  have build :
      ∀ {z : Obj},
        Relation.ReflTransGen (GPClearStep s) start z →
        ∃ rest, GPPathFrom s start rest z := by
    intro z hz
    induction hz with
    | refl =>
        refine ⟨[], ?_⟩
        exact ⟨rfl, hstartLoc, hstartClear⟩
    | tail hprefix hstep ih =>
        rcases hstep with ⟨hconnected, hnextClear⟩
        have hnextLoc : s.statics.loc_t _ = true :=
          (hvalidConnected _ _ hconnected).2
        exact extendExists ih hconnected hnextClear hnextLoc

  rcases build hreach with ⟨rest, hrest⟩
  refine ⟨start :: rest, ?_⟩
  exact ⟨rest, rfl, hrest⟩

/--
`GPSameExceptRobot` preserves clear reachability.
-/
lemma gpSameExceptRobot_preserves_clear_reachable
    {s t : State}
    (hsame : GPSameExceptRobot s t)
    {x y : Obj}
    (hreach : GPClearReachable s x y) :
    GPClearReachable t x y := by
  rcases hsame with
    ⟨hstatics, _hlaser, _hsoft, _hhard, _hgold, _harm,
     _hholdsBomb, _hholdsLaser, _hholdsGold, hclear⟩
  unfold GPClearReachable at hreach ⊢
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      apply Relation.ReflTransGen.tail ih
      simpa [GPClearStep, hstatics, hclear] using hstep

/-!
## Correctness of the BFS implementation
-/

/--
Extend a structural clear path by one connected clear destination.
-/
lemma gpPathFrom_extend
    {s : State}
    {current endpoint next : Obj}
    {rest : List Obj}
    (hfrom : GPPathFrom s current rest endpoint)
    (hconnected : s.statics.connected_p endpoint next = true)
    (hnextClear : s.dynamic.clear_p next = true)
    (hnextLoc : s.statics.loc_t next = true) :
    GPPathFrom s current (rest ++ [next]) next := by
  induction rest generalizing current with
  | nil =>
      change
        current = endpoint ∧
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true
        at hfrom
      rcases hfrom with
        ⟨hcurrentEndpoint, hcurrentLoc, hcurrentClear⟩
      subst endpoint
      change
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true ∧
        s.statics.connected_p current next = true ∧
        s.dynamic.clear_p next = true ∧
        GPPathFrom s next [] next
      refine
        ⟨hcurrentLoc, hcurrentClear, hconnected, hnextClear, ?_⟩
      exact ⟨rfl, hnextLoc, hnextClear⟩
  | cons first rest ih =>
      change
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true ∧
        s.statics.connected_p current first = true ∧
        s.dynamic.clear_p first = true ∧
        GPPathFrom s first rest endpoint
        at hfrom
      rcases hfrom with
        ⟨hcurrentLoc, hcurrentClear, hcurrentFirst,
         hfirstClear, hrest⟩
      change
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true ∧
        s.statics.connected_p current first = true ∧
        s.dynamic.clear_p first = true ∧
        GPPathFrom s first (rest ++ [next]) next
      exact
        ⟨hcurrentLoc, hcurrentClear, hcurrentFirst,
         hfirstClear, ih hrest⟩

/--
Extend a concrete clear path by one connected clear destination.
-/
lemma gpClearPath_extend
    {s : State}
    {start endpoint next : Obj}
    {path : List Obj}
    (hpath : GPClearPath s start endpoint path)
    (hconnected : s.statics.connected_p endpoint next = true)
    (hnextClear : s.dynamic.clear_p next = true)
    (hnextLoc : s.statics.loc_t next = true) :
    GPClearPath s start next (path ++ [next]) := by
  rcases hpath with ⟨rest, hpathEq, hfrom⟩
  subst path
  refine ⟨rest ++ [next], rfl, ?_⟩
  exact gpPathFrom_extend hfrom hconnected hnextClear hnextLoc

/--
Every location returned by `gpFreshClearNeighbors` belongs to the object
list and is a connected clear neighbor of `current`.
-/
lemma gpFreshClearNeighbors_sound
    (s : State)
    (current : Obj)
    (visited : List Obj)
    {next : Obj}
    (hmem : next ∈ gpFreshClearNeighbors s current visited) :
    next ∈ s.statics.objects ∧
    s.statics.connected_p current next = true ∧
    s.dynamic.clear_p next = true := by
  unfold gpFreshClearNeighbors at hmem
  rcases List.mem_filter.mp hmem with ⟨hobj, hp⟩
  cases hconnected : s.statics.connected_p current next with
  | false =>
      simp [hconnected] at hp
  | true =>
      cases hclear : s.dynamic.clear_p next with
      | false =>
          simp [hconnected, hclear] at hp
      | true =>
          exact ⟨hobj, rfl, rfl⟩

/--
Soundness of the internal BFS under the invariant that every queued
reversed path represents a clear path from `start` to its queued endpoint.
-/
lemma gpClearPathBfs_sound
    (s : State)
    (hwf : WellFormed s)
    {start goal : Obj}
    {fuel : Nat}
    {queue : List (Obj × List Obj)}
    {visited : List Obj}
    {path : List Obj}
    (hqueue :
      ∀ current reversePath,
        (current, reversePath) ∈ queue →
        GPClearPath s start current reversePath.reverse)
    (hfind :
      gpClearPathBfs s goal fuel queue visited = some path) :
    GPClearPath s start goal path := by
  induction fuel generalizing queue visited path with
  | zero =>
      simp [gpClearPathBfs] at hfind
  | succ fuel ih =>
      cases queue with
      | nil =>
          simp [gpClearPathBfs] at hfind
      | cons entry rest =>
          rcases entry with ⟨current, reversePath⟩
          by_cases hgoal : current = goal
          · subst goal
            have hpathEq : reversePath.reverse = path := by
              simpa [gpClearPathBfs] using hfind
            rw [← hpathEq]
            exact hqueue current reversePath (by simp)
          · have hrec :
                gpClearPathBfs
                    s
                    goal
                    fuel
                    (rest ++
                      (gpFreshClearNeighbors s current visited).map
                        (fun next => (next, next :: reversePath)))
                    (visited ++ gpFreshClearNeighbors s current visited) =
                  some path := by
                simpa [gpClearPathBfs, hgoal] using hfind

            have hqueue' :
                ∀ candidate candidateReversePath,
                  (candidate, candidateReversePath) ∈
                      (rest ++
                        (gpFreshClearNeighbors s current visited).map
                          (fun next => (next, next :: reversePath))) →
                  GPClearPath
                    s
                    start
                    candidate
                    candidateReversePath.reverse := by
              intro candidate candidateReversePath hmem
              rcases List.mem_append.mp hmem with hrest | hnew
              · apply hqueue candidate candidateReversePath
                exact List.mem_cons_of_mem (current, reversePath) hrest
              · rcases List.mem_map.mp hnew with ⟨next, hnext, heq⟩
                have hcandidate : candidate = next := by
                  exact
                    (congrArg
                      (fun p : Obj × List Obj => p.1)
                      heq).symm
                have hcandidateReversePath :
                    candidateReversePath = next :: reversePath := by
                  exact
                    (congrArg
                      (fun p : Obj × List Obj => p.2)
                      heq).symm
                subst candidate
                subst candidateReversePath

                have hcurrentPath :
                    GPClearPath
                      s
                      start
                      current
                      reversePath.reverse :=
                  hqueue current reversePath (by simp)
                rcases
                    gpFreshClearNeighbors_sound
                      s current visited hnext with
                  ⟨_hnextMem, hconnected, hnextClear⟩
                have hnextLoc :
                    s.statics.loc_t next = true :=
                  (hwf.1.2.2.1 current next hconnected).2
                have hextended :
                    GPClearPath
                      s
                      start
                      next
                      (reversePath.reverse ++ [next]) :=
                  gpClearPath_extend
                    hcurrentPath
                    hconnected
                    hnextClear
                    hnextLoc
                simpa using hextended

            exact ih
              (queue :=
                rest ++
                  (gpFreshClearNeighbors s current visited).map
                    (fun next => (next, next :: reversePath)))
              (visited :=
                visited ++ gpFreshClearNeighbors s current visited)
              (path := path)
              hqueue'
              hrec

/--
Soundness of `gpFindClearPath`: every returned list is a connected clear
path from the requested start to the requested goal.
-/
lemma gpFindClearPath_sound
    (s : State)
    (hwf : WellFormed s)
    {start goal : Obj}
    (hstartLoc : s.statics.loc_t start = true)
    (hstartClear : s.dynamic.clear_p start = true)
    {path : List Obj}
    (hfind : gpFindClearPath s start goal = some path) :
    GPClearPath s start goal path := by
  have hinitialPath :
      GPClearPath s start start [start] := by
    refine ⟨[], rfl, ?_⟩
    exact ⟨rfl, hstartLoc, hstartClear⟩

  have hqueue :
      ∀ current reversePath,
        (current, reversePath) ∈ [(start, [start])] →
        GPClearPath s start current reversePath.reverse := by
    intro current reversePath hmem
    simp only [List.mem_singleton] at hmem
    have hcurrent : current = start :=
      congrArg Prod.fst hmem
    have hreversePath : reversePath = [start] :=
      congrArg Prod.snd hmem
    subst current
    subst reversePath
    simpa using hinitialPath

  apply gpClearPathBfs_sound
    (s := s)
    (hwf := hwf)
    (start := start)
    (goal := goal)
    (fuel := s.statics.objects.length + 1)
    (queue := [(start, [start])])
    (visited := [start])
    (path := path)
  · exact hqueue
  · simpa [gpFindClearPath] using hfind

/--
An object distinct from the erased object remains in the list after
`List.erase`.
-/
lemma gp_mem_erase_of_mem_ne
    (xs : List Obj)
    {x y : Obj}
    (hmem : y ∈ xs)
    (hne : y ≠ x) :
    y ∈ xs.erase x := by
  induction xs with
  | nil =>
      simp at hmem
  | cons a xs ih =>
      simp only [List.erase]
      split
      · rename_i hax
        have hax' : a = x := by
          simpa using hax
        subst a
        rcases List.mem_cons.mp hmem with hyx | htail
        · exact (hne hyx).elim
        · exact htail
      · rcases List.mem_cons.mp hmem with hya | htail
        · exact List.mem_cons.mpr (Or.inl hya)
        · exact List.mem_cons.mpr (Or.inr (ih htail))

/--
Erasing an object that occurs in a list strictly decreases its length.
-/
lemma gp_length_erase_lt_of_mem
    (x : Obj)
    {xs : List Obj}
    (hmem : x ∈ xs) :
    (xs.erase x).length < xs.length := by
  induction xs with
  | nil =>
      simp at hmem
  | cons a xs ih =>
      by_cases hax : a = x
      · subst a
        simp [List.erase]
      · have hxa : x ≠ a := Ne.symm hax
        have htail : x ∈ xs :=
          (List.mem_cons.mp hmem).resolve_left hxa
        have hbeq : (a == x) = false := by
          simp [hax]
        simp only [List.erase, hbeq]
        exact Nat.succ_lt_succ (ih htail)

/--
A member returned by `gpFreshClearNeighbors` was not previously visited.
-/
lemma gpFreshClearNeighbors_fresh
    (s : State)
    (current : Obj)
    (visited : List Obj)
    {next : Obj}
    (hmem : next ∈ gpFreshClearNeighbors s current visited) :
    next ∉ visited := by
  unfold gpFreshClearNeighbors at hmem
  rcases List.mem_filter.mp hmem with ⟨_hobj, hp⟩
  intro hvisited
  have hcontains : visited.contains next = true := by
    simpa using hvisited
  simp [hcontains] at hp
  exact hp.2 hvisited

/--
Every connected, clear, unvisited object occurs among the fresh clear
neighbors.
-/
lemma gpFreshClearNeighbors_complete
    (s : State)
    (current : Obj)
    (visited : List Obj)
    {next : Obj}
    (hobj : next ∈ s.statics.objects)
    (hconnected : s.statics.connected_p current next = true)
    (hclear : s.dynamic.clear_p next = true)
    (hfresh : next ∉ visited) :
    next ∈ gpFreshClearNeighbors s current visited := by
  unfold gpFreshClearNeighbors
  apply List.mem_filter.mpr
  refine ⟨hobj, ?_⟩
  simpa [hconnected, hclear] using hfresh

/--
Completeness of `gpFindClearPath`: every relationally reachable clear goal
is found by the finite BFS.
-/
lemma gpFindClearPath_complete
    (s : State)
    (hwf : WellFormed s)
    {start goal : Obj}
    (hstartLoc : s.statics.loc_t start = true)
    (hstartClear : s.dynamic.clear_p start = true)
    (hreach : GPClearReachable s start goal) :
    ∃ path, gpFindClearPath s start goal = some path := by
  have hobjectsNodup : s.statics.objects.Nodup :=
    hwf.1.1
  have hvalidConnected : ValidConnectedParam s.statics :=
    hwf.1.2.2.1
  have htypeHierarchy : ValidTypeHierarchy s.statics :=
    hwf.1.2.2.2.1
  have hstartObj : start ∈ s.statics.objects :=
    htypeHierarchy start hstartLoc

  have reachable_mem_of_closed :
      ∀ {z : Obj} {visited : List Obj},
        start ∈ visited →
        (∀ x,
          x ∈ visited →
          ∀ y, GPClearStep s x y → y ∈ visited) →
        GPClearReachable s start z →
        z ∈ visited := by
    intro z visited hstartVisited hclosed hreach'
    unfold GPClearReachable at hreach'
    induction hreach' with
    | refl =>
        exact hstartVisited
    | @tail x y hprefix hstep ihReach =>
        exact hclosed x ihReach y hstep

  have bfsComplete :
      ∀ (fuel : Nat)
        (queue : List (Obj × List Obj))
        (visited remaining : List Obj),
        remaining.Nodup →
        remaining.length < fuel →
        (∀ entry, entry ∈ queue → entry.1 ∈ remaining) →
        (∀ x, x ∈ s.statics.objects → x ∉ visited → x ∈ remaining) →
        (∀ x, x ∈ visited → x ∈ s.statics.objects) →
        start ∈ visited →
        (∀ entry, entry ∈ queue → entry.1 ∈ visited) →
        (queue.map Prod.fst).Nodup →
        (goal ∈ visited → goal ∈ queue.map Prod.fst) →
        (∀ x,
          x ∈ visited →
          x ∉ queue.map Prod.fst →
          ∀ y, GPClearStep s x y → y ∈ visited) →
        ∃ path, gpClearPathBfs s goal fuel queue visited = some path := by
    intro fuel
    induction fuel with
    | zero =>
        intro queue visited remaining
          _hremainingNodup hlength
          _hqueueRemaining _hunvisitedRemaining
          _hvisitedObjects _hstartVisited _hqueueVisited
          _hqueueNodup _hgoalQueued _hclosed
        omega

    | succ fuel ih =>
        intro queue visited remaining
          hremainingNodup hlength
          hqueueRemaining hunvisitedRemaining
          hvisitedObjects hstartVisited hqueueVisited
          hqueueNodup hgoalQueued hclosed

        cases queue with
        | nil =>
            have hgoalVisited : goal ∈ visited := by
              apply reachable_mem_of_closed
                (visited := visited)
                hstartVisited
              · intro x hx y hstep
                exact hclosed x hx (by simp) y hstep
              · exact hreach

            have hgoalInQueue : goal ∈ ([].map Prod.fst) :=
              hgoalQueued hgoalVisited
            simp at hgoalInQueue

        | cons entry rest =>
            rcases entry with ⟨current, reversePath⟩

            by_cases hcurrentGoal : current = goal
            · subst goal
              refine ⟨reversePath.reverse, ?_⟩
              simp [gpClearPathBfs]

            · let neighbors :=
                gpFreshClearNeighbors s current visited
              let newQueue :=
                rest ++
                  neighbors.map
                    (fun next => (next, next :: reversePath))
              let newVisited :=
                visited ++ neighbors
              let newRemaining :=
                remaining.erase current

              have hcurrentRemaining : current ∈ remaining :=
                hqueueRemaining (current, reversePath) (by simp)

              have hcurrentVisited : current ∈ visited :=
                hqueueVisited (current, reversePath) (by simp)

              have holdNodesNodup :
                  (current :: rest.map Prod.fst).Nodup := by
                simpa using hqueueNodup

              have holdNodesNodupParts :
                  current ∉ rest.map Prod.fst ∧
                    (rest.map Prod.fst).Nodup :=
                List.nodup_cons.mp holdNodesNodup

              have hcurrentNotRest :
                  current ∉ rest.map Prod.fst :=
                holdNodesNodupParts.1

              have hrestNodesNodup :
                  (rest.map Prod.fst).Nodup :=
                holdNodesNodupParts.2

              have hneighborsNodup : neighbors.Nodup := by
                dsimp [neighbors, gpFreshClearNeighbors]
                exact hobjectsNodup.filter _

              have hnewRemainingNodup : newRemaining.Nodup := by
                dsimp [newRemaining]
                exact hremainingNodup.erase current

              have hnewLength : newRemaining.length < fuel := by
                have herase :
                    (remaining.erase current).length <
                      remaining.length :=
                  gp_length_erase_lt_of_mem current hcurrentRemaining
                dsimp [newRemaining]
                omega

              have hnewQueueRemaining :
                  ∀ queuedEntry,
                    queuedEntry ∈ newQueue →
                    queuedEntry.1 ∈ newRemaining := by
                intro queuedEntry hqueued
                dsimp [newQueue] at hqueued
                rcases List.mem_append.mp hqueued with hrest | hnew
                · have hnodeRemaining :
                      queuedEntry.1 ∈ remaining :=
                    hqueueRemaining queuedEntry
                      (List.mem_cons_of_mem
                        (current, reversePath) hrest)

                  have hnodeInRest :
                      queuedEntry.1 ∈ rest.map Prod.fst :=
                    List.mem_map.mpr ⟨queuedEntry, hrest, rfl⟩

                  have hnodeNe : queuedEntry.1 ≠ current := by
                    intro heq
                    rw [heq] at hnodeInRest
                    exact hcurrentNotRest hnodeInRest

                  dsimp [newRemaining]
                  exact gp_mem_erase_of_mem_ne
                    remaining hnodeRemaining hnodeNe

                · rcases List.mem_map.mp hnew with
                    ⟨next, hnext, rfl⟩
                  have hnextObj :
                      next ∈ s.statics.objects :=
                    (gpFreshClearNeighbors_sound
                      s current visited hnext).1
                  have hnextFresh :
                      next ∉ visited :=
                    gpFreshClearNeighbors_fresh
                      s current visited hnext
                  have hnextRemaining :
                      next ∈ remaining :=
                    hunvisitedRemaining next hnextObj hnextFresh
                  have hnextNe : next ≠ current := by
                    intro heq
                    subst next
                    exact hnextFresh hcurrentVisited
                  dsimp [newRemaining]
                  exact gp_mem_erase_of_mem_ne
                    remaining hnextRemaining hnextNe

              have hnewUnvisitedRemaining :
                  ∀ x,
                    x ∈ s.statics.objects →
                    x ∉ newVisited →
                    x ∈ newRemaining := by
                intro x hxObj hxNotVisited
                have hxNotOld : x ∉ visited := by
                  intro hx
                  apply hxNotVisited
                  dsimp [newVisited]
                  exact List.mem_append_left neighbors hx
                have hxRemaining :
                    x ∈ remaining :=
                  hunvisitedRemaining x hxObj hxNotOld
                have hxNe : x ≠ current := by
                  intro heq
                  subst x
                  exact hxNotVisited
                    (by
                      dsimp [newVisited]
                      exact List.mem_append_left
                        neighbors hcurrentVisited)
                dsimp [newRemaining]
                exact gp_mem_erase_of_mem_ne
                  remaining hxRemaining hxNe

              have hnewVisitedObjects :
                  ∀ x, x ∈ newVisited → x ∈ s.statics.objects := by
                intro x hx
                dsimp [newVisited] at hx
                rcases List.mem_append.mp hx with hxOld | hxNew
                · exact hvisitedObjects x hxOld
                · exact
                    (gpFreshClearNeighbors_sound
                      s current visited hxNew).1

              have hnewStartVisited : start ∈ newVisited := by
                dsimp [newVisited]
                exact List.mem_append_left neighbors hstartVisited

              have hnewQueueVisited :
                  ∀ queuedEntry,
                    queuedEntry ∈ newQueue →
                    queuedEntry.1 ∈ newVisited := by
                intro queuedEntry hqueued
                dsimp [newQueue] at hqueued
                rcases List.mem_append.mp hqueued with hrest | hnew
                · have holdVisited :
                      queuedEntry.1 ∈ visited :=
                    hqueueVisited queuedEntry
                      (List.mem_cons_of_mem
                        (current, reversePath) hrest)
                  dsimp [newVisited]
                  exact List.mem_append_left neighbors holdVisited
                · rcases List.mem_map.mp hnew with
                    ⟨next, hnext, rfl⟩
                  dsimp [newVisited]
                  exact List.mem_append_right visited hnext

              have hnewNodesNodup :
                  (rest.map Prod.fst ++ neighbors).Nodup := by
                rw [List.nodup_append]
                refine
                  ⟨hrestNodesNodup, hneighborsNodup, ?_⟩
                intro x hxRest y hyNeighbor hxy
                subst y
                have hxVisited : x ∈ visited := by
                  rcases List.mem_map.mp hxRest with
                    ⟨queuedEntry, hentry, rfl⟩
                  exact hqueueVisited queuedEntry
                    (List.mem_cons_of_mem
                      (current, reversePath) hentry)
                exact
                  (gpFreshClearNeighbors_fresh
                    s current visited hyNeighbor) hxVisited

              have hnewQueueNodup :
                  (newQueue.map Prod.fst).Nodup := by
                dsimp [newQueue]
                simpa [List.map_append, List.map_map,
                  Function.comp_def] using hnewNodesNodup

              have hnewGoalQueued :
                  goal ∈ newVisited →
                  goal ∈ newQueue.map Prod.fst := by
                intro hgoalNewVisited
                dsimp [newVisited] at hgoalNewVisited
                rcases List.mem_append.mp hgoalNewVisited with
                    hgoalOld | hgoalNeighbor
                · have hgoalOldQueue :
                      goal ∈
                        (((current, reversePath) :: rest).map
                          Prod.fst) :=
                    hgoalQueued hgoalOld
                  have hcases :
                      goal = current ∨
                      goal ∈ rest.map Prod.fst := by
                    simpa using hgoalOldQueue
                  rcases hcases with hgoalEq | hgoalRest
                  · exact False.elim
                      (hcurrentGoal hgoalEq.symm)
                  · dsimp [newQueue]
                    simp only [List.map_append, List.map_map]
                    exact List.mem_append_left _ hgoalRest
                · dsimp [newQueue]
                  simp only [List.map_append, List.map_map]
                  apply List.mem_append_right
                  simpa [Function.comp_def] using hgoalNeighbor

              have hnewClosed :
                  ∀ x,
                    x ∈ newVisited →
                    x ∉ newQueue.map Prod.fst →
                    ∀ y, GPClearStep s x y → y ∈ newVisited := by
                intro x hxVisitedNew hxNotQueued y hstep
                dsimp [newVisited] at hxVisitedNew
                rcases List.mem_append.mp hxVisitedNew with
                    hxOld | hxNeighbor
                · by_cases hxc : x = current
                  · subst x
                    by_cases hyOld : y ∈ visited
                    · dsimp [newVisited]
                      exact List.mem_append_left neighbors hyOld
                    · have hyLoc :
                          s.statics.loc_t y = true :=
                        (hvalidConnected current y hstep.1).2
                      have hyObj :
                          y ∈ s.statics.objects :=
                        htypeHierarchy y hyLoc
                      have hyNeighbor : y ∈ neighbors := by
                        dsimp [neighbors]
                        exact gpFreshClearNeighbors_complete
                          s current visited
                          hyObj hstep.1 hstep.2 hyOld
                      dsimp [newVisited]
                      exact List.mem_append_right
                        visited hyNeighbor

                  · have hxNotOldQueue :
                        x ∉
                          (((current, reversePath) :: rest).map
                            Prod.fst) := by
                      intro hxOldQueue
                      have hcases :
                          x = current ∨
                          x ∈ rest.map Prod.fst := by
                        simpa using hxOldQueue
                      rcases hcases with hxEq | hxRest
                      · exact hxc hxEq
                      · apply hxNotQueued
                        dsimp [newQueue]
                        simp only [List.map_append, List.map_map]
                        exact List.mem_append_left _ hxRest

                    have hyVisited :
                        y ∈ visited :=
                      hclosed x hxOld hxNotOldQueue y hstep
                    dsimp [newVisited]
                    exact List.mem_append_left neighbors hyVisited

                · exfalso
                  apply hxNotQueued
                  dsimp [newQueue]
                  simp only [List.map_append, List.map_map]
                  apply List.mem_append_right
                  simpa [Function.comp_def] using hxNeighbor

              rcases ih
                  newQueue
                  newVisited
                  newRemaining
                  hnewRemainingNodup
                  hnewLength
                  hnewQueueRemaining
                  hnewUnvisitedRemaining
                  hnewVisitedObjects
                  hnewStartVisited
                  hnewQueueVisited
                  hnewQueueNodup
                  hnewGoalQueued
                  hnewClosed with
                ⟨path, hpath⟩

              refine ⟨path, ?_⟩
              simpa [gpClearPathBfs, hcurrentGoal,
                newQueue, newVisited, neighbors] using hpath

  have hinitialQueueRemaining :
      ∀ entry,
        entry ∈ [(start, [start])] →
        entry.1 ∈ s.statics.objects := by
    intro entry hentry
    simp only [List.mem_singleton] at hentry
    subst entry
    exact hstartObj

  have hinitialUnvisitedRemaining :
      ∀ x,
        x ∈ s.statics.objects →
        x ∉ [start] →
        x ∈ s.statics.objects := by
    intro x hx _hnot
    exact hx

  have hinitialVisitedObjects :
      ∀ x, x ∈ [start] → x ∈ s.statics.objects := by
    intro x hx
    have hxs : x = start := by
      simpa using hx
    rw [hxs]
    exact hstartObj

  have hinitialQueueVisited :
      ∀ entry,
        entry ∈ [(start, [start])] →
        entry.1 ∈ [start] := by
    intro entry hentry
    simp only [List.mem_singleton] at hentry
    subst entry
    simp

  have hinitialGoalQueued :
      goal ∈ [start] →
      goal ∈ ([(start, [start])].map Prod.fst) := by
    intro hgoal
    simpa using hgoal

  have hinitialClosed :
      ∀ x,
        x ∈ [start] →
        x ∉ ([(start, [start])].map Prod.fst) →
        ∀ y, GPClearStep s x y → y ∈ [start] := by
    intro x hx hxNotQueued
    have hxs : x = start := by
      simpa using hx
    subst x
    simp at hxNotQueued

  rcases bfsComplete
      (s.statics.objects.length + 1)
      [(start, [start])]
      [start]
      s.statics.objects
      hobjectsNodup
      (by omega)
      hinitialQueueRemaining
      hinitialUnvisitedRemaining
      hinitialVisitedObjects
      (by simp)
      hinitialQueueVisited
      (by simp)
      hinitialGoalQueued
      hinitialClosed with
    ⟨path, hpath⟩

  exact ⟨path, by simpa [gpFindClearPath] using hpath⟩

/--
Under the usual typing and start-clear assumptions, BFS failure is
equivalent to lack of clear reachability.
-/
lemma gpFindClearPath_eq_none_iff
    (s : State)
    (hwf : WellFormed s)
    {start goal : Obj}
    (hstartLoc : s.statics.loc_t start = true)
    (hstartClear : s.dynamic.clear_p start = true) :
    gpFindClearPath s start goal = none ↔
      ¬ GPClearReachable s start goal := by
  constructor
  · intro hnone hreach
    rcases
        gpFindClearPath_complete
          s hwf hstartLoc hstartClear hreach with
      ⟨path, hsome⟩
    rw [hnone] at hsome
    simp at hsome
  · intro hnreach
    cases hfind : gpFindClearPath s start goal with
    | none =>
        rfl
    | some path =>
        exfalso
        apply hnreach
        apply gpClearPath_reachable
        exact
          gpFindClearPath_sound
            s hwf hstartLoc hstartClear hfind

/-!
## Executing paths as move actions
-/

/--
The initial location of a structural path is a typed location.
-/
lemma gpPathFrom_start_loc
    {s : State}
    {current goal : Obj}
    {rest : List Obj}
    (hpath : GPPathFrom s current rest goal) :
    s.statics.loc_t current = true := by
  cases rest with
  | nil =>
      change
        current = goal ∧
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true
        at hpath
      exact hpath.2.1
  | cons next rest =>
      change
        s.statics.loc_t current = true ∧
        s.dynamic.clear_p current = true ∧
        s.statics.connected_p current next = true ∧
        s.dynamic.clear_p next = true ∧
        GPPathFrom s next rest goal
        at hpath
      exact hpath.1

/--
Moving the robot does not change whether a list describes a structural
clear path, because moves preserve the static state and all clear fluents.
-/
lemma gpPathFrom_move
    (s : State)
    (var_x var_y : Obj)
    {current goal : Obj}
    {rest : List Obj} :
    GPPathFrom (move var_x var_y s) current rest goal ↔
      GPPathFrom s current rest goal := by
  induction rest generalizing current with
  | nil =>
      simp only [
        GPPathFrom,
        move_statics,
        move_clear_p
      ]
  | cons next rest ih =>
      simp only [
        GPPathFrom,
        move_statics,
        move_clear_p,
        ih
      ]

/--
Executing the move actions generated from the tail of a structural clear
path is valid, reaches the path goal, and changes only the robot position.
-/
lemma gpPathMovesFrom_correct
    (s : State)
    {start goal : Obj}
    {rest : List Obj}
    (hpath : GPPathFrom s start rest goal)
    (hrobot : s.dynamic.robot_at_p start = true) :
    ValidPlan (gpPathMovesFrom start rest) s ∧
    (runPlan (gpPathMovesFrom start rest) s).dynamic.robot_at_p goal = true ∧
    GPSameExceptRobot
      s
      (runPlan (gpPathMovesFrom start rest) s) := by
  induction rest generalizing s start with
  | nil =>
      change
        start = goal ∧
        s.statics.loc_t start = true ∧
        s.dynamic.clear_p start = true
        at hpath
      rcases hpath with ⟨hstartGoal, _hstartLoc, _hstartClear⟩
      subst goal
      simp only [gpPathMovesFrom, ValidPlan, runPlan]
      refine ⟨True.intro, hrobot, ?_⟩
      simp [GPSameExceptRobot]

  | cons next rest ih =>
      change
        s.statics.loc_t start = true ∧
        s.dynamic.clear_p start = true ∧
        s.statics.connected_p start next = true ∧
        s.dynamic.clear_p next = true ∧
        GPPathFrom s next rest goal
        at hpath
      rcases hpath with
        ⟨hstartLoc, _hstartClear, hconnected, hnextClear, hrest⟩

      have hnextLoc : s.statics.loc_t next = true :=
        gpPathFrom_start_loc hrest

      have hpre : movePre start next s :=
        ⟨hstartLoc, hnextLoc, hrobot, hconnected, hnextClear⟩

      have htailPath :
          GPPathFrom (move start next s) next rest goal :=
        (gpPathFrom_move s start next).2 hrest

      have htail :=
        ih
          (s := move start next s)
          (start := next)
          htailPath
          (move_robot_at_p_eq1 start next s)

      simp only [
        gpPathMovesFrom,
        ValidPlan,
        actionPre,
        actionApply,
        runPlan
      ]

      refine ⟨⟨hpre, htail.1⟩, htail.2.1, ?_⟩
      simpa only [
        GPSameExceptRobot,
        move_statics,
        move_laser_at_p,
        move_soft_rock_at_p,
        move_hard_rock_at_p,
        move_gold_at_p,
        move_arm_empty_p,
        move_holds_bomb_p,
        move_holds_laser_p,
        move_holds_gold_p,
        move_clear_p
      ] using htail.2.2

/--
Executing `gpPathMoves` for a concrete clear path produces a valid move
plan, leaves all non-robot fluents unchanged, and places the robot at the
path goal.
-/
lemma gpPathMoves_correct
    (s : State)
    {start goal : Obj}
    {path : List Obj}
    (hpath : GPClearPath s start goal path)
    (hrobot : s.dynamic.robot_at_p start = true) :
    ValidPlan (gpPathMoves path) s ∧
    (runPlan (gpPathMoves path) s).dynamic.robot_at_p goal = true ∧
    GPSameExceptRobot s (runPlan (gpPathMoves path) s) := by
  rcases hpath with ⟨rest, hpathEq, hfrom⟩
  subst path
  simpa only [gpPathMoves] using
    (gpPathMovesFrom_correct
      (s := s)
      (start := start)
      (goal := goal)
      (rest := rest)
      hfrom
      hrobot)

/--
Convenient consequence of `gpPathMoves_correct`: moving along a path
preserves well-formedness.
-/
lemma gpPathMoves_preserves_wf
    (s : State)
    {start goal : Obj}
    {path : List Obj}
    (hwf : WellFormed s)
    (hpath : GPClearPath s start goal path)
    (hrobot : s.dynamic.robot_at_p start = true) :
    WellFormed (runPlan (gpPathMoves path) s) := by
  have hvalid := (gpPathMoves_correct s hpath hrobot).1
  exact validPlan_preserves_wf hvalid hwf

/--
If the robot has an empty arm and follows a path to the gold, appending
`pick_gold` is valid and achieves `holds_gold_p`.
-/
lemma gpDirectGoldPlan_correct
    (s : State)
    {robot gold : Obj}
    {path : List Obj}
    (hwf : WellFormed s)
    (hpath : GPClearPath s robot gold path)
    (hrobot : s.dynamic.robot_at_p robot = true)
    (harmEmpty : s.dynamic.arm_empty_p = true)
    (hgold : s.dynamic.gold_at_p gold = true) :
    let plan :=
      gpPathMoves path ++ [PlanAction.pick_gold gold]
    ValidPlan plan s ∧
    (runPlan plan s).dynamic.holds_gold_p = true := by
  dsimp

  have hgoldLoc : s.statics.loc_t gold = true :=
    hwf.2.2.2.2.2.1 gold hgold

  rcases gpPathMoves_correct s hpath hrobot with
    ⟨hvalidMoves, hrobotAtGold, hsame⟩

  rcases hsame with
    ⟨hstatics, _hlaser, _hsoft, _hhard, hgoldSame, harmSame,
     _hholdsBomb, _hholdsLaser, _hholdsGold, _hclear⟩

  have hpickPre :
      pick_goldPre gold (runPlan (gpPathMoves path) s) := by
    refine ⟨?_, hrobotAtGold, ?_, ?_⟩
    · rw [hstatics]
      exact hgoldLoc
    · rw [harmSame]
      exact harmEmpty
    · rw [hgoldSame]
      exact hgold

  constructor
  · apply
      (validPlan_append
        (gpPathMoves path)
        [PlanAction.pick_gold gold]
        s).2
    refine ⟨hvalidMoves, ?_⟩
    change
      pick_goldPre gold (runPlan (gpPathMoves path) s) ∧ True
    exact ⟨hpickPre, True.intro⟩

  · rw [runPlan_append]
    change
      (pick_gold gold (runPlan (gpPathMoves path) s)).dynamic.holds_gold_p =
        true
    exact
      pick_gold_holds_gold_p
        gold
        (runPlan (gpPathMoves path) s)

/-!
## Reachable-neighbor search
-/

/--
Soundness of `gpFindReachableNeighbor`: the returned neighbor is clear,
is connected to the target, belongs to the object list, and the returned
path reaches it.
-/
lemma gpFindReachableNeighbor_sound
    (s : State)
    (hwf : WellFormed s)
    {start target neighbor : Obj}
    {path : List Obj}
    (hrobot : s.dynamic.robot_at_p start = true)
    (hfind :
      gpFindReachableNeighbor s start target =
        some (neighbor, path)) :
    neighbor ∈ s.statics.objects ∧
    s.dynamic.clear_p neighbor = true ∧
    s.statics.connected_p neighbor target = true ∧
    GPClearPath s start neighbor path := by
  have hwfCopy := hwf
  rcases hwfCopy with
    ⟨_hstatic, hVR, _hVL, _hVS, _hVH, _hVG, _hVC,
     _hR1, _hL1, _hG1, _hClear, _hSH, hRC, _hHeld,
     _hArm, _hLX, _hRExists, _hTerrain, _hPartition⟩

  have hstartLoc : s.statics.loc_t start = true :=
    hVR start hrobot
  have hstartClear : s.dynamic.clear_p start = true :=
    hRC start hrobot

  have aux :
      ∀ xs : List Obj,
        (∀ x, x ∈ xs → x ∈ s.statics.objects) →
        gpFindReachableNeighborAux s start target xs =
            some (neighbor, path) →
        neighbor ∈ s.statics.objects ∧
        s.dynamic.clear_p neighbor = true ∧
        s.statics.connected_p neighbor target = true ∧
        GPClearPath s start neighbor path := by
    intro xs
    induction xs with
    | nil =>
        intro _hsubset haux
        simp [gpFindReachableNeighborAux] at haux

    | cons candidate rest ih =>
        intro hsubset haux

        have hcandidateObj :
            candidate ∈ s.statics.objects :=
          hsubset candidate (by simp)

        have hrestSubset :
            ∀ x, x ∈ rest → x ∈ s.statics.objects := by
          intro x hx
          exact hsubset x (List.mem_cons_of_mem candidate hx)

        cases hclear : s.dynamic.clear_p candidate with
        | false =>
            apply ih hrestSubset
            simpa [gpFindReachableNeighborAux, hclear] using haux

        | true =>
            cases hconnected :
                s.statics.connected_p candidate target with
            | false =>
                apply ih hrestSubset
                simpa [gpFindReachableNeighborAux, hclear, hconnected]
                  using haux

            | true =>
                cases hpathfind :
                    gpFindClearPath s start candidate with
                | none =>
                    apply ih hrestSubset
                    simpa [
                      gpFindReachableNeighborAux,
                      hclear,
                      hconnected,
                      hpathfind
                    ] using haux

                | some candidatePath =>
                    have heq :
                        (candidate, candidatePath) = (neighbor, path) := by
                      simpa [
                        gpFindReachableNeighborAux,
                        hclear,
                        hconnected,
                        hpathfind
                      ] using haux
                    cases heq
                    refine
                      ⟨hcandidateObj, hclear, hconnected, ?_⟩
                    exact
                      gpFindClearPath_sound
                        s
                        hwf
                        hstartLoc
                        hstartClear
                        hpathfind

  unfold gpFindReachableNeighbor at hfind
  exact aux
    s.statics.objects
    (by
      intro x hx
      exact hx)
    hfind

/--
Completeness of reachable-neighbor search.
-/
lemma gpFindReachableNeighbor_complete
    (s : State)
    (hwf : WellFormed s)
    {start target candidate : Obj}
    (hrobot : s.dynamic.robot_at_p start = true)
    (hcandidateLoc : s.statics.loc_t candidate = true)
    (hcandidateClear : s.dynamic.clear_p candidate = true)
    (hconnected :
      s.statics.connected_p candidate target = true)
    (hreachable :
      GPClearReachable s start candidate) :
    ∃ neighbor path,
      gpFindReachableNeighbor s start target =
        some (neighbor, path) := by
  have hwfCopy := hwf
  rcases hwfCopy with
    ⟨hstatic, hVR, _hVL, _hVS, _hVH, _hVG, _hVC,
     _hR1, _hL1, _hG1, _hClear, _hSH, hRC, _hHeld,
     _hArm, _hLX, _hRExists, _hTerrain, _hPartition⟩

  have hstartLoc : s.statics.loc_t start = true :=
    hVR start hrobot

  have hstartClear : s.dynamic.clear_p start = true :=
    hRC start hrobot

  have hcandidateObj : candidate ∈ s.statics.objects :=
    hstatic.2.2.2.1 candidate hcandidateLoc

  rcases
      gpFindClearPath_complete
        s
        hwf
        hstartLoc
        hstartClear
        hreachable with
    ⟨candidatePath, hcandidatePath⟩

  have aux :
      ∀ xs : List Obj,
        candidate ∈ xs →
        ∃ neighbor path,
          gpFindReachableNeighborAux s start target xs =
            some (neighbor, path) := by
    intro xs
    induction xs with
    | nil =>
        intro hmem
        simp at hmem

    | cons x xs ih =>
        intro hmem

        by_cases hxc : x = candidate
        · subst x
          refine ⟨candidate, candidatePath, ?_⟩
          simp [
            gpFindReachableNeighborAux,
            hcandidateClear,
            hconnected,
            hcandidatePath
          ]

        · have htail : candidate ∈ xs := by
            rcases List.mem_cons.mp hmem with hcandidateEq | htail
            · exact (hxc hcandidateEq.symm).elim
            · exact htail

          cases hxclear : s.dynamic.clear_p x with
          | false =>
              rcases ih htail with ⟨neighbor, path, hfind⟩
              refine ⟨neighbor, path, ?_⟩
              simpa [
                gpFindReachableNeighborAux,
                hxclear
              ] using hfind

          | true =>
              cases hxconnected :
                  s.statics.connected_p x target with
              | false =>
                  rcases ih htail with ⟨neighbor, path, hfind⟩
                  refine ⟨neighbor, path, ?_⟩
                  simpa [
                    gpFindReachableNeighborAux,
                    hxclear,
                    hxconnected
                  ] using hfind

              | true =>
                  cases hxpath :
                      gpFindClearPath s start x with
                  | none =>
                      rcases ih htail with ⟨neighbor, path, hfind⟩
                      refine ⟨neighbor, path, ?_⟩
                      simpa [
                        gpFindReachableNeighborAux,
                        hxclear,
                        hxconnected,
                        hxpath
                      ] using hfind

                  | some path =>
                      refine ⟨x, path, ?_⟩
                      simp [
                        gpFindReachableNeighborAux,
                        hxclear,
                        hxconnected,
                        hxpath
                      ]

  unfold gpFindReachableNeighbor
  exact aux s.statics.objects hcandidateObj

/-!
## Laser-frontier search and progress
-/

/--
Soundness of `gpFindLaserTarget`.

The selected target:

* is not the gold location;
* currently contains soft or hard rock;
* is adjacent to the returned clear neighbor; and
* is reachable through the returned clear path.
-/
lemma gpFindLaserTarget_sound
    (s : State)
    (hwf : WellFormed s)
    {start gold : Obj}
    {frontier : GPFrontier}
    (hrobot : s.dynamic.robot_at_p start = true)
    (hfind :
      gpFindLaserTarget s start gold = some frontier) :
    frontier.target ∈ s.statics.objects ∧
    frontier.target ≠ gold ∧
    (s.dynamic.soft_rock_at_p frontier.target = true ∨
     s.dynamic.hard_rock_at_p frontier.target = true) ∧
    s.dynamic.clear_p frontier.neighbor = true ∧
    s.statics.connected_p frontier.neighbor frontier.target = true ∧
    GPClearPath s start frontier.neighbor frontier.path := by
  have aux :
      ∀ xs : List Obj,
        (∀ x, x ∈ xs → x ∈ s.statics.objects) →
        gpFindLaserTargetAux s start gold xs = some frontier →
        frontier.target ∈ s.statics.objects ∧
        frontier.target ≠ gold ∧
        (s.dynamic.soft_rock_at_p frontier.target = true ∨
         s.dynamic.hard_rock_at_p frontier.target = true) ∧
        s.dynamic.clear_p frontier.neighbor = true ∧
        s.statics.connected_p frontier.neighbor frontier.target = true ∧
        GPClearPath s start frontier.neighbor frontier.path := by
    intro xs
    induction xs with
    | nil =>
        intro _hsubset haux
        simp [gpFindLaserTargetAux] at haux

    | cons candidate rest ih =>
        intro hsubset haux

        have hcandidateObj :
            candidate ∈ s.statics.objects :=
          hsubset candidate (by simp)

        have hrestSubset :
            ∀ x, x ∈ rest → x ∈ s.statics.objects := by
          intro x hx
          exact hsubset x (List.mem_cons_of_mem candidate hx)

        cases hcondition :
            ((!(candidate == gold)) &&
              (s.dynamic.soft_rock_at_p candidate ||
               s.dynamic.hard_rock_at_p candidate)) with
        | false =>
            apply ih hrestSubset
            simpa [gpFindLaserTargetAux, hcondition] using haux

        | true =>
            have hcandidateNe : candidate ≠ gold := by
              intro heq
              subst gold
              simp at hcondition

            have hrocks :
                s.dynamic.soft_rock_at_p candidate = true ∨
                s.dynamic.hard_rock_at_p candidate = true := by
              cases hsoft :
                  s.dynamic.soft_rock_at_p candidate with
              | true =>
                  exact Or.inl rfl
              | false =>
                  cases hhard :
                      s.dynamic.hard_rock_at_p candidate with
                  | true =>
                      exact Or.inr rfl
                  | false =>
                      simp [hsoft, hhard] at hcondition

            cases hneighbor :
                gpFindReachableNeighbor s start candidate with
            | none =>
                apply ih hrestSubset
                simpa [
                  gpFindLaserTargetAux,
                  hcondition,
                  hneighbor
                ] using haux

            | some result =>
                rcases result with ⟨neighbor, path⟩

                have heq :
                    ({
                      target := candidate
                      neighbor := neighbor
                      path := path
                    } : GPFrontier) = frontier := by
                  simpa [
                    gpFindLaserTargetAux,
                    hcondition,
                    hneighbor
                  ] using haux

                rcases
                    gpFindReachableNeighbor_sound
                      s
                      hwf
                      hrobot
                      hneighbor with
                  ⟨_hneighborObj, hneighborClear,
                   hneighborConnected, hneighborPath⟩

                cases heq
                exact
                  ⟨hcandidateObj,
                   hcandidateNe,
                   hrocks,
                   hneighborClear,
                   hneighborConnected,
                   hneighborPath⟩

  unfold gpFindLaserTarget at hfind
  exact aux
    s.statics.objects
    (by
      intro x hx
      exact hx)
    hfind

/--
If the gold is not clear-reachable, then either a soft-rock gold is
already adjacent to the reachable clear region, or there is a non-gold
laser frontier.

This is the graph-theoretic progress lemma underlying `gpLaserLoop`.
-/
lemma gpLaserTarget_exists_of_stuck
    (s : State)
    {bomb gold robot : Obj}
    (hinv : GPLaserLoopInv bomb gold s)
    (hrobot : s.dynamic.robot_at_p robot = true)
    (hpathNone : gpFindClearPath s robot gold = none)
    (hnoBombFinish :
      s.dynamic.soft_rock_at_p gold = true →
      gpFindReachableNeighbor s robot gold = none) :
    ∃ frontier,
      gpFindLaserTarget s robot gold = some frontier := by
  rcases hinv with
    ⟨hwf, _hbombAt, hgoldAt, _hholdsLaser,
     _hreturnToBomb, hgoldNotHard⟩

  have hwfCopy := hwf
  rcases hwfCopy with
    ⟨hstatic, hVR, _hVL, _hVS, _hVH, hVG, hVC,
     _hR1, _hL1, _hG1, _hClear, _hSH, hRC, _hHeld,
     _hArm, _hLX, _hRExists, hTerrain, _hPartition⟩

  have hvalidConnected : ValidConnectedParam s.statics :=
    hstatic.2.2.1
  have htypeHierarchy : ValidTypeHierarchy s.statics :=
    hstatic.2.2.2.1
  have hgraphConnected : ConnectedGraphConnected s.statics :=
    hstatic.2.2.2.2.2.2.1

  have hrobotLoc : s.statics.loc_t robot = true :=
    hVR robot hrobot
  have hrobotClear : s.dynamic.clear_p robot = true :=
    hRC robot hrobot
  have hgoldLoc : s.statics.loc_t gold = true :=
    hVG gold hgoldAt

  have hgoldNotReachable :
      ¬ GPClearReachable s robot gold :=
    (gpFindClearPath_eq_none_iff
      s hwf hrobotLoc hrobotClear).1 hpathNone

  have hstaticPath :
      Relation.ReflTransGen
        (fun x y => s.statics.connected_p x y = true)
        robot
        gold :=
    hgraphConnected robot gold hrobotLoc hgoldLoc

  have clear_of_reachable :
      ∀ {x : Obj},
        GPClearReachable s robot x →
        s.dynamic.clear_p x = true := by
    intro x hreach
    unfold GPClearReachable at hreach
    induction hreach with
    | refl =>
        exact hrobotClear
    | tail _hprefix hstep _ih =>
        exact hstep.2

  have boundary_exists :
      ∀ {z : Obj},
        Relation.ReflTransGen
            (fun x y => s.statics.connected_p x y = true)
            robot
            z →
        ¬ GPClearReachable s robot z →
        ∃ reachable boundary,
          GPClearReachable s robot reachable ∧
          s.statics.connected_p reachable boundary = true ∧
          ¬ s.dynamic.clear_p boundary = true := by
    intro z hpath
    induction hpath with
    | refl =>
        intro hnotReachable
        exact
          (hnotReachable
            (Relation.ReflTransGen.refl :
              GPClearReachable s robot robot)).elim

    | @tail previous current hprefix hstep ih =>
        intro hcurrentNotReachable
        by_cases hpreviousReachable :
            GPClearReachable s robot previous
        · have hcurrentNotClear :
              ¬ s.dynamic.clear_p current = true := by
            intro hcurrentClear
            apply hcurrentNotReachable
            exact Relation.ReflTransGen.tail
              hpreviousReachable
              ⟨hstep, hcurrentClear⟩
          exact
            ⟨previous, current, hpreviousReachable,
             hstep, hcurrentNotClear⟩
        · exact ih hpreviousReachable

  rcases boundary_exists hstaticPath hgoldNotReachable with
    ⟨reachable, target, hreachable,
     hconnected, htargetNotClear⟩

  have hreachableClear :
      s.dynamic.clear_p reachable = true :=
    clear_of_reachable hreachable

  have hreachableLoc :
      s.statics.loc_t reachable = true :=
    hVC reachable hreachableClear

  have htargetLoc :
      s.statics.loc_t target = true :=
    (hvalidConnected reachable target hconnected).2

  have htargetObj :
      target ∈ s.statics.objects :=
    htypeHierarchy target htargetLoc

  have htargetRocks :
      s.dynamic.soft_rock_at_p target = true ∨
      s.dynamic.hard_rock_at_p target = true := by
    rcases hTerrain target htargetLoc with
      htargetClear | htargetSoft | htargetHard
    · exact (htargetNotClear htargetClear).elim
    · exact Or.inl htargetSoft
    · exact Or.inr htargetHard

  have htargetNeGold : target ≠ gold := by
    intro htargetGold
    subst target

    have hgoldSoft :
        s.dynamic.soft_rock_at_p gold = true := by
      rcases htargetRocks with hsoft | hhard
      · exact hsoft
      · rw [hgoldNotHard] at hhard
        simp at hhard

    rcases
        gpFindReachableNeighbor_complete
          s
          hwf
          hrobot
          hreachableLoc
          hreachableClear
          hconnected
          hreachable with
      ⟨neighbor, path, hneighborSome⟩

    have hneighborNone :
        gpFindReachableNeighbor s robot gold = none :=
      hnoBombFinish hgoldSoft

    rw [hneighborNone] at hneighborSome
    simp at hneighborSome

  have hneighborExists :
      ∃ neighbor path,
        gpFindReachableNeighbor s robot target =
          some (neighbor, path) :=
    gpFindReachableNeighbor_complete
      s
      hwf
      hrobot
      hreachableLoc
      hreachableClear
      hconnected
      hreachable

  have htargetCondition :
      ((!(target == gold)) &&
        (s.dynamic.soft_rock_at_p target ||
         s.dynamic.hard_rock_at_p target)) = true := by
    rcases htargetRocks with hsoft | hhard
    · simp [htargetNeGold, hsoft]
    · simp [htargetNeGold, hhard]

  have search_complete :
      ∀ xs : List Obj,
        target ∈ xs →
        ∃ frontier,
          gpFindLaserTargetAux s robot gold xs =
            some frontier := by
    intro xs
    induction xs with
    | nil =>
        intro hmem
        simp at hmem

    | cons candidate rest ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst candidate
          rcases hneighborExists with
            ⟨neighbor, path, hneighbor⟩
          refine
            ⟨{
                target := target
                neighbor := neighbor
                path := path
              },
              ?_⟩
          simpa [
            gpFindLaserTargetAux,
            htargetCondition,
            hneighbor
          ]

        · cases hcondition :
            ((!(candidate == gold)) &&
              (s.dynamic.soft_rock_at_p candidate ||
               s.dynamic.hard_rock_at_p candidate)) with
          | false =>
              rcases ih htail with ⟨frontier, hfind⟩
              refine ⟨frontier, ?_⟩
              simpa [
                gpFindLaserTargetAux,
                hcondition
              ] using hfind

          | true =>
              cases hneighbor :
                  gpFindReachableNeighbor s robot candidate with
              | none =>
                  rcases ih htail with ⟨frontier, hfind⟩
                  refine ⟨frontier, ?_⟩
                  simpa [
                    gpFindLaserTargetAux,
                    hcondition,
                    hneighbor
                  ] using hfind

              | some result =>
                  rcases result with ⟨neighbor, path⟩
                  refine
                    ⟨{
                        target := candidate
                        neighbor := neighbor
                        path := path
                      },
                      ?_⟩
                  simpa [
                    gpFindLaserTargetAux,
                    hcondition,
                    hneighbor
                  ]

  unfold gpFindLaserTarget
  exact search_complete s.statics.objects htargetObj

/--
The number of non-gold obstacles is bounded by the number of objects.
-/
lemma gpObstacleCount_le_objects_length
    (s : State)
    (gold : Obj) :
    gpObstacleCount s gold ≤ s.statics.objects.length := by
  unfold gpObstacleCount
  exact List.length_filter_le
    (fun x : Obj =>
      (x != gold) &&
      (s.dynamic.soft_rock_at_p x ||
       s.dynamic.hard_rock_at_p x))
    s.statics.objects

/--
Adding an additional Boolean condition to a list filter cannot increase
the length of the filtered list.
-/
lemma gp_filter_left_and_length_le
    (xs : List Obj)
    (q p : Obj → Bool) :
    (xs.filter (fun x => q x && p x)).length ≤
      (xs.filter p).length := by
  induction xs with
  | nil =>
      simp
  | cons a xs ih =>
      cases hq : q a <;> cases hp : p a <;>
        simp [hq, hp] at * <;> omega

/--
Filtering out an object that occurs in a list and satisfies the original
predicate strictly decreases the filtered-list length.
-/
lemma gp_filter_without_member_length_lt
    (xs : List Obj)
    (p : Obj → Bool)
    (target : Obj)
    (hmem : target ∈ xs)
    (hp : p target = true) :
    (xs.filter (fun x => (x != target) && p x)).length <
      (xs.filter p).length := by
  induction xs with
  | nil =>
      simp at hmem

  | cons a xs ih =>
      by_cases hat : a = target
      · subst a
        have hle :
            (xs.filter (fun x => (x != target) && p x)).length ≤
              (xs.filter p).length :=
          gp_filter_left_and_length_le
            xs
            (fun x => x != target)
            p
        simpa [hp] using Nat.lt_succ_of_le hle

      · have htail : target ∈ xs := by
          rcases List.mem_cons.mp hmem with hhead | htail
          · exact (hat hhead.symm).elim
          · exact htail

        cases hpa : p a with
        | false =>
            simpa [hat, hpa] using ih htail
        | true =>
            simpa [hat, hpa] using
              Nat.succ_lt_succ (ih htail)

/--
Firing at a non-gold obstacle strictly decreases `gpObstacleCount`.
-/
lemma fire_laser_decreases_obstacle_count
    (s : State)
    {neighbor target gold : Obj}
    (htargetMem : target ∈ s.statics.objects)
    (hneGold : target ≠ gold)
    (hobstacle :
      s.dynamic.soft_rock_at_p target = true ∨
      s.dynamic.hard_rock_at_p target = true) :
    gpObstacleCount (fire_laser neighbor target s) gold <
      gpObstacleCount s gold := by
  have htargetObstacle :
      ((target != gold) &&
        (s.dynamic.soft_rock_at_p target ||
         s.dynamic.hard_rock_at_p target)) = true := by
    rcases hobstacle with hsoft | hhard
    · simp [hneGold, hsoft]
    · simp [hneGold, hhard]

  have hpred :
      (fun x : Obj =>
        (x != gold) &&
          ((fire_laser neighbor target s).dynamic.soft_rock_at_p x ||
           (fire_laser neighbor target s).dynamic.hard_rock_at_p x)) =
      (fun x : Obj =>
        (x != target) &&
          ((x != gold) &&
           (s.dynamic.soft_rock_at_p x ||
            s.dynamic.hard_rock_at_p x))) := by
    funext x
    by_cases hxt : x = target
    · subst x
      simp [fire_laser]
    · simp [fire_laser, hxt]

  unfold gpObstacleCount
  rw [fire_laser_statics neighbor target s]
  rw [hpred]
  exact
    gp_filter_without_member_length_lt
      s.statics.objects
      (fun x : Obj =>
        (x != gold) &&
          (s.dynamic.soft_rock_at_p x ||
           s.dynamic.hard_rock_at_p x))
      target
      htargetMem
      htargetObstacle

/-!
## Bomb finishing plan
-/

/--
Picking up a bomb preserves clear reachability because it changes neither
the static state nor the `clear_p` fluent.
-/
lemma pickup_bomb_preserves_clear_reachable
    (s : State)
    (bomb : Obj)
    {x y : Obj}
    (hreach : GPClearReachable s x y) :
    GPClearReachable (pickup_bomb bomb s) x y := by
  unfold GPClearReachable at hreach ⊢
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      apply Relation.ReflTransGen.tail ih
      simpa [GPClearStep, pickup_bomb] using hstep

/--
Correctness of `gpBombFinishPlan`.

The robot must be able to reach both the bomb and the selected neighbor
through the current clear region. The plan then:

1. reaches and picks up the bomb;
2. returns to the selected neighbor;
3. detonates the soft rock at the gold;
4. moves onto the gold location; and
5. picks up the gold.
-/
lemma gpBombFinishPlan_correct
    (s : State)
    {robot bomb gold neighbor : Obj}
    (hwf : WellFormed s)
    (hrobot : s.dynamic.robot_at_p robot = true)
    (harmEmpty : s.dynamic.arm_empty_p = true)
    (hbomb : s.statics.bomb_at_p bomb = true)
    (hgold : s.dynamic.gold_at_p gold = true)
    (hsoftGold : s.dynamic.soft_rock_at_p gold = true)
    (hneighborClear : s.dynamic.clear_p neighbor = true)
    (hneighborGold :
      s.statics.connected_p neighbor gold = true)
    (hreachBomb :
      GPClearReachable s robot bomb)
    (hreachNeighbor :
      GPClearReachable s robot neighbor) :
    ValidPlan (gpBombFinishPlan s bomb gold neighbor) s ∧
    (runPlan
      (gpBombFinishPlan s bomb gold neighbor)
      s).dynamic.holds_gold_p = true := by
  have hwfData := hwf
  rcases hwfData with
    ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
     hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
     hArm, hLX, hRExists, hTerrain, hPartition⟩

  have hrobotLoc : s.statics.loc_t robot = true :=
    hVR robot hrobot
  have hrobotClear : s.dynamic.clear_p robot = true :=
    hRC robot hrobot
  have hbombLoc : s.statics.loc_t bomb = true :=
    hstatic.2.1 bomb hbomb

  rcases gpFindRobot?_exists s hwf with
    ⟨foundRobot, hfindRobot, hfoundRobotAt, hfoundRobotLoc⟩
  have hfoundRobotEq : foundRobot = robot :=
    gpFindRobot?_unique s hwf hfindRobot hrobot
  subst foundRobot

  rcases
      gpFindClearPath_complete
        s hwf hrobotLoc hrobotClear hreachBomb with
    ⟨pathToBomb, hfindPathToBomb⟩

  have hpathToBomb :
      GPClearPath s robot bomb pathToBomb :=
    gpFindClearPath_sound
      s hwf hrobotLoc hrobotClear hfindPathToBomb

  rcases
      gpPathMoves_correct s hpathToBomb hrobot with
    ⟨hvalidToBomb, hrobotAtBomb, hsameAtBomb⟩

  rcases hsameAtBomb with
    ⟨hstaticsAtBomb, hlaserAtBomb, hsoftAtBomb,
     hhardAtBomb, hgoldAtBomb, harmAtBomb,
     hholdsBombAtBomb, hholdsLaserAtBomb,
     hholdsGoldAtBomb, hclearAtBomb⟩

  have hpickupBombPre :
      pickup_bombPre bomb
        (runPlan (gpPathMoves pathToBomb) s) := by
    refine ⟨?_, hrobotAtBomb, ?_, ?_⟩
    · rw [hstaticsAtBomb]
      exact hbombLoc
    · rw [hstaticsAtBomb]
      exact hbomb
    · rw [harmAtBomb]
      exact harmEmpty

  have hvalidPickupBomb :
      ValidPlan
        [PlanAction.pickup_bomb bomb]
        (runPlan (gpPathMoves pathToBomb) s) := by
    change
      pickup_bombPre bomb
          (runPlan (gpPathMoves pathToBomb) s) ∧
        True
    exact ⟨hpickupBombPre, True.intro⟩

  have hvalidInitial :
      ValidPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s := by
    exact
      (validPlan_append
        (gpPathMoves pathToBomb)
        [PlanAction.pickup_bomb bomb]
        s).2
        ⟨hvalidToBomb, hvalidPickupBomb⟩

  have hrunInitial :
      runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s =
        pickup_bomb bomb
          (runPlan (gpPathMoves pathToBomb) s) := by
    rw [runPlan_append]
    rfl

  have hwfAfterPickup :
      WellFormed
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s) :=
    validPlan_preserves_wf hvalidInitial hwf

  have hrobotAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).dynamic.robot_at_p bomb = true := by
    rw [hrunInitial]
    simpa only [pickup_bomb_robot_at_p] using hrobotAtBomb

  have hholdsBombAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).dynamic.holds_bomb_p = true := by
    rw [hrunInitial]
    exact
      pickup_bomb_holds_bomb_p
        bomb
        (runPlan (gpPathMoves pathToBomb) s)

  have hgoldAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).dynamic.gold_at_p gold = true := by
    rw [hrunInitial]
    rw [pickup_bomb_gold_at_p, hgoldAtBomb]
    exact hgold

  have hsoftAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).dynamic.soft_rock_at_p gold = true := by
    rw [hrunInitial]
    rw [pickup_bomb_soft_rock_at_p, hsoftAtBomb]
    exact hsoftGold

  have hreturnToRobot :
      GPClearReachable s bomb robot :=
    gpClearReachable_symm s hwf hrobotClear hreachBomb

  have hreachBombToNeighbor :
      GPClearReachable s bomb neighbor :=
    gpClearReachable_trans
      s hreturnToRobot hreachNeighbor

  have hreachAtBombState :
      GPClearReachable
        (runPlan (gpPathMoves pathToBomb) s)
        bomb
        neighbor :=
    gpSameExceptRobot_preserves_clear_reachable
      ⟨hstaticsAtBomb, hlaserAtBomb, hsoftAtBomb,
       hhardAtBomb, hgoldAtBomb, harmAtBomb,
       hholdsBombAtBomb, hholdsLaserAtBomb,
       hholdsGoldAtBomb, hclearAtBomb⟩
      hreachBombToNeighbor

  have hreachAfterPickup :
      GPClearReachable
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)
        bomb
        neighbor := by
    rw [hrunInitial]
    exact
      pickup_bomb_preserves_clear_reachable
        (runPlan (gpPathMoves pathToBomb) s)
        bomb
        hreachAtBombState

  have hwfAfterPickupData := hwfAfterPickup
  rcases hwfAfterPickupData with
    ⟨hstaticAfter, hVRAfter, hVLAfter, hVSAfter,
     hVHAfter, hVGAfter, hVCAfter, hR1After,
     hL1After, hG1After, hClearAfter, hSHAfter,
     hRCAfter, hHeldAfter, hArmAfter, hLXAfter,
     hRExistsAfter, hTerrainAfter, hPartitionAfter⟩

  have hbombLocAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).statics.loc_t bomb = true :=
    hVRAfter bomb hrobotAfterPickup

  have hbombClearAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).dynamic.clear_p bomb = true :=
    hRCAfter bomb hrobotAfterPickup

  rcases
      gpFindClearPath_complete
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)
        hwfAfterPickup
        hbombLocAfterPickup
        hbombClearAfterPickup
        hreachAfterPickup with
    ⟨pathToNeighbor, hfindPathToNeighbor⟩

  have hpathToNeighbor :
      GPClearPath
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)
        bomb
        neighbor
        pathToNeighbor :=
    gpFindClearPath_sound
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s)
      hwfAfterPickup
      hbombLocAfterPickup
      hbombClearAfterPickup
      hfindPathToNeighbor

  rcases
      gpPathMoves_correct
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)
        hpathToNeighbor
        hrobotAfterPickup with
    ⟨hvalidToNeighbor, hrobotAtNeighbor, hsameAtNeighbor⟩

  rcases hsameAtNeighbor with
    ⟨hstaticsAtNeighbor, hlaserAtNeighbor,
     hsoftAtNeighbor, hhardAtNeighbor,
     hgoldAtNeighbor, harmAtNeighbor,
     hholdsBombAtNeighbor, hholdsLaserAtNeighbor,
     hholdsGoldAtNeighbor, hclearAtNeighbor⟩

  have hstaticsAfterPickup :
      (runPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        s).statics = s.statics :=
    runPlan_statics
      (gpPathMoves pathToBomb ++
        [PlanAction.pickup_bomb bomb])
      s

  have hstaticsNeighborOriginal :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).statics = s.statics :=
    hstaticsAtNeighbor.trans hstaticsAfterPickup

  have hsoftAtNeighborGold :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).dynamic.soft_rock_at_p gold = true := by
    rw [hsoftAtNeighbor]
    exact hsoftAfterPickup

  have hgoldAtNeighborGold :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).dynamic.gold_at_p gold = true := by
    rw [hgoldAtNeighbor]
    exact hgoldAfterPickup

  have hholdsBombAtNeighborTrue :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).dynamic.holds_bomb_p = true := by
    rw [hholdsBombAtNeighbor]
    exact hholdsBombAfterPickup

  have hneighborLoc :
      s.statics.loc_t neighbor = true :=
    (hstatic.2.2.1 neighbor gold hneighborGold).1

  have hgoldLoc :
      s.statics.loc_t gold = true :=
    (hstatic.2.2.1 neighbor gold hneighborGold).2

  have hneighborLocCurrent :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).statics.loc_t neighbor = true := by
    rw [hstaticsNeighborOriginal]
    exact hneighborLoc

  have hgoldLocCurrent :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).statics.loc_t gold = true := by
    rw [hstaticsNeighborOriginal]
    exact hgoldLoc

  have hneighborGoldCurrent :
      (runPlan
        (gpPathMoves pathToNeighbor)
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).statics.connected_p neighbor gold = true := by
    rw [hstaticsNeighborOriginal]
    exact hneighborGold

  have hdetonatePre :
      detonate_bombPre
        neighbor
        gold
        (runPlan
          (gpPathMoves pathToNeighbor)
          (runPlan
            (gpPathMoves pathToBomb ++
              [PlanAction.pickup_bomb bomb])
            s)) :=
    ⟨hneighborLocCurrent,
     hgoldLocCurrent,
     hrobotAtNeighbor,
     hholdsBombAtNeighborTrue,
     hneighborGoldCurrent,
     hsoftAtNeighborGold⟩

  have hmoveGoldPre :
      movePre
        neighbor
        gold
        (detonate_bomb
          neighbor
          gold
          (runPlan
            (gpPathMoves pathToNeighbor)
            (runPlan
              (gpPathMoves pathToBomb ++
                [PlanAction.pickup_bomb bomb])
              s))) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [detonate_bomb_statics] using
        hneighborLocCurrent
    · simpa only [detonate_bomb_statics] using
        hgoldLocCurrent
    · simpa only [detonate_bomb_robot_at_p] using
        hrobotAtNeighbor
    · simpa only [detonate_bomb_statics] using
        hneighborGoldCurrent
    · exact
        detonate_bomb_clear_p_eq1
          neighbor
          gold
          (runPlan
            (gpPathMoves pathToNeighbor)
            (runPlan
              (gpPathMoves pathToBomb ++
                [PlanAction.pickup_bomb bomb])
              s))

  have hpickGoldPre :
      pick_goldPre
        gold
        (move
          neighbor
          gold
          (detonate_bomb
            neighbor
            gold
            (runPlan
              (gpPathMoves pathToNeighbor)
              (runPlan
                (gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb])
                s)))) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [move_statics, detonate_bomb_statics] using
        hgoldLocCurrent
    · exact
        move_robot_at_p_eq1
          neighbor
          gold
          (detonate_bomb
            neighbor
            gold
            (runPlan
              (gpPathMoves pathToNeighbor)
              (runPlan
                (gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb])
                s)))
    · simpa only [move_arm_empty_p] using
        detonate_bomb_arm_empty_p
          neighbor
          gold
          (runPlan
            (gpPathMoves pathToNeighbor)
            (runPlan
              (gpPathMoves pathToBomb ++
                [PlanAction.pickup_bomb bomb])
              s))
    · simpa only [
        move_gold_at_p,
        detonate_bomb_gold_at_p
      ] using hgoldAtNeighborGold

  have hvalidTail :
      ValidPlan
        [ PlanAction.detonate_bomb neighbor gold
        , PlanAction.move neighbor gold
        , PlanAction.pick_gold gold
        ]
        (runPlan
          (gpPathMoves pathToNeighbor)
          (runPlan
            (gpPathMoves pathToBomb ++
              [PlanAction.pickup_bomb bomb])
            s)) := by
    change
      detonate_bombPre
          neighbor
          gold
          (runPlan
            (gpPathMoves pathToNeighbor)
            (runPlan
              (gpPathMoves pathToBomb ++
                [PlanAction.pickup_bomb bomb])
              s)) ∧
      movePre
          neighbor
          gold
          (detonate_bomb
            neighbor
            gold
            (runPlan
              (gpPathMoves pathToNeighbor)
              (runPlan
                (gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb])
                s))) ∧
      pick_goldPre
          gold
          (move
            neighbor
            gold
            (detonate_bomb
              neighbor
              gold
              (runPlan
                (gpPathMoves pathToNeighbor)
                (runPlan
                  (gpPathMoves pathToBomb ++
                    [PlanAction.pickup_bomb bomb])
                  s)))) ∧
      True
    exact
      ⟨hdetonatePre, hmoveGoldPre, hpickGoldPre, True.intro⟩

  have hvalidRemainder :
      ValidPlan
        (gpPathMoves pathToNeighbor ++
          [ PlanAction.detonate_bomb neighbor gold
          , PlanAction.move neighbor gold
          , PlanAction.pick_gold gold
          ])
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s) := by
    exact
      (validPlan_append
        (gpPathMoves pathToNeighbor)
        [ PlanAction.detonate_bomb neighbor gold
        , PlanAction.move neighbor gold
        , PlanAction.pick_gold gold
        ]
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb])
          s)).2
        ⟨hvalidToNeighbor, hvalidTail⟩

  have hvalidAssociated :
      ValidPlan
        ((gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb]) ++
          (gpPathMoves pathToNeighbor ++
            [ PlanAction.detonate_bomb neighbor gold
            , PlanAction.move neighbor gold
            , PlanAction.pick_gold gold
            ]))
        s := by
    exact
      (validPlan_append
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_bomb bomb])
        (gpPathMoves pathToNeighbor ++
          [ PlanAction.detonate_bomb neighbor gold
          , PlanAction.move neighbor gold
          , PlanAction.pick_gold gold
          ])
        s).2
        ⟨hvalidInitial, hvalidRemainder⟩

  have hvalidFull :
      ValidPlan
        ((gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb]) ++
          gpPathMoves pathToNeighbor ++
          [ PlanAction.detonate_bomb neighbor gold
          , PlanAction.move neighbor gold
          , PlanAction.pick_gold gold
          ])
        s := by
    simpa only [List.append_assoc] using hvalidAssociated

  have htailHoldsGold :
      (runPlan
        [ PlanAction.detonate_bomb neighbor gold
        , PlanAction.move neighbor gold
        , PlanAction.pick_gold gold
        ]
        (runPlan
          (gpPathMoves pathToNeighbor)
          (runPlan
            (gpPathMoves pathToBomb ++
              [PlanAction.pickup_bomb bomb])
            s))).dynamic.holds_gold_p = true := by
    simpa only [runPlan, actionApply] using
      pick_gold_holds_gold_p
        gold
        (move
          neighbor
          gold
          (detonate_bomb
            neighbor
            gold
            (runPlan
              (gpPathMoves pathToNeighbor)
              (runPlan
                (gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb])
                s))))

  have hholdsGoldFull :
      (runPlan
        ((gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb]) ++
          gpPathMoves pathToNeighbor ++
          [ PlanAction.detonate_bomb neighbor gold
          , PlanAction.move neighbor gold
          , PlanAction.pick_gold gold
          ])
        s).dynamic.holds_gold_p = true := by
    calc
      (runPlan
        ((gpPathMoves pathToBomb ++
            [PlanAction.pickup_bomb bomb]) ++
          gpPathMoves pathToNeighbor ++
          [ PlanAction.detonate_bomb neighbor gold
          , PlanAction.move neighbor gold
          , PlanAction.pick_gold gold
          ])
        s).dynamic.holds_gold_p =
          (runPlan
            [ PlanAction.detonate_bomb neighbor gold
            , PlanAction.move neighbor gold
            , PlanAction.pick_gold gold
            ]
            (runPlan
              ((gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb]) ++
                gpPathMoves pathToNeighbor)
              s)).dynamic.holds_gold_p := by
                rw [runPlan_append]
      _ =
          (runPlan
            [ PlanAction.detonate_bomb neighbor gold
            , PlanAction.move neighbor gold
            , PlanAction.pick_gold gold
            ]
            (runPlan
              (gpPathMoves pathToNeighbor)
              (runPlan
                (gpPathMoves pathToBomb ++
                  [PlanAction.pickup_bomb bomb])
                s))).dynamic.holds_gold_p := by
                  rw [runPlan_append]
      _ = true := htailHoldsGold

  simpa only [
    gpBombFinishPlan,
    hfindRobot,
    hfindPathToBomb,
    hfindPathToNeighbor
  ] using And.intro hvalidFull hholdsGoldFull

/-!
## Establishing and maintaining the laser-loop invariant
-/

/--
Moving to the bomb and picking up the laser establishes the invariant
required by `gpLaserLoop`.
-/
lemma gpLaserStartPlan_correct
    (s : State)
    {robot bomb gold : Obj}
    {pathToBomb : List Obj}
    (hwf : WellFormed s)
    (hpath : GPClearPath s robot bomb pathToBomb)
    (hrobot : s.dynamic.robot_at_p robot = true)
    (harmEmpty : s.dynamic.arm_empty_p = true)
    (hbomb : s.statics.bomb_at_p bomb = true)
    (hlaser : s.dynamic.laser_at_p bomb = true)
    (hgold : s.dynamic.gold_at_p gold = true)
    (hgoldNotHard : s.dynamic.hard_rock_at_p gold = false) :
    let initialActions :=
      gpPathMoves pathToBomb ++
      [PlanAction.pickup_laser bomb]
    ValidPlan initialActions s ∧
    GPLaserLoopInv
      bomb
      gold
      (runPlan initialActions s) := by
  dsimp

  have hbombLoc : s.statics.loc_t bomb = true :=
    hwf.1.2.1 bomb hbomb

  rcases gpPathMoves_correct s hpath hrobot with
    ⟨hvalidMoves, hrobotAtBomb, hsameAfterMoves⟩

  rcases hsameAfterMoves with
    ⟨hstaticsAfterMoves, hlaserAfterMoves,
     _hsoftAfterMoves, hhardAfterMoves,
     hgoldAfterMoves, harmAfterMoves,
     _hholdsBombAfterMoves, _hholdsLaserAfterMoves,
     _hholdsGoldAfterMoves, _hclearAfterMoves⟩

  have hpickupPre :
      pickup_laserPre
        bomb
        (runPlan (gpPathMoves pathToBomb) s) := by
    refine ⟨?_, hrobotAtBomb, ?_, ?_⟩
    · rw [hstaticsAfterMoves]
      exact hbombLoc
    · rw [hlaserAfterMoves]
      exact hlaser
    · rw [harmAfterMoves]
      exact harmEmpty

  have hvalidPickup :
      ValidPlan
        [PlanAction.pickup_laser bomb]
        (runPlan (gpPathMoves pathToBomb) s) := by
    change
      pickup_laserPre
          bomb
          (runPlan (gpPathMoves pathToBomb) s) ∧
        True
    exact ⟨hpickupPre, True.intro⟩

  have hvalidInitial :
      ValidPlan
        (gpPathMoves pathToBomb ++
          [PlanAction.pickup_laser bomb])
        s := by
    exact
      (validPlan_append
        (gpPathMoves pathToBomb)
        [PlanAction.pickup_laser bomb]
        s).2
        ⟨hvalidMoves, hvalidPickup⟩

  have hwfAfterPickup :
      WellFormed
        (runPlan
          (gpPathMoves pathToBomb ++
            [PlanAction.pickup_laser bomb])
          s) :=
    validPlan_preserves_wf hvalidInitial hwf

  refine ⟨hvalidInitial, ?_⟩
  unfold GPLaserLoopInv
  refine
    ⟨hwfAfterPickup, ?_, ?_, ?_, ?_, ?_⟩

  · simpa only [runPlan_statics] using hbomb

  · rw [runPlan_append]
    change
      (pickup_laser
        bomb
        (runPlan (gpPathMoves pathToBomb) s)).dynamic.gold_at_p gold =
        true
    rw [pickup_laser_gold_at_p, hgoldAfterMoves]
    exact hgold

  · rw [runPlan_append]
    change
      (pickup_laser
        bomb
        (runPlan (gpPathMoves pathToBomb) s)).dynamic.holds_laser_p =
        true
    exact
      pickup_laser_holds_laser_p
        bomb
        (runPlan (gpPathMoves pathToBomb) s)

  · refine ⟨bomb, ?_, ?_⟩
    · rw [runPlan_append]
      change
        (pickup_laser
          bomb
          (runPlan (gpPathMoves pathToBomb) s)).dynamic.robot_at_p bomb =
          true
      simpa only [pickup_laser_robot_at_p] using hrobotAtBomb
    · exact Relation.ReflTransGen.refl

  · rw [runPlan_append]
    change
      (pickup_laser
        bomb
        (runPlan (gpPathMoves pathToBomb) s)).dynamic.hard_rock_at_p gold =
        false
    rw [pickup_laser_hard_rock_at_p, hhardAfterMoves]
    exact hgoldNotHard

/--
Putting down the laser preserves structural clear paths because it changes
neither the static state nor the `clear_p` fluent.
-/
lemma gpPathFrom_putdown_laser
    (s : State)
    (var_x : Obj)
    {current goal : Obj}
    {rest : List Obj} :
    GPPathFrom (putdown_laser var_x s) current rest goal ↔
      GPPathFrom s current rest goal := by
  induction rest generalizing current with
  | nil =>
      simp only [
        GPPathFrom,
        putdown_laser_statics,
        putdown_laser_clear_p
      ]
  | cons next rest ih =>
      simp only [
        GPPathFrom,
        putdown_laser_statics,
        putdown_laser_clear_p,
        ih
      ]

/--
Putting down the laser preserves concrete clear paths.
-/
lemma gpClearPath_putdown_laser
    (s : State)
    (var_x : Obj)
    {start goal : Obj}
    {path : List Obj} :
    GPClearPath (putdown_laser var_x s) start goal path ↔
      GPClearPath s start goal path := by
  constructor
  · rintro ⟨rest, hpath, hfrom⟩
    exact
      ⟨rest, hpath,
       (gpPathFrom_putdown_laser s var_x).1 hfrom⟩
  · rintro ⟨rest, hpath, hfrom⟩
    exact
      ⟨rest, hpath,
       (gpPathFrom_putdown_laser s var_x).2 hfrom⟩

/--
Putting down the laser preserves clear reachability.
-/
lemma putdown_laser_preserves_clear_reachable
    (s : State)
    (var_x : Obj)
    {x y : Obj}
    (hreach : GPClearReachable s x y) :
    GPClearReachable (putdown_laser var_x s) x y := by
  unfold GPClearReachable at hreach ⊢
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      apply Relation.ReflTransGen.tail ih
      simpa [GPClearStep, putdown_laser] using hstep

/--
Firing the laser preserves every previously existing clear path: it keeps
the static graph unchanged and can only make an additional location clear.
-/
lemma fire_laser_preserves_clear_reachable
    (s : State)
    (var_x var_y : Obj)
    {x y : Obj}
    (hreach : GPClearReachable s x y) :
    GPClearReachable (fire_laser var_x var_y s) x y := by
  unfold GPClearReachable at hreach ⊢
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail previous current hprefix hstep ih =>
      apply Relation.ReflTransGen.tail ih
      rcases hstep with ⟨hconnected, hclear⟩
      refine ⟨?_, ?_⟩
      · exact hconnected
      · by_cases hcurrent : current = var_y
        · subst current
          simp [fire_laser]
        · simpa [fire_laser, hcurrent] using hclear

/--
Main inductive correctness theorem for `gpLaserLoop`.
-/
lemma gpLaserLoop_correct
    (bomb gold fuel : Nat)
    (s : State)
    (hinv : GPLaserLoopInv bomb gold s)
    (hfuel : gpObstacleCount s gold < fuel) :
    ValidPlan (gpLaserLoop bomb gold fuel s) s ∧
    (runPlan
      (gpLaserLoop bomb gold fuel s)
      s).dynamic.holds_gold_p = true := by
  induction fuel generalizing s with
  | zero =>
      omega

  | succ fuel' ih =>
      have hinvCopy := hinv
      rcases hinv with
        ⟨hwf, hbomb, hgold, hholdsLaser,
         hreturnToBomb, hgoldNotHard⟩

      have hwfData := hwf
      rcases hwfData with
        ⟨hstatic, hVR, hVL, hVS, hVH, hVG, hVC,
         hR1, hL1, hG1, hClear, hSH, hRC, hHeld,
         hArm, hLX, hRExists, hTerrain, hPartition⟩

      rcases gpFindRobot?_exists s hwf with
        ⟨robot, hfindRobot, hrobot, hrobotLoc⟩

      have hrobotClear : s.dynamic.clear_p robot = true :=
        hRC robot hrobot

      rcases hreturnToBomb with
        ⟨actualRobot, hactualRobot, hactualReachBomb⟩
      have hrobotEq :
          robot = actualRobot :=
        gpFindRobot?_unique
          s hwf hfindRobot hactualRobot
      subst actualRobot

      have hreachBomb :
          GPClearReachable s robot bomb :=
        hactualReachBomb

      cases hpathFind :
          gpFindClearPath s robot gold with
      | some pathToGold =>
          have hpathToGold :
              GPClearPath s robot gold pathToGold :=
            gpFindClearPath_sound
              s hwf hrobotLoc hrobotClear hpathFind

          have hputdownPre :
              putdown_laserPre robot s :=
            ⟨hrobotLoc, hrobot, hholdsLaser⟩

          have hvalidPutdown :
              ValidPlan [PlanAction.putdown_laser robot] s := by
            change putdown_laserPre robot s ∧ True
            exact ⟨hputdownPre, True.intro⟩

          have hwfAfterPutdown :
              WellFormed (putdown_laser robot s) :=
            putdown_laser_preserves_wf
              robot s hwf hputdownPre

          have hpathAfterPutdown :
              GPClearPath
                (putdown_laser robot s)
                robot
                gold
                pathToGold :=
            (gpClearPath_putdown_laser s robot).2 hpathToGold

          have hrobotAfterPutdown :
              (putdown_laser robot s).dynamic.robot_at_p robot = true := by
            simpa only [putdown_laser_robot_at_p] using hrobot

          have hgoldAfterPutdown :
              (putdown_laser robot s).dynamic.gold_at_p gold = true := by
            simpa only [putdown_laser_gold_at_p] using hgold

          have harmAfterPutdown :
              (putdown_laser robot s).dynamic.arm_empty_p = true :=
            putdown_laser_arm_empty_p robot s

          have hdirect :=
            gpDirectGoldPlan_correct
              (putdown_laser robot s)
              hwfAfterPutdown
              hpathAfterPutdown
              hrobotAfterPutdown
              harmAfterPutdown
              hgoldAfterPutdown

          have hcombined :
              ValidPlan
                ([PlanAction.putdown_laser robot] ++
                  (gpPathMoves pathToGold ++
                    [PlanAction.pick_gold gold]))
                s ∧
              (runPlan
                ([PlanAction.putdown_laser robot] ++
                  (gpPathMoves pathToGold ++
                    [PlanAction.pick_gold gold]))
                s).dynamic.holds_gold_p = true := by
            constructor
            · exact
                (validPlan_append
                  [PlanAction.putdown_laser robot]
                  (gpPathMoves pathToGold ++
                    [PlanAction.pick_gold gold])
                  s).2
                  ⟨hvalidPutdown, hdirect.1⟩
            · rw [runPlan_append]
              exact hdirect.2

          simpa [
            gpLaserLoop,
            hfindRobot,
            hpathFind,
            List.append_assoc
          ] using hcombined

      | none =>
          have laserBranch :
              ∀ frontier : GPFrontier,
                gpFindLaserTarget s robot gold = some frontier →
                let laserActions :=
                  gpPathMoves frontier.path ++
                  [PlanAction.fire_laser
                    frontier.neighbor
                    frontier.target]
                let nextState := runPlan laserActions s
                ValidPlan
                    (laserActions ++
                      gpLaserLoop bomb gold fuel' nextState)
                    s ∧
                  (runPlan
                    (laserActions ++
                      gpLaserLoop bomb gold fuel' nextState)
                    s).dynamic.holds_gold_p = true := by
            intro frontier hfindFrontier
            dsimp

            rcases
                gpFindLaserTarget_sound
                  s hwf hrobot hfindFrontier with
              ⟨htargetMem, htargetNeGold, htargetObstacle,
               hneighborClear, hneighborConnected,
               hfrontierPath⟩

            rcases
                gpPathMoves_correct
                  s hfrontierPath hrobot with
              ⟨hvalidMoves, hrobotAtNeighbor, hsameAfterMoves⟩

            have hsameAfterMovesCopy := hsameAfterMoves
            rcases hsameAfterMovesCopy with
              ⟨hstaticsAfterMoves, hlaserAfterMoves,
               hsoftAfterMoves, hhardAfterMoves,
               hgoldAfterMoves, harmAfterMoves,
               hholdsBombAfterMoves, hholdsLaserAfterMoves,
               hholdsGoldAfterMoves, hclearAfterMoves⟩

            have hlocations :
                s.statics.loc_t frontier.neighbor = true ∧
                s.statics.loc_t frontier.target = true :=
              hstatic.2.2.1
                frontier.neighbor
                frontier.target
                hneighborConnected

            have hfirePre :
                fire_laserPre
                  frontier.neighbor
                  frontier.target
                  (runPlan
                    (gpPathMoves frontier.path)
                    s) := by
              refine
                ⟨?_, ?_, hrobotAtNeighbor, ?_, ?_⟩
              · rw [hstaticsAfterMoves]
                exact hlocations.1
              · rw [hstaticsAfterMoves]
                exact hlocations.2
              · rw [hholdsLaserAfterMoves]
                exact hholdsLaser
              · rw [hstaticsAfterMoves]
                exact hneighborConnected

            have hvalidFire :
                ValidPlan
                  [PlanAction.fire_laser
                    frontier.neighbor
                    frontier.target]
                  (runPlan
                    (gpPathMoves frontier.path)
                    s) := by
              change
                fire_laserPre
                    frontier.neighbor
                    frontier.target
                    (runPlan
                      (gpPathMoves frontier.path)
                      s) ∧
                  True
              exact ⟨hfirePre, True.intro⟩

            have hvalidLaserActions :
                ValidPlan
                  (gpPathMoves frontier.path ++
                    [PlanAction.fire_laser
                      frontier.neighbor
                      frontier.target])
                  s :=
              (validPlan_append
                (gpPathMoves frontier.path)
                [PlanAction.fire_laser
                  frontier.neighbor
                  frontier.target]
                s).2
                ⟨hvalidMoves, hvalidFire⟩

            have hrunLaserActions :
                runPlan
                    (gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target])
                    s =
                  fire_laser
                    frontier.neighbor
                    frontier.target
                    (runPlan
                      (gpPathMoves frontier.path)
                      s) := by
              rw [runPlan_append]
              rfl

            have hwfNext :
                WellFormed
                  (runPlan
                    (gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target])
                    s) :=
              validPlan_preserves_wf hvalidLaserActions hwf

            have htargetMemAfterMoves :
                frontier.target ∈
                  (runPlan
                    (gpPathMoves frontier.path)
                    s).statics.objects := by
              rw [hstaticsAfterMoves]
              exact htargetMem

            have htargetObstacleAfterMoves :
                (runPlan
                    (gpPathMoves frontier.path)
                    s).dynamic.soft_rock_at_p frontier.target = true ∨
                (runPlan
                    (gpPathMoves frontier.path)
                    s).dynamic.hard_rock_at_p frontier.target = true := by
              rcases htargetObstacle with hsoft | hhard
              · left
                rw [hsoftAfterMoves]
                exact hsoft
              · right
                rw [hhardAfterMoves]
                exact hhard

            have hcountAfterMoves :
                gpObstacleCount
                    (runPlan
                      (gpPathMoves frontier.path)
                      s)
                    gold =
                  gpObstacleCount s gold := by
              unfold gpObstacleCount
              rw [
                hstaticsAfterMoves,
                hsoftAfterMoves,
                hhardAfterMoves
              ]

            have hcountDecreases :
                gpObstacleCount
                    (runPlan
                      (gpPathMoves frontier.path ++
                        [PlanAction.fire_laser
                          frontier.neighbor
                          frontier.target])
                      s)
                    gold <
                  gpObstacleCount s gold := by
              rw [hrunLaserActions]
              calc
                gpObstacleCount
                    (fire_laser
                      frontier.neighbor
                      frontier.target
                      (runPlan
                        (gpPathMoves frontier.path)
                        s))
                    gold <
                    gpObstacleCount
                      (runPlan
                        (gpPathMoves frontier.path)
                        s)
                      gold :=
                  fire_laser_decreases_obstacle_count
                    (runPlan
                      (gpPathMoves frontier.path)
                      s)
                    htargetMemAfterMoves
                    htargetNeGold
                    htargetObstacleAfterMoves
                _ = gpObstacleCount s gold :=
                  hcountAfterMoves

            have hfuelNext :
                gpObstacleCount
                    (runPlan
                      (gpPathMoves frontier.path ++
                        [PlanAction.fire_laser
                          frontier.neighbor
                          frontier.target])
                      s)
                    gold <
                  fuel' := by
              omega

            have hreachRobotNeighbor :
                GPClearReachable
                  s
                  robot
                  frontier.neighbor :=
              gpClearPath_reachable hfrontierPath

            have hreachNeighborRobot :
                GPClearReachable
                  s
                  frontier.neighbor
                  robot :=
              gpClearReachable_symm
                s hwf hrobotClear hreachRobotNeighbor

            have hreachNeighborBomb :
                GPClearReachable
                  s
                  frontier.neighbor
                  bomb :=
              gpClearReachable_trans
                s
                hreachNeighborRobot
                hreachBomb

            have hreachAfterMoves :
                GPClearReachable
                  (runPlan
                    (gpPathMoves frontier.path)
                    s)
                  frontier.neighbor
                  bomb :=
              gpSameExceptRobot_preserves_clear_reachable
                hsameAfterMoves
                hreachNeighborBomb

            have hreachNext :
                GPClearReachable
                  (runPlan
                    (gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target])
                    s)
                  frontier.neighbor
                  bomb := by
              rw [hrunLaserActions]
              exact
                fire_laser_preserves_clear_reachable
                  (runPlan
                    (gpPathMoves frontier.path)
                    s)
                  frontier.neighbor
                  frontier.target
                  hreachAfterMoves

            have hinvNext :
                GPLaserLoopInv
                  bomb
                  gold
                  (runPlan
                    (gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target])
                    s) := by
              unfold GPLaserLoopInv
              refine
                ⟨hwfNext, ?_, ?_, ?_, ?_, ?_⟩

              · simpa only [runPlan_statics] using hbomb

              · rw [hrunLaserActions]
                rw [
                  fire_laser_gold_at_p_ne
                    frontier.neighbor
                    frontier.target
                    (runPlan
                      (gpPathMoves frontier.path)
                      s)
                    (Ne.symm htargetNeGold),
                  hgoldAfterMoves
                ]
                exact hgold

              · rw [hrunLaserActions]
                rw [
                  fire_laser_holds_laser_p,
                  hholdsLaserAfterMoves
                ]
                exact hholdsLaser

              · refine ⟨frontier.neighbor, ?_, hreachNext⟩
                rw [hrunLaserActions]
                simpa only [fire_laser_robot_at_p] using
                  hrobotAtNeighbor

              · rw [hrunLaserActions]
                rw [
                  fire_laser_hard_rock_at_p_ne
                    frontier.neighbor
                    frontier.target
                    (runPlan
                      (gpPathMoves frontier.path)
                      s)
                    (Ne.symm htargetNeGold),
                  hhardAfterMoves
                ]
                exact hgoldNotHard

            have hrecursive :=
              ih
                (s :=
                  runPlan
                    (gpPathMoves frontier.path ++
                      [PlanAction.fire_laser
                        frontier.neighbor
                        frontier.target])
                    s)
                hinvNext
                hfuelNext

            constructor
            · exact
                (validPlan_append
                  (gpPathMoves frontier.path ++
                    [PlanAction.fire_laser
                      frontier.neighbor
                      frontier.target])
                  (gpLaserLoop
                    bomb
                    gold
                    fuel'
                    (runPlan
                      (gpPathMoves frontier.path ++
                        [PlanAction.fire_laser
                          frontier.neighbor
                          frontier.target])
                      s))
                  s).2
                  ⟨hvalidLaserActions, hrecursive.1⟩
            · rw [runPlan_append]
              exact hrecursive.2

          cases hsoft : s.dynamic.soft_rock_at_p gold with
          | true =>
              cases hneighborFind :
                  gpFindReachableNeighbor s robot gold with
              | some result =>
                  rcases result with ⟨neighbor, neighborPath⟩

                  rcases
                      gpFindReachableNeighbor_sound
                        s hwf hrobot hneighborFind with
                    ⟨_hneighborMem, hneighborClear,
                     hneighborGold, hneighborPathCorrect⟩

                  have hputdownPre :
                      putdown_laserPre robot s :=
                    ⟨hrobotLoc, hrobot, hholdsLaser⟩

                  have hvalidPutdown :
                      ValidPlan
                        [PlanAction.putdown_laser robot]
                        s := by
                    change putdown_laserPre robot s ∧ True
                    exact ⟨hputdownPre, True.intro⟩

                  have hwfAfterPutdown :
                      WellFormed (putdown_laser robot s) :=
                    putdown_laser_preserves_wf
                      robot s hwf hputdownPre

                  have hrobotAfterPutdown :
                      (putdown_laser robot s).dynamic.robot_at_p robot =
                        true := by
                    simpa only [putdown_laser_robot_at_p] using hrobot

                  have harmAfterPutdown :
                      (putdown_laser robot s).dynamic.arm_empty_p = true :=
                    putdown_laser_arm_empty_p robot s

                  have hbombAfterPutdown :
                      (putdown_laser robot s).statics.bomb_at_p bomb =
                        true := by
                    simpa only [putdown_laser_statics] using hbomb

                  have hgoldAfterPutdown :
                      (putdown_laser robot s).dynamic.gold_at_p gold =
                        true := by
                    simpa only [putdown_laser_gold_at_p] using hgold

                  have hsoftAfterPutdown :
                      (putdown_laser robot s).dynamic.soft_rock_at_p gold =
                        true := by
                    simpa only [putdown_laser_soft_rock_at_p] using hsoft

                  have hneighborClearAfterPutdown :
                      (putdown_laser robot s).dynamic.clear_p neighbor =
                        true := by
                    simpa only [putdown_laser_clear_p] using
                      hneighborClear

                  have hneighborGoldAfterPutdown :
                      (putdown_laser robot s).statics.connected_p
                          neighbor gold =
                        true := by
                    simpa only [putdown_laser_statics] using
                      hneighborGold

                  have hreachBombAfterPutdown :
                      GPClearReachable
                        (putdown_laser robot s)
                        robot
                        bomb :=
                    putdown_laser_preserves_clear_reachable
                      s robot hreachBomb

                  have hreachNeighbor :
                      GPClearReachable s robot neighbor :=
                    gpClearPath_reachable hneighborPathCorrect

                  have hreachNeighborAfterPutdown :
                      GPClearReachable
                        (putdown_laser robot s)
                        robot
                        neighbor :=
                    putdown_laser_preserves_clear_reachable
                      s robot hreachNeighbor

                  have hbombFinish :=
                    gpBombFinishPlan_correct
                      (putdown_laser robot s)
                      hwfAfterPutdown
                      hrobotAfterPutdown
                      harmAfterPutdown
                      hbombAfterPutdown
                      hgoldAfterPutdown
                      hsoftAfterPutdown
                      hneighborClearAfterPutdown
                      hneighborGoldAfterPutdown
                      hreachBombAfterPutdown
                      hreachNeighborAfterPutdown

                  have hcombined :
                      ValidPlan
                        ([PlanAction.putdown_laser robot] ++
                          gpBombFinishPlan
                            (putdown_laser robot s)
                            bomb
                            gold
                            neighbor)
                        s ∧
                      (runPlan
                        ([PlanAction.putdown_laser robot] ++
                          gpBombFinishPlan
                            (putdown_laser robot s)
                            bomb
                            gold
                            neighbor)
                        s).dynamic.holds_gold_p = true := by
                    constructor
                    · exact
                        (validPlan_append
                          [PlanAction.putdown_laser robot]
                          (gpBombFinishPlan
                            (putdown_laser robot s)
                            bomb
                            gold
                            neighbor)
                          s).2
                          ⟨hvalidPutdown, hbombFinish.1⟩
                    · rw [runPlan_append]
                      exact hbombFinish.2

                  simpa [
                    gpLaserLoop,
                    hfindRobot,
                    hpathFind,
                    hsoft,
                    hneighborFind,
                    actionApply,
                    List.append_assoc
                  ] using hcombined

              | none =>
                  rcases
                      gpLaserTarget_exists_of_stuck
                        s
                        hinvCopy
                        hrobot
                        hpathFind
                        (by
                          intro _
                          exact hneighborFind) with
                    ⟨frontier, hfindFrontier⟩

                  have hbranch :=
                    laserBranch frontier hfindFrontier

                  simpa [
                    gpLaserLoop,
                    hfindRobot,
                    hpathFind,
                    hsoft,
                    hneighborFind,
                    hfindFrontier,
                    List.append_assoc
                  ] using hbranch

          | false =>
              have hnoBombFinish :
                  s.dynamic.soft_rock_at_p gold = true →
                  gpFindReachableNeighbor s robot gold = none := by
                intro hsoftTrue
                rw [hsoft] at hsoftTrue
                simp at hsoftTrue

              rcases
                  gpLaserTarget_exists_of_stuck
                    s
                    hinvCopy
                    hrobot
                    hpathFind
                    hnoBombFinish with
                ⟨frontier, hfindFrontier⟩

              have hbranch :=
                laserBranch frontier hfindFrontier

              simpa [
                gpLaserLoop,
                hfindRobot,
                hpathFind,
                hsoft,
                hfindFrontier,
                List.append_assoc
              ] using hbranch

/-!
## Core correctness of solve
-/

/--
Core planner correctness for an arbitrary goal.

The implementation of `solve` does not inspect the goal, so its validity
and its achievement of `holds_gold_p` are independent of the particular
goal representation.
-/
lemma solve_achieves_gold_for_goal
    (s : State)
    (g : Goal)
    (hinit : WellFormedInit s) :
    ValidPlan (solve s g) s ∧
    (runPlan (solve s g) s).dynamic.holds_gold_p = true := by
  rcases hinit with
    ⟨hwf, harmEmpty, _hInitRobotClear, hLaserAtBomb,
     hGoldNotHard, hClearToBomb, hGoldExists⟩

  have hwfData := hwf
  rcases hwfData with
    ⟨hstatic, hVR, _hVL, _hVS, _hVH, _hVG, _hVC,
     _hR1, _hL1, _hG1, _hClear, _hSH, hRC, _hHeld,
     _hArm, _hLX, _hRExists, _hTerrain, _hPartition⟩

  rcases gpFindRobot?_exists s hwf with
    ⟨robot, hfindRobot, hrobot, hrobotLoc⟩
  rcases gpFindBomb?_exists s hstatic with
    ⟨bomb, hfindBomb, hbomb, _hbombLoc⟩
  rcases gpFindGold?_exists s hwf hGoldExists with
    ⟨gold, hfindGold, hgold, _hgoldLoc⟩

  have hrobotClear : s.dynamic.clear_p robot = true :=
    hRC robot hrobot

  have hreachBomb :
      GPClearReachable s robot bomb := by
    change
      Relation.ReflTransGen
        (fun a b =>
          s.statics.connected_p a b = true ∧
          s.dynamic.clear_p b = true)
        robot
        bomb
    exact hClearToBomb robot bomb hrobot hbomb

  have hlaserAtBomb :
      s.dynamic.laser_at_p bomb = true :=
    (hLaserAtBomb bomb).2 hbomb

  have hgoldNotHard :
      s.dynamic.hard_rock_at_p gold = false :=
    hGoldNotHard gold hgold

  cases hpathFind : gpFindClearPath s robot gold with
  | some pathToGold =>
      have hpathToGold :
          GPClearPath s robot gold pathToGold :=
        gpFindClearPath_sound
          s
          hwf
          hrobotLoc
          hrobotClear
          hpathFind

      have hdirect :=
        gpDirectGoldPlan_correct
          s
          hwf
          hpathToGold
          hrobot
          harmEmpty
          hgold

      simpa [
        solve,
        hfindRobot,
        hfindBomb,
        hfindGold,
        hpathFind
      ] using hdirect

  | none =>
      rcases
          gpFindClearPath_complete
            s
            hwf
            hrobotLoc
            hrobotClear
            hreachBomb with
        ⟨pathToBomb, hfindPathToBomb⟩

      have hpathToBomb :
          GPClearPath s robot bomb pathToBomb :=
        gpFindClearPath_sound
          s
          hwf
          hrobotLoc
          hrobotClear
          hfindPathToBomb

      let initialActions :=
        gpPathMoves pathToBomb ++
        [PlanAction.pickup_laser bomb]

      let afterPickup :=
        runPlan initialActions s

      have hstart :
          ValidPlan initialActions s ∧
          GPLaserLoopInv bomb gold afterPickup := by
        simpa only [initialActions, afterPickup] using
          (gpLaserStartPlan_correct
            (s := s)
            (robot := robot)
            (bomb := bomb)
            (gold := gold)
            (pathToBomb := pathToBomb)
            hwf
            hpathToBomb
            hrobot
            harmEmpty
            hbomb
            hlaserAtBomb
            hgold
            hgoldNotHard)

      have hstaticsAfterPickup :
          afterPickup.statics = s.statics := by
        dsimp [afterPickup]
        exact runPlan_statics initialActions s

      have hlengthAfterPickup :
          afterPickup.statics.objects.length =
            s.statics.objects.length :=
        congrArg
          (fun st : StaticState => st.objects.length)
          hstaticsAfterPickup

      have hfuel :
          gpObstacleCount afterPickup gold <
            s.statics.objects.length + 1 := by
        calc
          gpObstacleCount afterPickup gold ≤
              afterPickup.statics.objects.length :=
            gpObstacleCount_le_objects_length afterPickup gold
          _ = s.statics.objects.length :=
            hlengthAfterPickup
          _ < s.statics.objects.length + 1 :=
            Nat.lt_succ_self _

      have hloop :=
        gpLaserLoop_correct
          bomb
          gold
          (s.statics.objects.length + 1)
          afterPickup
          hstart.2
          hfuel

      have hcombined :
          ValidPlan
              (initialActions ++
                gpLaserLoop
                  bomb
                  gold
                  (s.statics.objects.length + 1)
                  afterPickup)
              s ∧
          (runPlan
              (initialActions ++
                gpLaserLoop
                  bomb
                  gold
                  (s.statics.objects.length + 1)
                  afterPickup)
              s).dynamic.holds_gold_p = true := by
        constructor
        · exact
            (validPlan_append
              initialActions
              (gpLaserLoop
                bomb
                gold
                (s.statics.objects.length + 1)
                afterPickup)
              s).2
              ⟨hstart.1, hloop.1⟩
        · rw [runPlan_append]
          exact hloop.2

      cases hsoft : s.dynamic.soft_rock_at_p gold with
      | true =>
          cases hneighborFind :
              gpFindReachableNeighbor s robot gold with
          | some result =>
              rcases result with ⟨neighbor, neighborPath⟩

              rcases
                  gpFindReachableNeighbor_sound
                    s
                    hwf
                    hrobot
                    hneighborFind with
                ⟨_hneighborMem, hneighborClear,
                 hneighborGold, hneighborPathCorrect⟩

              have hreachNeighbor :
                  GPClearReachable s robot neighbor :=
                gpClearPath_reachable hneighborPathCorrect

              have hfinish :=
                gpBombFinishPlan_correct
                  (s := s)
                  (robot := robot)
                  (bomb := bomb)
                  (gold := gold)
                  (neighbor := neighbor)
                  hwf
                  hrobot
                  harmEmpty
                  hbomb
                  hgold
                  hsoft
                  hneighborClear
                  hneighborGold
                  hreachBomb
                  hreachNeighbor

              simpa [
                solve,
                hfindRobot,
                hfindBomb,
                hfindGold,
                hpathFind,
                hsoft,
                hneighborFind
              ] using hfinish

          | none =>
              simpa [
                solve,
                hfindRobot,
                hfindBomb,
                hfindGold,
                hpathFind,
                hsoft,
                hneighborFind,
                hfindPathToBomb,
                initialActions,
                afterPickup
              ] using hcombined

      | false =>
          simpa [
            solve,
            hfindRobot,
            hfindBomb,
            hfindGold,
            hpathFind,
            hsoft,
            hfindPathToBomb,
            initialActions,
            afterPickup
          ] using hcombined

/--
Core planner correctness for the canonical goal that only requires holding
the gold.
-/
lemma solve_achieves_gold
    (s : State)
    (hinit : WellFormedInit s) :
    ValidPlan (solve s { dynamic := {
      robot_at_p := fun _ => none
      laser_at_p := fun _ => none
      soft_rock_at_p := fun _ => none
      hard_rock_at_p := fun _ => none
      gold_at_p := fun _ => none
      arm_empty_p := none
      holds_bomb_p := none
      holds_laser_p := none
      holds_gold_p := some true
      clear_p := fun _ => none
    } }) s ∧
    (runPlan
      (solve s { dynamic := {
        robot_at_p := fun _ => none
        laser_at_p := fun _ => none
        soft_rock_at_p := fun _ => none
        hard_rock_at_p := fun _ => none
        gold_at_p := fun _ => none
        arm_empty_p := none
        holds_bomb_p := none
        holds_laser_p := none
        holds_gold_p := some true
        clear_p := fun _ => none
      } })
      s).dynamic.holds_gold_p = true := by
  exact solve_achieves_gold_for_goal s _ hinit

theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  have hachieves :=
    solve_achieves_gold_for_goal s g hinit

  rcases hgoal with
    ⟨_hgoalStatic,
     _hValidRobot, _hValidLaser, _hValidSoft,
     _hValidHard, _hValidGold, _hValidClear,
     _hRobotUnique, _hLaserUnique, _hGoldUnique,
     _hClearNoRock, _hRockExclusive,
     _hRobotClear, _hHeldUnique,
     hIgnoreRobot, hIgnoreLaser, hIgnoreSoft,
     hIgnoreHard, hIgnoreGold, hIgnoreArm,
     hIgnoreBomb, hIgnoreHeldLaser,
     hIgnoreClear, hRequiresGold⟩

  unfold GoalIgnoreRobotAt at hIgnoreRobot
  unfold GoalIgnoreLaserAt at hIgnoreLaser
  unfold GoalIgnoreSoftRockAt at hIgnoreSoft
  unfold GoalIgnoreHardRockAt at hIgnoreHard
  unfold GoalIgnoreGoldAt at hIgnoreGold
  unfold GoalIgnoreArmEmpty at hIgnoreArm
  unfold GoalIgnoreHoldsBomb at hIgnoreBomb
  unfold GoalIgnoreHoldsLaser at hIgnoreHeldLaser
  unfold GoalIgnoreClear at hIgnoreClear
  unfold GoalHoldsGoldRequired at hRequiresGold

  refine ⟨hachieves.1, ?_⟩
  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [hIgnoreRobot x]
  · intro x
    simp [hIgnoreLaser x]
  · intro x
    simp [hIgnoreSoft x]
  · intro x
    simp [hIgnoreHard x]
  · intro x
    simp [hIgnoreGold x]
  · simp [hIgnoreArm]
  · simp [hIgnoreBomb]
  · simp [hIgnoreHeldLaser]
  · simpa [hRequiresGold] using hachieves.2
  · intro x
    simp [hIgnoreClear x]

/-!
## Reduction of a well-formed goal to `holds_gold_p`
-/

/--
A `WellFormedGoal` ignores every fluent except `holds_gold_p`, which it
requires to be true. Consequently, any state holding the gold satisfies
the goal.
-/
lemma satisfiesGoal_of_wellFormedGoal
    (initial final : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (hholdsGold : final.dynamic.holds_gold_p = true) :
    SatisfiesGoal final g := by
  rcases hgoal with
    ⟨_hstatic,
     _hVR, _hVL, _hVS, _hVH, _hVG, _hVC,
     _hR1, _hL1, _hG1, _hClear, _hSH, _hRC, _hHeld,
     hIgnoreRobot,
     hIgnoreLaser,
     hIgnoreSoft,
     hIgnoreHard,
     hIgnoreGold,
     hIgnoreArm,
     hIgnoreBomb,
     hIgnoreHeldLaser,
     hIgnoreClear,
     hRequiredGold⟩

  unfold GoalIgnoreRobotAt at hIgnoreRobot
  unfold GoalIgnoreLaserAt at hIgnoreLaser
  unfold GoalIgnoreSoftRockAt at hIgnoreSoft
  unfold GoalIgnoreHardRockAt at hIgnoreHard
  unfold GoalIgnoreGoldAt at hIgnoreGold
  unfold GoalIgnoreArmEmpty at hIgnoreArm
  unfold GoalIgnoreHoldsBomb at hIgnoreBomb
  unfold GoalIgnoreHoldsLaser at hIgnoreHeldLaser
  unfold GoalIgnoreClear at hIgnoreClear
  unfold GoalHoldsGoldRequired at hRequiredGold

  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [hIgnoreRobot x]
  · intro x
    simp [hIgnoreLaser x]
  · intro x
    simp [hIgnoreSoft x]
  · intro x
    simp [hIgnoreHard x]
  · intro x
    simp [hIgnoreGold x]
  · simp [hIgnoreArm]
  · simp [hIgnoreBomb]
  · simp [hIgnoreHeldLaser]
  · rw [hRequiredGold]
    exact hholdsGold
  · intro x
    simp [hIgnoreClear x]

/-!
## Main correctness theorem
-/

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

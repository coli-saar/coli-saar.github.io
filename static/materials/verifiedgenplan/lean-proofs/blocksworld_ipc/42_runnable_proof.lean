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

structure DynamicStateGen (α : Type) where
  clear_p : Obj → α
  on_table_p : Obj → α
  arm_empty_p : α
  holding_p : Obj → α
  on_p : Obj → Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def MinNumObj (s : StaticState) : Prop :=
  ∃ o, o ∈ s.objects

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  MinNumObj s

def ValidClearParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.clear_p var_x) → var_x ∈ s.objects

def ValidOnTableParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.on_table_p var_x) → var_x ∈ s.objects

def ValidHoldingParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x, Truthy.isTrue (d.holding_p var_x) → var_x ∈ s.objects

def ValidOnParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x var_y, Truthy.isTrue (d.on_p var_x var_y) → var_x ∈ s.objects ∧ var_y ∈ s.objects

def OnUniqueBelow {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y1 y2, Truthy.isTrue (d.on_p x y1) → Truthy.isTrue (d.on_p x y2) → y1 = y2

def OnUniqueAbove {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x1 x2 y, Truthy.isTrue (d.on_p x1 y) → Truthy.isTrue (d.on_p x2 y) → x1 = x2

def NoOnCycles {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, ¬ Relation.TransGen (fun a b => Truthy.isTrue (d.on_p a b)) x x

def BlockLocXor {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects →
    ¬ ((∃ y, Truthy.isTrue (d.on_p x y)) ∧ Truthy.isTrue (d.on_table_p x)) ∧
    ¬ ((∃ y, Truthy.isTrue (d.on_p x y)) ∧ Truthy.isTrue (d.holding_p x)) ∧
    ¬ (Truthy.isTrue (d.on_table_p x) ∧ Truthy.isTrue (d.holding_p x))

def ClearConsistency {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects →
    (Truthy.isTrue (d.clear_p x) → ¬ ∃ y, Truthy.isTrue (d.on_p y x)) ∧
    ((∃ y, Truthy.isTrue (d.on_p y x)) → ¬ Truthy.isTrue (d.clear_p x))

def HeldClearXor {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects → ¬ (Truthy.isTrue (d.holding_p x) ∧ Truthy.isTrue (d.clear_p x))

def ArmEmptyIffNoneHeld {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  (Truthy.isTrue d.arm_empty_p → ¬ ∃ x, Truthy.isTrue (d.holding_p x)) ∧
  ((∃ x, Truthy.isTrue (d.holding_p x)) → ¬ Truthy.isTrue d.arm_empty_p)

def HoldingCapacity {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x1 x2, Truthy.isTrue (d.holding_p x1) → Truthy.isTrue (d.holding_p x2) → x1 = x2

def BlockHasLocation (s : State) : Prop :=
  ∀ x, x ∈ s.statics.objects →
    (∃ y, s.dynamic.on_p x y = true) ∨ s.dynamic.on_table_p x = true ∨ s.dynamic.holding_p x = true

def NoBlockOnTopImpliesClear (s : State) : Prop :=
  ∀ x, x ∈ s.statics.objects →
    (¬ ∃ y, s.dynamic.on_p y x = true) → s.dynamic.clear_p x = true ∨ s.dynamic.holding_p x = true

def StackGroundedOnTable (s : State) : Prop :=
  ∀ x, x ∈ s.statics.objects → s.dynamic.holding_p x = false →
    ∃ y, Relation.ReflTransGen (fun a b => s.dynamic.on_p a b = true) x y ∧
         s.dynamic.on_table_p y = true

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidClearParam s.statics s.dynamic ∧
  ValidOnTableParam s.statics s.dynamic ∧
  ValidHoldingParam s.statics s.dynamic ∧
  ValidOnParam s.statics s.dynamic ∧
  OnUniqueBelow s.statics s.dynamic ∧
  OnUniqueAbove s.statics s.dynamic ∧
  NoOnCycles s.statics s.dynamic ∧
  BlockLocXor s.statics s.dynamic ∧
  ClearConsistency s.statics s.dynamic ∧
  HeldClearXor s.statics s.dynamic ∧
  ArmEmptyIffNoneHeld s.statics s.dynamic ∧
  HoldingCapacity s.statics s.dynamic ∧
  BlockHasLocation s ∧
  NoBlockOnTopImpliesClear s ∧
  StackGroundedOnTable s

def InitArmEmpty (s : State) : Prop :=
  s.dynamic.arm_empty_p = true

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitArmEmpty s

def GoalIgnoreClear (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.clear_p x = none

def GoalIgnoreOnTable (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.on_table_p x = none

def GoalIgnoreArmEmpty (initial : State) (g : Goal) : Prop :=
  g.dynamic.arm_empty_p = none

def GoalIgnoreHolding (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.holding_p x = none

def GoalOnOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ x y, g.dynamic.on_p x y ≠ some false

def GoalHasOnTarget (initial : State) (g : Goal) : Prop :=
  ∃ x y, g.dynamic.on_p x y = some true

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidClearParam initial.statics g.dynamic ∧
  ValidOnTableParam initial.statics g.dynamic ∧
  ValidHoldingParam initial.statics g.dynamic ∧
  ValidOnParam initial.statics g.dynamic ∧
  OnUniqueBelow initial.statics g.dynamic ∧
  OnUniqueAbove initial.statics g.dynamic ∧
  NoOnCycles initial.statics g.dynamic ∧
  BlockLocXor initial.statics g.dynamic ∧
  ClearConsistency initial.statics g.dynamic ∧
  HeldClearXor initial.statics g.dynamic ∧
  ArmEmptyIffNoneHeld initial.statics g.dynamic ∧
  HoldingCapacity initial.statics g.dynamic ∧
  GoalIgnoreClear initial g ∧
  GoalIgnoreOnTable initial g ∧
  GoalIgnoreArmEmpty initial g ∧
  GoalIgnoreHolding initial g ∧
  GoalOnOnlyPositive initial g ∧
  GoalHasOnTarget initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_x,
    match g.dynamic.clear_p var_x with
    | none => True
    | some b => s.dynamic.clear_p var_x = b) ∧
  (∀ var_x,
    match g.dynamic.on_table_p var_x with
    | none => True
    | some b => s.dynamic.on_table_p var_x = b) ∧
  (match g.dynamic.arm_empty_p with
  | none => True
  | some b => s.dynamic.arm_empty_p = b) ∧
  (∀ var_x,
    match g.dynamic.holding_p var_x with
    | none => True
    | some b => s.dynamic.holding_p var_x = b) ∧
  (∀ var_x var_y,
    match g.dynamic.on_p var_x var_y with
    | none => True
    | some b => s.dynamic.on_p var_x var_y = b)

def pickupPre (var_ob : Obj) (s : State) : Prop :=
  var_ob ∈ s.statics.objects ∧
  s.dynamic.clear_p var_ob = true ∧
  s.dynamic.on_table_p var_ob = true ∧
  s.dynamic.arm_empty_p = true

def putdownPre (var_ob : Obj) (s : State) : Prop :=
  var_ob ∈ s.statics.objects ∧
  s.dynamic.holding_p var_ob = true

def stackPre (var_ob : Obj) (var_underob : Obj) (s : State) : Prop :=
  var_ob ∈ s.statics.objects ∧
  var_underob ∈ s.statics.objects ∧
  s.dynamic.clear_p var_underob = true ∧
  s.dynamic.holding_p var_ob = true

def unstackPre (var_ob : Obj) (var_underob : Obj) (s : State) : Prop :=
  var_ob ∈ s.statics.objects ∧
  var_underob ∈ s.statics.objects ∧
  s.dynamic.on_p var_ob var_underob = true ∧
  s.dynamic.clear_p var_ob = true ∧
  s.dynamic.arm_empty_p = true

def pickup (var_ob : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    clear_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          false
        else
          s.dynamic.clear_p var_ob',
    on_table_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          false
        else
          s.dynamic.on_table_p var_ob',
    arm_empty_p := false,
    holding_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          true
        else
          s.dynamic.holding_p var_ob'
  }
}

def putdown (var_ob : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    clear_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          true
        else
          s.dynamic.clear_p var_ob',
    on_table_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          true
        else
          s.dynamic.on_table_p var_ob',
    arm_empty_p := true,
    holding_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          false
        else
          s.dynamic.holding_p var_ob'
  }
}

def stack (var_ob : Obj) (var_underob : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    clear_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          true
        else if var_ob' = var_underob then
          false
        else
          s.dynamic.clear_p var_ob',
    arm_empty_p := true,
    holding_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          false
        else
          s.dynamic.holding_p var_ob',
    on_p :=
      fun var_ob' var_underob' =>
        if var_ob' = var_ob ∧ var_underob' = var_underob then
          true
        else
          s.dynamic.on_p var_ob' var_underob'
  }
}

def unstack (var_ob : Obj) (var_underob : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    clear_p :=
      fun var_underob' =>
        if var_underob' = var_underob then
          true
        else if var_underob' = var_ob then
          false
        else
          s.dynamic.clear_p var_underob',
    arm_empty_p := false,
    holding_p :=
      fun var_ob' =>
        if var_ob' = var_ob then
          true
        else
          s.dynamic.holding_p var_ob',
    on_p :=
      fun var_ob' var_underob' =>
        if var_ob' = var_ob ∧ var_underob' = var_underob then
          false
        else
          s.dynamic.on_p var_ob' var_underob'
  }
}

inductive PlanAction where
  | pickup  (var_ob : Obj)
  | putdown (var_ob : Obj)
  | stack   (var_ob : Obj) (var_underob : Obj)
  | unstack (var_ob : Obj) (var_underob : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .pickup  var_ob            , s => pickupPre var_ob s
  | .putdown var_ob            , s => putdownPre var_ob s
  | .stack   var_ob var_underob, s => stackPre var_ob var_underob s
  | .unstack var_ob var_underob, s => unstackPre var_ob var_underob s

def actionApply : PlanAction → State → State
  | .pickup  var_ob            , s => pickup var_ob s
  | .putdown var_ob            , s => putdown var_ob s
  | .stack   var_ob var_underob, s => stack var_ob var_underob s
  | .unstack var_ob var_underob, s => unstack var_ob var_underob s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def gpFindCurrentSupport (b : Obj) (s : State) : List Obj → Option Obj
  | [] => none
  | a :: rest =>
      if s.dynamic.on_p b a = true then
        some a
      else
        gpFindCurrentSupport b s rest

def gpFindUnstackCandidate (s : State) :
    List Obj → Option (Obj × Obj)
  | [] => none
  | b :: rest =>
      if s.dynamic.clear_p b = true ∧
         s.dynamic.on_table_p b = false then
        match gpFindCurrentSupport b s s.statics.objects with
        | some a => some (b, a)
        | none => gpFindUnstackCandidate s rest
      else
        gpFindUnstackCandidate s rest

def gpClearToTableAux : List Obj → State → List PlanAction
  | [], _ => []
  | _ :: fuel, s =>
      match gpFindUnstackCandidate s s.statics.objects with
      | none => []
      | some (b, a) =>
          let nextState := putdown b (unstack b a s)
          PlanAction.unstack b a ::
          PlanAction.putdown b ::
          gpClearToTableAux fuel nextState

def gpFindGoalSupport (b : Obj) (g : Goal) :
    List Obj → Option Obj
  | [] => none
  | a :: rest =>
      if g.dynamic.on_p b a = some true then
        some a
      else
        gpFindGoalSupport b g rest

def gpCollectGoalRoots (g : Goal) (allObjects : List Obj) :
    List Obj → List Obj
  | [] => []
  | b :: rest =>
      match gpFindGoalSupport b g allObjects with
      | none =>
          b :: gpCollectGoalRoots g allObjects rest
      | some _ =>
          gpCollectGoalRoots g allObjects rest

def gpFindBuildCandidate
    (g : Goal)
    (allObjects : List Obj)
    (processed : List Obj) :
    List Obj → Option (Obj × Obj)
  | [] => none
  | b :: rest =>
      if b ∈ processed then
        gpFindBuildCandidate g allObjects processed rest
      else
        match gpFindGoalSupport b g allObjects with
        | none =>
            gpFindBuildCandidate g allObjects processed rest
        | some a =>
            if a ∈ processed then
              some (b, a)
            else
              gpFindBuildCandidate g allObjects processed rest

def gpBuildGoalAux (allObjects : List Obj) (g : Goal) :
    List Obj → List Obj → List PlanAction
  | [], _ => []
  | _ :: fuel, processed =>
      match gpFindBuildCandidate g allObjects processed allObjects with
      | none => []
      | some (b, a) =>
          PlanAction.pickup b ::
          PlanAction.stack b a ::
          gpBuildGoalAux allObjects g fuel (b :: processed)

def solve (s : State) (g : Goal) : List PlanAction :=
  let objects := s.statics.objects
  let clearPlan := gpClearToTableAux objects s
  let goalRoots := gpCollectGoalRoots g objects objects
  let buildPlan := gpBuildGoalAux objects g objects goalRoots
  clearPlan ++ buildPlan

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

lemma pickup_statics (var_ob : Obj) (s : State) :
    (pickup var_ob s).statics = s.statics := rfl

lemma putdown_statics (var_ob : Obj) (s : State) :
    (putdown var_ob s).statics = s.statics := rfl

lemma stack_statics (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).statics = s.statics := rfl

lemma unstack_statics (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | pickup var_ob              => exact pickup_statics var_ob s
      | putdown var_ob             => exact putdown_statics var_ob s
      | stack var_ob var_underob   => exact stack_statics var_ob var_underob s
      | unstack var_ob var_underob => exact unstack_statics var_ob var_underob s

-- pickup only touches holding_p, clear_p, on_table_p
lemma pickup_clear_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (pickup var_ob s).dynamic.clear_p var_ob' = s.dynamic.clear_p var_ob' := by
  unfold pickup
  simp [h1]

lemma pickup_on_table_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (pickup var_ob s).dynamic.on_table_p var_ob' = s.dynamic.on_table_p var_ob' := by
  unfold pickup
  simp [h1]

lemma pickup_holding_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (pickup var_ob s).dynamic.holding_p var_ob' = s.dynamic.holding_p var_ob' := by
  unfold pickup
  simp [h1]

-- pickup never touches on_p
lemma pickup_on_p (var_ob : Obj) (s : State) :
    (pickup var_ob s).dynamic.on_p = s.dynamic.on_p := rfl

-- putdown only touches clear_p, on_table_p, holding_p
lemma putdown_clear_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (putdown var_ob s).dynamic.clear_p var_ob' = s.dynamic.clear_p var_ob' := by
  unfold putdown
  simp [h1]

lemma putdown_on_table_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (putdown var_ob s).dynamic.on_table_p var_ob' = s.dynamic.on_table_p var_ob' := by
  unfold putdown
  simp [h1]

lemma putdown_holding_p_ne (var_ob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (putdown var_ob s).dynamic.holding_p var_ob' = s.dynamic.holding_p var_ob' := by
  unfold putdown
  simp [h1]

-- putdown never touches on_p
lemma putdown_on_p (var_ob : Obj) (s : State) :
    (putdown var_ob s).dynamic.on_p = s.dynamic.on_p := rfl

-- stack only touches clear_p, on_p, holding_p
lemma stack_clear_p_ne (var_ob var_underob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) (h2 : var_ob' ≠ var_underob) :
    (stack var_ob var_underob s).dynamic.clear_p var_ob' = s.dynamic.clear_p var_ob' := by
  unfold stack
  simp [h1, h2]

lemma stack_holding_p_ne (var_ob var_underob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (stack var_ob var_underob s).dynamic.holding_p var_ob' = s.dynamic.holding_p var_ob' := by
  unfold stack
  simp [h1]

lemma stack_on_p_ne (var_ob var_underob : Obj) (s : State) {var_ob' var_underob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (stack var_ob var_underob s).dynamic.on_p var_ob' var_underob' = s.dynamic.on_p var_ob' var_underob' := by
  unfold stack
  simp [h1]

lemma stack_on_p_ne_var_y (var_ob var_underob : Obj) (s : State) {var_underob' : Obj} (h1 : var_underob' ≠ var_underob) :
    (stack var_ob var_underob s).dynamic.on_p var_ob var_underob' = s.dynamic.on_p var_ob var_underob' := by
  unfold stack
  simp [h1]

-- stack never touches on_table_p
lemma stack_on_table_p (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).dynamic.on_table_p = s.dynamic.on_table_p := rfl

-- unstack only touches holding_p, clear_p, on_p
lemma unstack_clear_p_ne (var_ob var_underob : Obj) (s : State) {var_underob' : Obj} (h1 : var_underob' ≠ var_underob) (h2 : var_underob' ≠ var_ob) :
    (unstack var_ob var_underob s).dynamic.clear_p var_underob' = s.dynamic.clear_p var_underob' := by
  unfold unstack
  simp [h1, h2]

lemma unstack_holding_p_ne (var_ob var_underob : Obj) (s : State) {var_ob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (unstack var_ob var_underob s).dynamic.holding_p var_ob' = s.dynamic.holding_p var_ob' := by
  unfold unstack
  simp [h1]

lemma unstack_on_p_ne (var_ob var_underob : Obj) (s : State) {var_ob' var_underob' : Obj} (h1 : var_ob' ≠ var_ob) :
    (unstack var_ob var_underob s).dynamic.on_p var_ob' var_underob' = s.dynamic.on_p var_ob' var_underob' := by
  unfold unstack
  simp [h1]

lemma unstack_on_p_ne_var_y (var_ob var_underob : Obj) (s : State) {var_underob' : Obj} (h1 : var_underob' ≠ var_underob) :
    (unstack var_ob var_underob s).dynamic.on_p var_ob var_underob' = s.dynamic.on_p var_ob var_underob' := by
  unfold unstack
  simp [h1]

-- unstack never touches on_table_p
lemma unstack_on_table_p (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).dynamic.on_table_p = s.dynamic.on_table_p := rfl

lemma pickup_clear_p_eq1 (var_ob : Obj) (s : State) :
    (pickup var_ob s).dynamic.clear_p var_ob = false := by
  unfold pickup
  simp

lemma pickup_on_table_p_eq1 (var_ob : Obj) (s : State) :
    (pickup var_ob s).dynamic.on_table_p var_ob = false := by
  unfold pickup
  simp

lemma pickup_arm_empty_p (var_ob : Obj) (s : State) :
    (pickup var_ob s).dynamic.arm_empty_p = false := by
  unfold pickup
  simp

lemma pickup_holding_p_eq1 (var_ob : Obj) (s : State) :
    (pickup var_ob s).dynamic.holding_p var_ob = true := by
  unfold pickup
  simp

lemma putdown_clear_p_eq1 (var_ob : Obj) (s : State) :
    (putdown var_ob s).dynamic.clear_p var_ob = true := by
  unfold putdown
  simp

lemma putdown_on_table_p_eq1 (var_ob : Obj) (s : State) :
    (putdown var_ob s).dynamic.on_table_p var_ob = true := by
  unfold putdown
  simp

lemma putdown_arm_empty_p (var_ob : Obj) (s : State) :
    (putdown var_ob s).dynamic.arm_empty_p = true := by
  unfold putdown
  simp

lemma putdown_holding_p_eq1 (var_ob : Obj) (s : State) :
    (putdown var_ob s).dynamic.holding_p var_ob = false := by
  unfold putdown
  simp

lemma stack_clear_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).dynamic.clear_p var_ob = true := by
  unfold stack
  simp

lemma stack_clear_p_eq2 (var_ob var_underob : Obj) (s : State) (h1 : var_underob ≠ var_ob) :
    (stack var_ob var_underob s).dynamic.clear_p var_underob = false := by
  unfold stack
  simp [h1]

lemma stack_arm_empty_p (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).dynamic.arm_empty_p = true := by
  unfold stack
  simp

lemma stack_holding_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).dynamic.holding_p var_ob = false := by
  unfold stack
  simp

lemma stack_on_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (stack var_ob var_underob s).dynamic.on_p var_ob var_underob = true := by
  unfold stack
  simp

lemma unstack_clear_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).dynamic.clear_p var_underob = true := by
  unfold unstack
  simp

lemma unstack_clear_p_eq2 (var_ob var_underob : Obj) (s : State) (h1 : var_ob ≠ var_underob) :
    (unstack var_ob var_underob s).dynamic.clear_p var_ob = false := by
  unfold unstack
  simp [h1]

lemma unstack_arm_empty_p (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).dynamic.arm_empty_p = false := by
  unfold unstack
  simp

lemma unstack_holding_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).dynamic.holding_p var_ob = true := by
  unfold unstack
  simp

lemma unstack_on_p_eq1 (var_ob var_underob : Obj) (s : State) :
    (unstack var_ob var_underob s).dynamic.on_p var_ob var_underob = false := by
  unfold unstack
  simp

@[simp] lemma truthy_isTrue_bool_iff (b : Bool) :
    Truthy.isTrue b ↔ b = true := by
  rfl

-- Some small generic lemmas about transitive closures.

lemma tg_to_rt {α : Type} {r : α → α → Prop} {a b : α}
    (h : Relation.TransGen r a b) :
    Relation.ReflTransGen r a b := by
  induction h with
  | single hab =>
      exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl hab
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.tail ih hbc

lemma rt_trans {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : Relation.ReflTransGen r a b)
    (hbc : Relation.ReflTransGen r b c) :
    Relation.ReflTransGen r a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hcd ih =>
      exact Relation.ReflTransGen.tail ih hcd

lemma transGen_mono {α : Type} {r q : α → α → Prop} {a b : α}
    (hmono : ∀ x y, r x y → q x y)
    (h : Relation.TransGen r a b) :
    Relation.TransGen q a b := by
  induction h with
  | single hab =>
      exact Relation.TransGen.single (hmono _ _ hab)
  | tail _ hbc ih =>
      exact Relation.TransGen.tail ih (hmono _ _ hbc)

lemma rt_mono {α : Type} {r q : α → α → Prop} {a b : α}
    (hmono : ∀ x y, r x y → q x y)
    (h : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen q a b := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.tail ih (hmono _ _ hbc)

lemma rt_after_first
    {α : Type} {r : α → α → Prop} {x y z : α}
    (hfun : ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂)
    (hxy : r x y)
    (hpath : Relation.ReflTransGen r x z) :
    z = x ∨ Relation.ReflTransGen r y z := by
  induction hpath with
  | refl =>
      exact Or.inl rfl
  | @tail b c _ hbc ih =>
      rcases ih with hb | ih
      · subst b
        have hcy : c = y := hfun x c y hbc hxy
        subst c
        exact Or.inr Relation.ReflTransGen.refl
      · exact Or.inr (Relation.ReflTransGen.tail ih hbc)

lemma rt_eq_of_no_out
    {α : Type} {r : α → α → Prop} {x z : α}
    (hout : ∀ y, ¬ r x y)
    (hpath : Relation.ReflTransGen r x z) :
    z = x := by
  induction hpath with
  | refl =>
      rfl
  | @tail b c _ hbc ih =>
      subst b
      exact False.elim (hout c hbc)

lemma rt_not_of_no_in
    {α : Type} {r : α → α → Prop} {a b : α}
    (hne : a ≠ b)
    (hin : ∀ x, ¬ r x b) :
    ¬ Relation.ReflTransGen r a b := by
  intro h
  cases h with
  | refl =>
      exact hne rfl
  | tail _ hlast =>
      exact hin _ hlast

lemma rt_map_avoiding
    {α : Type} {r q : α → α → Prop} {u x z : α}
    (hx : x ≠ u)
    (hin : ∀ a, ¬ r a u)
    (hmap : ∀ a b, a ≠ u → r a b → q a b)
    (hpath : Relation.ReflTransGen r x z) :
    Relation.ReflTransGen q x z ∧ z ≠ u := by
  induction hpath with
  | refl =>
      exact ⟨Relation.ReflTransGen.refl, hx⟩
  | @tail b c _ hbc ih =>
      rcases ih with ⟨ihpath, hb⟩
      have hc : c ≠ u := by
        intro hcu
        subst c
        exact hin b hbc
      exact ⟨Relation.ReflTransGen.tail ihpath (hmap b c hb hbc), hc⟩

lemma transGen_add_edge_decomp
    {α : Type} {r : α → α → Prop} {u v a b : α}
    (hvu : ¬ Relation.ReflTransGen r v u)
    (h :
      Relation.TransGen
        (fun x y => r x y ∨ (x = u ∧ y = v)) a b) :
    Relation.TransGen r a b ∨
      (Relation.ReflTransGen r a u ∧
       Relation.ReflTransGen r v b) := by
  induction h with
  | single hab =>
      rcases hab with hab | ⟨rfl, rfl⟩
      · exact Or.inl (Relation.TransGen.single hab)
      · exact Or.inr
          ⟨Relation.ReflTransGen.refl,
           Relation.ReflTransGen.refl⟩
  | @tail c d _ hcd ih =>
      rcases ih with ih | ⟨hau, hvc⟩
      · rcases hcd with hcd | ⟨rfl, rfl⟩
        · exact Or.inl (Relation.TransGen.tail ih hcd)
        · exact Or.inr
            ⟨tg_to_rt ih, Relation.ReflTransGen.refl⟩
      · rcases hcd with hcd | ⟨rfl, rfl⟩
        · exact Or.inr
            ⟨hau, Relation.ReflTransGen.tail hvc hcd⟩
        · exact False.elim (hvu hvc)

-- A held block cannot have another block on top of it.
lemma wf_held_no_on_top
    (s : State)
    (hwf : WellFormed s)
    (x : Obj)
    (hh : s.dynamic.holding_p x = true) :
    ¬ ∃ y, s.dynamic.on_p y x = true := by
  rcases hwf with
    ⟨_, _, _, hvalidHolding, hvalidOn, hbelow, _, _, hloc, _, _, _,
      _, _, _, hground⟩
  have hxmem : x ∈ s.statics.objects :=
    hvalidHolding x hh
  have hxNoOut : ∀ z, ¬ s.dynamic.on_p x z = true := by
    intro z hxz
    exact (hloc x hxmem).2.1 ⟨⟨z, hxz⟩, hh⟩
  have hxNotTable : ¬ s.dynamic.on_table_p x = true := by
    intro htable
    exact (hloc x hxmem).2.2 ⟨htable, hh⟩
  rintro ⟨y, hyx⟩
  have hymem : y ∈ s.statics.objects :=
    (hvalidOn y x hyx).1
  have hyNotHeld : ¬ s.dynamic.holding_p y = true := by
    intro hyHeld
    exact (hloc y hymem).2.1 ⟨⟨x, hyx⟩, hyHeld⟩
  have hyHeldFalse : s.dynamic.holding_p y = false := by
    cases hy : s.dynamic.holding_p y with
    | false => rfl
    | true => exact False.elim (hyNotHeld hy)
  rcases hground y hymem hyHeldFalse with ⟨z, hyz, hzTable⟩
  rcases rt_after_first hbelow hyx hyz with hzy | hxz
  · subst z
    exact (hloc y hymem).1 ⟨⟨x, hyx⟩, hzTable⟩
  · have hzx : z = x := rt_eq_of_no_out hxNoOut hxz
    subst z
    exact hxNotTable hzTable

lemma pickup_preserves_wf
    (var_ob)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pickupPre var_ob s) :
    WellFormed (pickup var_ob s) := by
  rcases hwf with
    ⟨hstatic, hclear, htable, hholding, hon, hbelow, habove,
      hcycles, hloc, hclearCons, hheldClear, harm, hcapacity,
      hhasLoc, hnoTop, hground⟩
  rcases hpre with ⟨hobmem, hobClear, hobTable, harmEmpty⟩

  have hobNoOut : ¬ ∃ y, s.dynamic.on_p var_ob y = true := by
    intro h
    exact (hloc var_ob hobmem).1 ⟨h, hobTable⟩

  have hobNoIn : ∀ y, ¬ s.dynamic.on_p y var_ob = true := by
    intro y hy
    exact (hclearCons var_ob hobmem).1 hobClear ⟨y, hy⟩

  have holdOnlyOb :
      ∀ x, (pickup var_ob s).dynamic.holding_p x = true →
        x = var_ob := by
    intro x hx
    by_cases hxo : x = var_ob
    · exact hxo
    · have hxold : s.dynamic.holding_p x = true := by
        simpa [pickup, hxo] using hx
      exact False.elim ((harm.1 harmEmpty) ⟨x, hxold⟩)

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa [pickup] using hstatic
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup] at hx
    · have hxold : s.dynamic.clear_p x = true := by
        simpa [pickup, hxo] using hx
      simpa [pickup] using hclear x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup] at hx
    · have hxold : s.dynamic.on_table_p x = true := by
        simpa [pickup, hxo] using hx
      simpa [pickup] using htable x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simpa [pickup] using hobmem
    · have hxold : s.dynamic.holding_p x = true := by
        simpa [pickup, hxo] using hx
      simpa [pickup] using hholding x hxold
  · intro x y hxy
    have hxyold : s.dynamic.on_p x y = true := by
      simpa [pickup] using hxy
    simpa [pickup] using hon x y hxyold
  · intro x y₁ y₂ h₁ h₂
    apply hbelow x y₁ y₂
    · simpa [pickup] using h₁
    · simpa [pickup] using h₂
  · intro x₁ x₂ y h₁ h₂
    apply habove x₁ x₂ y
    · simpa [pickup] using h₁
    · simpa [pickup] using h₂
  · intro x hcycle
    apply hcycles x
    apply transGen_mono _ hcycle
    intro a b hab
    simpa [pickup] using hab
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup, hobNoOut]
    · simpa [pickup, hxo] using hloc x (by simpa [pickup] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup]
    · simpa [pickup, hxo] using
        hclearCons x (by simpa [pickup] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup]
    · simpa [pickup, hxo] using
        hheldClear x (by simpa [pickup] using hxmem)
  · simp [ArmEmptyIffNoneHeld, pickup]
  · intro x₁ x₂ hx₁ hx₂
    exact (holdOnlyOb x₁ hx₁).trans (holdOnlyOb x₂ hx₂).symm
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inr (Or.inr (by simp [pickup]))
    · simpa [pickup, hxo] using
        hhasLoc x (by simpa [pickup] using hxmem)
  · intro x hxmem hnone
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inr (by simp [pickup])
    · have hnoneOld : ¬ ∃ y, s.dynamic.on_p y x = true := by
        simpa [pickup] using hnone
      simpa [pickup, hxo] using
        hnoTop x (by simpa [pickup] using hxmem) hnoneOld
  · intro x hxmem hxNotHeld
    by_cases hxo : x = var_ob
    · subst x
      simp [pickup] at hxNotHeld
    · have hxOldNotHeld : s.dynamic.holding_p x = false := by
        simpa [pickup, hxo] using hxNotHeld
      rcases hground x (by simpa [pickup] using hxmem) hxOldNotHeld with
        ⟨y, hxy, hyTable⟩
      have hyne : y ≠ var_ob := by
        intro hy
        subst y
        exact (rt_not_of_no_in hxo hobNoIn) hxy
      exact ⟨y, by simpa [pickup] using hxy,
        by simpa [pickup, hyne] using hyTable⟩

lemma putdown_preserves_wf
    (var_ob)
    (s : State)
    (hwf : WellFormed s)
    (hpre : putdownPre var_ob s) :
    WellFormed (putdown var_ob s) := by
  have hwfCopy := hwf
  rcases hwf with
    ⟨hstatic, hclear, htable, hholding, hon, hbelow, habove,
      hcycles, hloc, hclearCons, hheldClear, harm, hcapacity,
      hhasLoc, hnoTop, hground⟩
  rcases hpre with ⟨hobmem, hobHeld⟩

  have hobNoTop : ¬ ∃ y, s.dynamic.on_p y var_ob = true :=
    wf_held_no_on_top s hwfCopy var_ob hobHeld

  have hobNoOut : ¬ ∃ y, s.dynamic.on_p var_ob y = true := by
    intro h
    exact (hloc var_ob hobmem).2.1 ⟨h, hobHeld⟩

  have noHeldAfter :
      ¬ ∃ x, (putdown var_ob s).dynamic.holding_p x = true := by
    rintro ⟨x, hx⟩
    by_cases hxo : x = var_ob
    · subst x
      simp [putdown] at hx
    · have hxOld : s.dynamic.holding_p x = true := by
        simpa [putdown, hxo] using hx
      have : x = var_ob := hcapacity x var_ob hxOld hobHeld
      exact hxo this

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa [putdown] using hstatic
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simpa [putdown] using hobmem
    · have hxold : s.dynamic.clear_p x = true := by
        simpa [putdown, hxo] using hx
      simpa [putdown] using hclear x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simpa [putdown] using hobmem
    · have hxold : s.dynamic.on_table_p x = true := by
        simpa [putdown, hxo] using hx
      simpa [putdown] using htable x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simp [putdown] at hx
    · have hxold : s.dynamic.holding_p x = true := by
        simpa [putdown, hxo] using hx
      simpa [putdown] using hholding x hxold
  · intro x y hxy
    have hxyold : s.dynamic.on_p x y = true := by
      simpa [putdown] using hxy
    simpa [putdown] using hon x y hxyold
  · intro x y₁ y₂ h₁ h₂
    apply hbelow x y₁ y₂
    · simpa [putdown] using h₁
    · simpa [putdown] using h₂
  · intro x₁ x₂ y h₁ h₂
    apply habove x₁ x₂ y
    · simpa [putdown] using h₁
    · simpa [putdown] using h₂
  · intro x hcycle
    apply hcycles x
    apply transGen_mono _ hcycle
    intro a b hab
    simpa [putdown] using hab
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [putdown, hobNoOut]
    · simpa [putdown, hxo] using
        hloc x (by simpa [putdown] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [putdown, hobNoTop]
    · simpa [putdown, hxo] using
        hclearCons x (by simpa [putdown] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [putdown]
    · simpa [putdown, hxo] using
        hheldClear x (by simpa [putdown] using hxmem)
  · constructor
    · intro _
      exact noHeldAfter
    · intro hex
      exact False.elim (noHeldAfter hex)
  · intro x₁ x₂ hx₁ hx₂
    by_cases h₁ : x₁ = var_ob
    · subst x₁
      simp [putdown] at hx₁
    · by_cases h₂ : x₂ = var_ob
      · subst x₂
        simp [putdown] at hx₂
      · exact hcapacity x₁ x₂
          (by simpa [putdown, h₁] using hx₁)
          (by simpa [putdown, h₂] using hx₂)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inr (Or.inl (by simp [putdown]))
    · simpa [putdown, hxo] using
        hhasLoc x (by simpa [putdown] using hxmem)
  · intro x hxmem hnone
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inl (by simp [putdown])
    · have hnoneOld : ¬ ∃ y, s.dynamic.on_p y x = true := by
        simpa [putdown] using hnone
      simpa [putdown, hxo] using
        hnoTop x (by simpa [putdown] using hxmem) hnoneOld
  · intro x hxmem hxNotHeld
    by_cases hxo : x = var_ob
    · subst x
      exact ⟨var_ob, Relation.ReflTransGen.refl,
        by simp [putdown]⟩
    · have hxOldNotHeld : s.dynamic.holding_p x = false := by
        simpa [putdown, hxo] using hxNotHeld
      rcases hground x (by simpa [putdown] using hxmem) hxOldNotHeld with
        ⟨y, hxy, hyTable⟩
      refine ⟨y, by simpa [putdown] using hxy, ?_⟩
      by_cases hyo : y = var_ob
      · subst y
        simp [putdown]
      · simpa [putdown, hyo] using hyTable

lemma stack_preserves_wf
    (var_ob var_underob)
    (s : State)
    (hwf : WellFormed s)
    (hpre : stackPre var_ob var_underob s) :
    WellFormed (stack var_ob var_underob s) := by
  have hwfCopy := hwf
  rcases hwf with
    ⟨hstatic, hclear, htable, hholding, hon, hbelow, habove,
      hcycles, hloc, hclearCons, hheldClear, harm, hcapacity,
      hhasLoc, hnoTop, hground⟩
  rcases hpre with
    ⟨hobmem, hundmem, hundClear, hobHeld⟩

  have hne : var_ob ≠ var_underob := by
    intro heq
    subst var_underob
    exact (hheldClear var_ob hobmem) ⟨hobHeld, hundClear⟩

  have hobNoOut : ∀ y, ¬ s.dynamic.on_p var_ob y = true := by
    intro y hy
    exact (hloc var_ob hobmem).2.1 ⟨⟨y, hy⟩, hobHeld⟩

  have hobNotTable : ¬ s.dynamic.on_table_p var_ob = true := by
    intro ht
    exact (hloc var_ob hobmem).2.2 ⟨ht, hobHeld⟩

  have hundNoTop : ∀ y, ¬ s.dynamic.on_p y var_underob = true := by
    intro y hy
    exact (hclearCons var_underob hundmem).1 hundClear ⟨y, hy⟩

  have hobNoTop : ∀ y, ¬ s.dynamic.on_p y var_ob = true := by
    intro y hy
    exact wf_held_no_on_top s hwfCopy var_ob hobHeld ⟨y, hy⟩

  have hundNotHeld : s.dynamic.holding_p var_underob = false := by
    cases h : s.dynamic.holding_p var_underob with
    | false => rfl
    | true =>
        exact False.elim
          ((hheldClear var_underob hundmem) ⟨h, hundClear⟩)

  have noHeldAfter :
      ¬ ∃ x, (stack var_ob var_underob s).dynamic.holding_p x = true := by
    rintro ⟨x, hx⟩
    by_cases hxo : x = var_ob
    · subst x
      simp [stack] at hx
    · have hxOld : s.dynamic.holding_p x = true := by
        simpa [stack, hxo] using hx
      exact hxo (hcapacity x var_ob hxOld hobHeld)

  have oldToNew :
      ∀ a b, s.dynamic.on_p a b = true →
        (stack var_ob var_underob s).dynamic.on_p a b = true := by
    intro a b hab
    by_cases hp : a = var_ob ∧ b = var_underob
    · simp [stack, hp]
    · simpa [stack, hp] using hab

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa [stack] using hstatic
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simpa [stack] using hobmem
    · by_cases hxu : x = var_underob
      · subst x
        simp [stack, hne, Ne.symm hne] at hx
      · have hxold : s.dynamic.clear_p x = true := by
          simpa [stack, hxo, hxu] using hx
        simpa [stack] using hclear x hxold
  · intro x hx
    have hxold : s.dynamic.on_table_p x = true := by
      simpa [stack] using hx
    simpa [stack] using htable x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simp [stack] at hx
    · have hxold : s.dynamic.holding_p x = true := by
        simpa [stack, hxo] using hx
      simpa [stack] using hholding x hxold
  · intro x y hxy
    by_cases hp : x = var_ob ∧ y = var_underob
    · rcases hp with ⟨rfl, rfl⟩
      simpa [stack] using And.intro hobmem hundmem
    · have hxyold : s.dynamic.on_p x y = true := by
        simpa [stack, hp] using hxy
      simpa [stack] using hon x y hxyold
  · intro x y₁ y₂ h₁ h₂
    by_cases hxo : x = var_ob
    · subst x
      have hy₁ : y₁ = var_underob := by
        by_cases h : y₁ = var_underob
        · exact h
        · have hold : s.dynamic.on_p var_ob y₁ = true := by
            simpa [stack, h] using h₁
          exact False.elim (hobNoOut y₁ hold)
      have hy₂ : y₂ = var_underob := by
        by_cases h : y₂ = var_underob
        · exact h
        · have hold : s.dynamic.on_p var_ob y₂ = true := by
            simpa [stack, h] using h₂
          exact False.elim (hobNoOut y₂ hold)
      exact hy₁.trans hy₂.symm
    · exact hbelow x y₁ y₂
        (by simpa [stack, hxo] using h₁)
        (by simpa [stack, hxo] using h₂)
  · intro x₁ x₂ y h₁ h₂
    by_cases hy : y = var_underob
    · subst y
      have hx₁ : x₁ = var_ob := by
        by_cases h : x₁ = var_ob
        · exact h
        · have hold : s.dynamic.on_p x₁ var_underob = true := by
            simpa [stack, h] using h₁
          exact False.elim (hundNoTop x₁ hold)
      have hx₂ : x₂ = var_ob := by
        by_cases h : x₂ = var_ob
        · exact h
        · have hold : s.dynamic.on_p x₂ var_underob = true := by
            simpa [stack, h] using h₂
          exact False.elim (hundNoTop x₂ hold)
      exact hx₁.trans hx₂.symm
    · have ho₁ : s.dynamic.on_p x₁ y = true := by
        by_cases h : x₁ = var_ob
        · subst x₁
          simpa [stack, hy] using h₁
        · simpa [stack, h] using h₁
      have ho₂ : s.dynamic.on_p x₂ y = true := by
        by_cases h : x₂ = var_ob
        · subst x₂
          simpa [stack, hy] using h₂
        · simpa [stack, h] using h₂
      exact habove x₁ x₂ y ho₁ ho₂
  · intro x hcycle
    have hNoPath :
        ¬ Relation.ReflTransGen
          (fun a b => s.dynamic.on_p a b = true)
          var_underob var_ob :=
      rt_not_of_no_in (Ne.symm hne) hobNoTop
    have hmapped :
        Relation.TransGen
          (fun a b =>
            s.dynamic.on_p a b = true ∨
              (a = var_ob ∧ b = var_underob)) x x := by
      apply transGen_mono _ hcycle
      intro a b hab
      by_cases hp : a = var_ob ∧ b = var_underob
      · exact Or.inr hp
      · exact Or.inl (by simpa [stack, hp] using hab)
    rcases transGen_add_edge_decomp hNoPath hmapped with
      hold | ⟨hxu, hux⟩
    · exact hcycles x hold
    · exact hNoPath (rt_trans hux hxu)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [stack, hobNotTable]
    · simpa [stack, hxo] using
        hloc x (by simpa [stack] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      have hNoTopNew :
          ¬ ∃ y,
            (stack var_ob var_underob s).dynamic.on_p
              y var_ob = true := by
        rintro ⟨y, hy⟩
        by_cases hp : y = var_ob ∧ var_ob = var_underob
        · exact hne hp.2
        · have hold : s.dynamic.on_p y var_ob = true := by
            simpa [stack, hp] using hy
          exact hobNoTop y hold
      constructor
      · intro _
        exact hNoTopNew
      · intro hex _
        exact hNoTopNew hex
    · by_cases hxu : x = var_underob
      · subst x
        simp [stack, hne, Ne.symm hne]
      · simpa [stack, hxo, hxu] using
          hclearCons x (by simpa [stack] using hxmem)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      simp [stack]
    · by_cases hxu : x = var_underob
      · subst x
        simp [stack, hne, Ne.symm hne]
      · simpa [stack, hxo, hxu] using
          hheldClear x (by simpa [stack] using hxmem)
  · constructor
    · intro _
      exact noHeldAfter
    · intro hex
      exact False.elim (noHeldAfter hex)
  · intro x₁ x₂ hx₁ _
    exact False.elim (noHeldAfter ⟨x₁, hx₁⟩)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inl ⟨var_underob, by simp [stack]⟩
    · simpa [stack, hxo] using
        hhasLoc x (by simpa [stack] using hxmem)
  · intro x hxmem hnone
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inl (by simp [stack])
    · by_cases hxu : x = var_underob
      · subst x
        exfalso
        apply hnone
        exact ⟨var_ob, by simp [stack]⟩
      · have hnoneOld : ¬ ∃ y, s.dynamic.on_p y x = true := by
          intro hex
          rcases hex with ⟨y, hy⟩
          apply hnone
          exact ⟨y, oldToNew y x hy⟩
        simpa [stack, hxo, hxu] using
          hnoTop x (by simpa [stack] using hxmem) hnoneOld
  · intro x hxmem hxNotHeld
    by_cases hxo : x = var_ob
    · subst x
      rcases hground var_underob hundmem hundNotHeld with
        ⟨y, huy, hyTable⟩
      have hstep :
          Relation.ReflTransGen
            (fun a b =>
              (stack var_ob var_underob s).dynamic.on_p a b = true)
            var_ob var_underob :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (by simp [stack])
      have huy' := rt_mono oldToNew huy
      exact ⟨y, rt_trans hstep huy', by simpa [stack] using hyTable⟩
    · have hxOldNotHeld : s.dynamic.holding_p x = false := by
        simpa [stack, hxo] using hxNotHeld
      rcases hground x (by simpa [stack] using hxmem) hxOldNotHeld with
        ⟨y, hxy, hyTable⟩
      exact ⟨y, rt_mono oldToNew hxy, by simpa [stack] using hyTable⟩

lemma unstack_preserves_wf
    (var_ob var_underob)
    (s : State)
    (hwf : WellFormed s)
    (hpre : unstackPre var_ob var_underob s) :
    WellFormed (unstack var_ob var_underob s) := by
  rcases hwf with
    ⟨hstatic, hclear, htable, hholding, hon, hbelow, habove,
      hcycles, hloc, hclearCons, hheldClear, harm, hcapacity,
      hhasLoc, hnoTop, hground⟩
  rcases hpre with
    ⟨hobmem, hundmem, hobOnUnder, hobClear, harmEmpty⟩

  have hne : var_ob ≠ var_underob := by
    intro heq
    subst var_underob
    exact hcycles var_ob
      (Relation.TransGen.single hobOnUnder)

  have hobNoTop : ∀ y, ¬ s.dynamic.on_p y var_ob = true := by
    intro y hy
    exact (hclearCons var_ob hobmem).1 hobClear ⟨y, hy⟩

  have hobOnlyUnder :
      ∀ y, s.dynamic.on_p var_ob y = true → y = var_underob := by
    intro y hy
    exact hbelow var_ob y var_underob hy hobOnUnder

  have hobNotTable : ¬ s.dynamic.on_table_p var_ob = true := by
    intro ht
    exact (hloc var_ob hobmem).1
      ⟨⟨var_underob, hobOnUnder⟩, ht⟩

  have noOldHeld : ¬ ∃ x, s.dynamic.holding_p x = true :=
    harm.1 harmEmpty

  have hundNotHeld : s.dynamic.holding_p var_underob = false := by
    cases h : s.dynamic.holding_p var_underob with
    | false => rfl
    | true => exact False.elim (noOldHeld ⟨var_underob, h⟩)

  have newToOld :
      ∀ a b, (unstack var_ob var_underob s).dynamic.on_p a b = true →
        s.dynamic.on_p a b = true := by
    intro a b hab
    have hh :
        (a ≠ var_ob ∨ b ≠ var_underob) ∧
          s.dynamic.on_p a b = true := by
      simpa [unstack] using hab
    exact hh.2

  have oldToNewAway :
      ∀ a b, a ≠ var_ob →
        s.dynamic.on_p a b = true →
        (unstack var_ob var_underob s).dynamic.on_p a b = true := by
    intro a b ha hab
    simpa [unstack, ha] using hab

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa [unstack] using hstatic
  · intro x hx
    by_cases hxu : x = var_underob
    · subst x
      simpa [unstack] using hundmem
    · by_cases hxo : x = var_ob
      · subst x
        simp [unstack, hne] at hx
      · have hxold : s.dynamic.clear_p x = true := by
          simpa [unstack, hxu, hxo] using hx
        simpa [unstack] using hclear x hxold
  · intro x hx
    have hxold : s.dynamic.on_table_p x = true := by
      simpa [unstack] using hx
    simpa [unstack] using htable x hxold
  · intro x hx
    by_cases hxo : x = var_ob
    · subst x
      simpa [unstack] using hobmem
    · have hxold : s.dynamic.holding_p x = true := by
        simpa [unstack, hxo] using hx
      simpa [unstack] using hholding x hxold
  · intro x y hxy
    have hxyold := newToOld x y hxy
    simpa [unstack] using hon x y hxyold
  · intro x y₁ y₂ h₁ h₂
    exact hbelow x y₁ y₂
      (newToOld x y₁ h₁) (newToOld x y₂ h₂)
  · intro x₁ x₂ y h₁ h₂
    exact habove x₁ x₂ y
      (newToOld x₁ y h₁) (newToOld x₂ y h₂)
  · intro x hcycle
    exact hcycles x (transGen_mono newToOld hcycle)
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      have hNoOutNew :
          ¬ ∃ y,
            (unstack var_ob var_underob s).dynamic.on_p var_ob y = true := by
        rintro ⟨y, hy⟩
        have hyOld := newToOld var_ob y hy
        have hyEq := hobOnlyUnder y hyOld
        subst y
        simp [unstack] at hy
      constructor
      · rintro ⟨hex, _⟩
        exact hNoOutNew hex
      · constructor
        · rintro ⟨hex, _⟩
          exact hNoOutNew hex
        · rintro ⟨ht, _⟩
          apply hobNotTable
          simpa [unstack] using ht
    · simpa [unstack, hxo] using
        hloc x (by simpa [unstack] using hxmem)
  · intro x hxmem
    by_cases hxu : x = var_underob
    · subst x
      have hNoTopNew :
          ¬ ∃ y,
            (unstack var_ob var_underob s).dynamic.on_p
              y var_underob = true := by
        rintro ⟨y, hy⟩
        have hyOld := newToOld y var_underob hy
        have hyEq : y = var_ob :=
          habove y var_ob var_underob hyOld hobOnUnder
        subst y
        simp [unstack] at hy
      constructor
      · intro _
        exact hNoTopNew
      · intro hex _
        exact hNoTopNew hex
    · by_cases hxo : x = var_ob
      · subst x
        constructor
        · intro hfalse
          simp [unstack, hne] at hfalse
        · intro _ hfalse
          simp [unstack, hne] at hfalse
      · constructor
        · intro hcx
          intro hex
          rcases hex with ⟨y, hy⟩
          exact (hclearCons x (by simpa [unstack] using hxmem)).1
            (by simpa [unstack, hxu, hxo] using hcx)
            ⟨y, newToOld y x hy⟩
        · intro hex hcx
          apply (hclearCons x (by simpa [unstack] using hxmem)).2
            ⟨hex.choose, newToOld hex.choose x hex.choose_spec⟩
          simpa [unstack, hxu, hxo] using hcx
  · intro x hxmem
    by_cases hxu : x = var_underob
    · subst x
      simp [unstack, Ne.symm hne, hundNotHeld]
    · by_cases hxo : x = var_ob
      · subst x
        simp [unstack, hne]
      · simpa [unstack, hxu, hxo] using
          hheldClear x (by simpa [unstack] using hxmem)
  · simp [ArmEmptyIffNoneHeld, unstack]
  · intro x₁ x₂ hx₁ hx₂
    have h₁ : x₁ = var_ob := by
      by_cases h : x₁ = var_ob
      · exact h
      · have hold : s.dynamic.holding_p x₁ = true := by
          simpa [unstack, h] using hx₁
        exact False.elim (noOldHeld ⟨x₁, hold⟩)
    have h₂ : x₂ = var_ob := by
      by_cases h : x₂ = var_ob
      · exact h
      · have hold : s.dynamic.holding_p x₂ = true := by
          simpa [unstack, h] using hx₂
        exact False.elim (noOldHeld ⟨x₂, hold⟩)
    exact h₁.trans h₂.symm
  · intro x hxmem
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inr (Or.inr (by simp [unstack]))
    · simpa [unstack, hxo] using
        hhasLoc x (by simpa [unstack] using hxmem)
  · intro x hxmem hnone
    by_cases hxo : x = var_ob
    · subst x
      exact Or.inr (by simp [unstack])
    · by_cases hxu : x = var_underob
      · subst x
        exact Or.inl (by simp [unstack, hne])
      · have hnoneOld : ¬ ∃ y, s.dynamic.on_p y x = true := by
          intro hex
          rcases hex with ⟨y, hy⟩
          apply hnone
          by_cases hyo : y = var_ob
          · subst y
            have : x = var_underob := hobOnlyUnder x hy
            exact False.elim (hxu this)
          · exact ⟨y, by simpa [unstack, hyo] using hy⟩
        simpa [unstack, hxo, hxu] using
          hnoTop x (by simpa [unstack] using hxmem) hnoneOld
  · intro x hxmem hxNotHeld
    have hxo : x ≠ var_ob := by
      intro h
      subst x
      simp [unstack] at hxNotHeld
    have hxOldNotHeld : s.dynamic.holding_p x = false := by
      simpa [unstack, hxo] using hxNotHeld
    rcases hground x (by simpa [unstack] using hxmem) hxOldNotHeld with
      ⟨y, hxy, hyTable⟩
    have hmapped :=
      rt_map_avoiding hxo hobNoTop oldToNewAway hxy
    exact ⟨y, hmapped.1, by simpa [unstack] using hyTable⟩

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | pickup var_ob =>
      exact pickup_preserves_wf var_ob s hwf hpre
  | putdown var_ob =>
      exact putdown_preserves_wf var_ob s hwf hpre
  | stack var_ob var_underob =>
      exact stack_preserves_wf var_ob var_underob s hwf hpre
  | unstack var_ob var_underob =>
      exact unstack_preserves_wf var_ob var_underob s hwf hpre

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
## Auxiliary predicates and measures
-/

def GPFlat (objects : List Obj) (s : State) : Prop :=
  s.statics.objects = objects ∧
  s.dynamic.arm_empty_p = true ∧
  (∀ x, s.dynamic.holding_p x = false) ∧
  (∀ x y, s.dynamic.on_p x y = false) ∧
  (∀ x, x ∈ objects →
    s.dynamic.clear_p x = true ∧
    s.dynamic.on_table_p x = true)

def gpNonTableCount (objects : List Obj) (s : State) : Nat :=
  (objects.filter
    (fun b => s.dynamic.on_table_p b = false)).length

def GPGoalRoot
    (g : Goal)
    (allObjects : List Obj)
    (b : Obj) : Prop :=
  b ∈ allObjects ∧
  gpFindGoalSupport b g allObjects = none

def gpUnprocessedCount
    (allObjects processed : List Obj) : Nat :=
  (allObjects.filter (fun b => b ∉ processed)).length

def GPBuildInv
    (allObjects : List Obj)
    (g : Goal)
    (processed : List Obj)
    (s : State) : Prop :=
  s.statics.objects = allObjects ∧
  s.dynamic.arm_empty_p = true ∧
  (∀ x, s.dynamic.holding_p x = false) ∧
  (∀ b, b ∈ allObjects → b ∉ processed →
    s.dynamic.clear_p b = true ∧
    s.dynamic.on_table_p b = true) ∧
  (∀ x y,
    s.dynamic.on_p x y = true ↔
      x ∈ processed ∧
      g.dynamic.on_p x y = some true) ∧
  (∀ y, y ∈ allObjects →
    (s.dynamic.clear_p y = true ↔
      ¬ ∃ x, x ∈ processed ∧
        g.dynamic.on_p x y = some true))

/-!
## Specifications of the clearing-phase search functions
-/

lemma gpFindCurrentSupport_some
    (b : Obj)
    (s : State)
    (candidates : List Obj)
    (a : Obj)
    (h :
      gpFindCurrentSupport b s candidates = some a) :
    a ∈ candidates ∧
    s.dynamic.on_p b a = true := by
  induction candidates with
  | nil =>
      simp [gpFindCurrentSupport] at h
  | cons c rest ih =>
      by_cases hc : s.dynamic.on_p b c = true
      · simp [gpFindCurrentSupport, hc] at h
        subst a
        exact ⟨by simp, hc⟩
      · have hrest :
            gpFindCurrentSupport b s rest = some a := by
          simpa [gpFindCurrentSupport, hc] using h
        rcases ih hrest with ⟨ha, hon⟩
        exact ⟨by simp [ha], hon⟩

lemma gpFindCurrentSupport_none
    (b : Obj)
    (s : State)
    (candidates : List Obj)
    (h :
      gpFindCurrentSupport b s candidates = none) :
    ∀ a, a ∈ candidates →
      s.dynamic.on_p b a ≠ true := by
  induction candidates with
  | nil =>
      simp
  | cons c rest ih =>
      by_cases hc : s.dynamic.on_p b c = true
      · simp [gpFindCurrentSupport, hc] at h
      · have hrest :
            gpFindCurrentSupport b s rest = none := by
          simpa [gpFindCurrentSupport, hc] using h
        intro a ha
        have ha' : a = c ∨ a ∈ rest := by
          simpa only [List.mem_cons] using ha
        rcases ha' with hac | haRest
        · subst a
          exact hc
        · exact ih hrest a haRest

lemma gpFindCurrentSupport_complete
    (b : Obj)
    (s : State)
    (candidates : List Obj)
    (a : Obj)
    (ha : a ∈ candidates)
    (hon : s.dynamic.on_p b a = true) :
    ∃ a',
      gpFindCurrentSupport b s candidates = some a' := by
  cases hfind : gpFindCurrentSupport b s candidates with
  | none =>
      have hnot :=
        gpFindCurrentSupport_none b s candidates hfind a ha
      exact False.elim (hnot hon)
  | some a' =>
      exact ⟨a', rfl⟩

lemma gpFindUnstackCandidate_some
    (s : State)
    (candidates : List Obj)
    (b a : Obj)
    (h :
      gpFindUnstackCandidate s candidates = some (b, a)) :
    b ∈ candidates ∧
    s.dynamic.clear_p b = true ∧
    s.dynamic.on_table_p b = false ∧
    a ∈ s.statics.objects ∧
    s.dynamic.on_p b a = true := by
  induction candidates with
  | nil =>
      simp [gpFindUnstackCandidate] at h
  | cons c rest ih =>
      by_cases hc :
          s.dynamic.clear_p c = true ∧
          s.dynamic.on_table_p c = false
      · cases hs :
          gpFindCurrentSupport c s s.statics.objects with
        | none =>
            have hrest :
                gpFindUnstackCandidate s rest = some (b, a) := by
              simpa [gpFindUnstackCandidate, hc, hs] using h
            rcases ih hrest with
              ⟨hbmem, hbClear, hbNotTable, hamem, hba⟩
            exact
              ⟨List.mem_cons_of_mem c hbmem,
               hbClear, hbNotTable, hamem, hba⟩
        | some d =>
            have hp : (c, d) = (b, a) := by
              simpa [gpFindUnstackCandidate, hc, hs] using h
            have hcb : c = b := congrArg Prod.fst hp
            have hda : d = a := congrArg Prod.snd hp
            subst b
            subst a
            rcases
                gpFindCurrentSupport_some
                  c s s.statics.objects d hs with
              ⟨hdmem, hcd⟩
            exact
              ⟨by simp,
               hc.1,
               hc.2,
               hdmem,
               hcd⟩
      · have hrest :
            gpFindUnstackCandidate s rest = some (b, a) := by
          simpa [gpFindUnstackCandidate, hc] using h
        rcases ih hrest with
          ⟨hbmem, hbClear, hbNotTable, hamem, hba⟩
        exact
          ⟨List.mem_cons_of_mem c hbmem,
           hbClear, hbNotTable, hamem, hba⟩

lemma gpFindUnstackCandidate_none
    (s : State)
    (candidates : List Obj)
    (h :
      gpFindUnstackCandidate s candidates = none) :
    ∀ b, b ∈ candidates →
      s.dynamic.clear_p b = true →
      s.dynamic.on_table_p b = false →
      ∀ a, a ∈ s.statics.objects →
        s.dynamic.on_p b a ≠ true := by
  induction candidates with
  | nil =>
      intro b hb
      simp at hb
  | cons c rest ih =>
      by_cases hc :
          s.dynamic.clear_p c = true ∧
          s.dynamic.on_table_p c = false
      · cases hs :
          gpFindCurrentSupport c s s.statics.objects with
        | none =>
            have hrest :
                gpFindUnstackCandidate s rest = none := by
              simpa [gpFindUnstackCandidate, hc, hs] using h
            intro b hb hbClear hbNotTable a ha
            have hbCases : b = c ∨ b ∈ rest := by
              simpa only [List.mem_cons] using hb
            rcases hbCases with hbc | hbRest
            · subst b
              exact
                gpFindCurrentSupport_none
                  c s s.statics.objects hs a ha
            · exact
                ih hrest b hbRest hbClear hbNotTable a ha
        | some d =>
            simp [gpFindUnstackCandidate, hc, hs] at h
      · have hrest :
            gpFindUnstackCandidate s rest = none := by
          simpa [gpFindUnstackCandidate, hc] using h
        intro b hb hbClear hbNotTable a ha
        have hbCases : b = c ∨ b ∈ rest := by
          simpa only [List.mem_cons] using hb
        rcases hbCases with hbc | hbRest
        · subst b
          exact False.elim (hc ⟨hbClear, hbNotTable⟩)
        · exact
            ih hrest b hbRest hbClear hbNotTable a ha

/-!
## Structural result for the clearing phase
-/

lemma gp_mem_erase_of_mem_ne
    {a x : Obj}
    {objects : List Obj}
    (ha : a ∈ objects)
    (hne : a ≠ x) :
    a ∈ objects.erase x := by
  induction objects with
  | nil =>
      simp at ha
  | cons b rest ih =>
      by_cases hbx : b = x
      · subst b
        have haRest : a ∈ rest := by
          simpa [hne] using ha
        simpa using haRest
      · have haCases : a = b ∨ a ∈ rest := by
          simpa only [List.mem_cons] using ha
        rcases haCases with hab | haRest
        · subst a
          simp [hbx]
        · have hi : a ∈ rest.erase x := ih haRest
          simpa [hbx] using List.mem_cons_of_mem b hi

lemma gp_mem_of_mem_erase
    {a x : Obj}
    {objects : List Obj}
    (ha : a ∈ objects.erase x) :
    a ∈ objects := by
  induction objects with
  | nil =>
      simp at ha
  | cons b rest ih =>
      by_cases hbx : b = x
      · subst b
        have haRest : a ∈ rest := by
          simpa using ha
        exact List.mem_cons_of_mem x haRest
      · have haCases : a = b ∨ a ∈ rest.erase x := by
          simpa [hbx] using ha
        rcases haCases with hab | haRest
        · subst a
          simp
        · exact List.mem_cons_of_mem b (ih haRest)

lemma gp_length_erase_lt_of_mem
    {x : Obj}
    {objects : List Obj}
    (hx : x ∈ objects) :
    (objects.erase x).length < objects.length := by
  induction objects with
  | nil =>
      simp at hx
  | cons b rest ih =>
      by_cases hbx : b = x
      · subst b
        simp
      · have hxb : x ≠ b := by
          intro h
          exact hbx h.symm
        have hxRest : x ∈ rest := by
          simpa only [List.mem_cons, hxb, false_or] using hx
        have hlt := ih hxRest
        simpa [hbx] using Nat.succ_lt_succ hlt

lemma gp_rt_prepend_to_transGen
    {α : Type}
    {r : α → α → Prop}
    {a b c : α}
    (hab : r a b)
    (hbc : Relation.ReflTransGen r b c) :
    Relation.TransGen r a c := by
  induction hbc with
  | refl =>
      exact Relation.TransGen.single hab
  | tail _ hcd ih =>
      exact Relation.TransGen.tail ih hcd

lemma gp_rt_then_step_to_transGen
    {α : Type}
    {r : α → α → Prop}
    {a b c : α}
    (hab : Relation.ReflTransGen r a b)
    (hbc : r b c) :
    Relation.TransGen r a c := by
  induction hab generalizing c with
  | refl =>
      exact Relation.TransGen.single hbc
  | tail hpath hlast ih =>
      exact Relation.TransGen.tail (ih hlast) hbc

lemma gp_transGen_has_first
    {α : Type}
    {r : α → α → Prop}
    {a b : α}
    (h : Relation.TransGen r a b) :
    ∃ c, r a c := by
  induction h with
  | single hab =>
      exact ⟨_, hab⟩
  | tail _ _ ih =>
      exact ih

lemma gp_finite_acyclic_has_source
    (r : Obj → Obj → Prop)
    (objects : List Obj)
    (hvalid :
      ∀ a b, r a b → a ∈ objects ∧ b ∈ objects)
    (hcycles :
      ∀ a, ¬ Relation.TransGen r a a)
    (x : Obj)
    (hx : x ∈ objects) :
    ∃ top,
      top ∈ objects ∧
      Relation.ReflTransGen r top x ∧
      ∀ z, ¬ r z top := by
  classical
  by_cases hsource : ∀ z, ¬ r z x
  · exact
      ⟨x, hx, Relation.ReflTransGen.refl, hsource⟩
  · push_neg at hsource
    rcases hsource with ⟨y, hyx⟩

    have hyMem : y ∈ objects :=
      (hvalid y x hyx).1

    have hyne : y ≠ x := by
      intro hyxEq
      subst y
      exact hcycles x (Relation.TransGen.single hyx)

    let q : Obj → Obj → Prop :=
      fun a b => r a b ∧ a ≠ x ∧ b ≠ x

    have hvalidQ :
        ∀ a b, q a b →
          a ∈ objects.erase x ∧ b ∈ objects.erase x := by
      intro a b hab
      change r a b ∧ a ≠ x ∧ b ≠ x at hab
      have habMem := hvalid a b hab.1
      exact
        ⟨gp_mem_erase_of_mem_ne habMem.1 hab.2.1,
         gp_mem_erase_of_mem_ne habMem.2 hab.2.2⟩

    have hcyclesQ :
        ∀ a, ¬ Relation.TransGen q a a := by
      intro a hcycle
      apply hcycles a
      apply transGen_mono _ hcycle
      intro u v huv
      change r u v ∧ u ≠ x ∧ v ≠ x at huv
      exact huv.1

    have hyErase : y ∈ objects.erase x :=
      gp_mem_erase_of_mem_ne hyMem hyne

    rcases
        gp_finite_acyclic_has_source
          q (objects.erase x) hvalidQ hcyclesQ y hyErase with
      ⟨top, htopErase, htopToYQ, htopSourceQ⟩

    have htopMem : top ∈ objects :=
      gp_mem_of_mem_erase htopErase

    have htopToY :
        Relation.ReflTransGen r top y := by
      apply rt_mono _ htopToYQ
      intro a b hab
      change r a b ∧ a ≠ x ∧ b ≠ x at hab
      exact hab.1

    have htopToX :
        Relation.ReflTransGen r top x :=
      Relation.ReflTransGen.tail htopToY hyx

    have htopNe : top ≠ x := by
      intro htx
      subst top
      have hcycle :
          Relation.TransGen r x x :=
        gp_rt_then_step_to_transGen htopToY hyx
      exact hcycles x hcycle

    have htopSource : ∀ z, ¬ r z top := by
      intro z hzt
      have hzNe : z ≠ x := by
        intro hzx
        subst z
        have hxy :
            Relation.TransGen r x y :=
          gp_rt_prepend_to_transGen hzt htopToY
        exact hcycles x (Relation.TransGen.tail hxy hyx)
      have hq : q z top := by
        exact ⟨hzt, hzNe, htopNe⟩
      exact htopSourceQ z hq

    exact ⟨top, htopMem, htopToX, htopSource⟩
termination_by objects.length
decreasing_by
  exact gp_length_erase_lt_of_mem hx

lemma gpFindUnstackCandidate_none_flat
    (s : State)
    (hwf : WellFormed s)
    (harm : s.dynamic.arm_empty_p = true)
    (hnone :
      gpFindUnstackCandidate s s.statics.objects = none) :
    GPFlat s.statics.objects s := by
  rcases hwf with
    ⟨hstatic, hvalidClear, hvalidTable, hvalidHolding, hvalidOn,
      hbelow, habove, hcycles, hloc, hclearCons, hheldClear,
      harmIff, hcapacity, hhasLoc, hnoTop, hground⟩

  have hnoHeld :
      ¬ ∃ x, s.dynamic.holding_p x = true :=
    harmIff.1 harm

  have hallHolding :
      ∀ x, s.dynamic.holding_p x = false := by
    intro x
    cases hx : s.dynamic.holding_p x with
    | false =>
        rfl
    | true =>
        exact False.elim (hnoHeld ⟨x, hx⟩)

  have hvalidRel :
      ∀ a b,
        s.dynamic.on_p a b = true →
          a ∈ s.statics.objects ∧ b ∈ s.statics.objects := by
    intro a b hab
    exact hvalidOn a b hab

  have hacyclicRel :
      ∀ a,
        ¬ Relation.TransGen
          (fun x y => s.dynamic.on_p x y = true) a a := by
    intro a hcycle
    exact hcycles a hcycle

  have hnoneSpec :=
    gpFindUnstackCandidate_none
      s s.statics.objects hnone

  have hallOn :
      ∀ x y, s.dynamic.on_p x y = false := by
    intro x y
    cases hxy : s.dynamic.on_p x y with
    | false =>
        rfl
    | true =>
        exfalso

        have hxMem : x ∈ s.statics.objects :=
          (hvalidRel x y hxy).1

        rcases
            gp_finite_acyclic_has_source
              (fun a b => s.dynamic.on_p a b = true)
              s.statics.objects
              hvalidRel
              hacyclicRel
              x
              hxMem with
          ⟨top, htopMem, htopToX, htopSource⟩

        have hnoneAboveTop :
            ¬ ∃ z, s.dynamic.on_p z top = true := by
          rintro ⟨z, hzt⟩
          exact htopSource z hzt

        have htopClear :
            s.dynamic.clear_p top = true := by
          rcases hnoTop top htopMem hnoneAboveTop with
            hclear | hheld
          · exact hclear
          · exact False.elim (hnoHeld ⟨top, hheld⟩)

        have htopToY :
            Relation.TransGen
              (fun a b => s.dynamic.on_p a b = true)
              top y :=
          gp_rt_then_step_to_transGen htopToX hxy

        rcases gp_transGen_has_first htopToY with
          ⟨under, htopOnUnder⟩

        have hunderMem : under ∈ s.statics.objects :=
          (hvalidRel top under htopOnUnder).2

        have htopNotTable :
            ¬ s.dynamic.on_table_p top = true := by
          intro htable
          exact
            (hloc top htopMem).1
              ⟨⟨under, htopOnUnder⟩, htable⟩

        have htopTableFalse :
            s.dynamic.on_table_p top = false := by
          cases htable : s.dynamic.on_table_p top with
          | false =>
              rfl
          | true =>
              exact False.elim (htopNotTable htable)

        exact
          (hnoneSpec
            top htopMem htopClear htopTableFalse
            under hunderMem) htopOnUnder

  have hallTable :
      ∀ x, x ∈ s.statics.objects →
        s.dynamic.on_table_p x = true := by
    intro x hxMem
    rcases hhasLoc x hxMem with hon | htable | hheld
    · rcases hon with ⟨y, hxy⟩
      have hfalse := hallOn x y
      exfalso
      simpa [hfalse] using hxy
    · exact htable
    · exact False.elim (hnoHeld ⟨x, hheld⟩)

  have hallClear :
      ∀ x, x ∈ s.statics.objects →
        s.dynamic.clear_p x = true := by
    intro x hxMem
    have hnoneAbove :
        ¬ ∃ y, s.dynamic.on_p y x = true := by
      rintro ⟨y, hyx⟩
      have hfalse := hallOn y x
      simpa [hfalse] using hyx
    rcases hnoTop x hxMem hnoneAbove with hclear | hheld
    · exact hclear
    · exact False.elim (hnoHeld ⟨x, hheld⟩)

  refine ⟨rfl, harm, hallHolding, hallOn, ?_⟩
  intro x hxMem
  exact ⟨hallClear x hxMem, hallTable x hxMem⟩

lemma gp_filter_false_length_lt_of_removed
    (objects : List Obj)
    (old new : Obj → Bool)
    (b : Obj)
    (hbmem : b ∈ objects)
    (hold : old b = false)
    (hnew : new b = true)
    (hne : ∀ x, x ≠ b → new x = old x) :
    (objects.filter (fun x => new x = false)).length <
      (objects.filter (fun x => old x = false)).length := by
  have hle :
      ∀ ys : List Obj,
        (ys.filter (fun x => new x = false)).length ≤
          (ys.filter (fun x => old x = false)).length := by
    intro ys
    induction ys with
    | nil =>
        simp
    | cons x xs ih =>
        by_cases hxb : x = b
        · subst x
          simpa [hnew, hold] using Nat.le_succ_of_le ih
        · have heq : new x = old x := hne x hxb
          cases hx : old x with
          | false =>
              have hn : new x = false := heq.trans hx
              simpa [hx, hn] using Nat.succ_le_succ ih
          | true =>
              have hn : new x = true := heq.trans hx
              simpa [hx, hn] using ih

  induction objects with
  | nil =>
      simp at hbmem
  | cons x xs ih =>
      by_cases hxb : x = b
      · subst x
        simpa [hnew, hold] using
          (Nat.lt_succ_iff.mpr (hle xs))
      · have hbxs : b ∈ xs := by
          have hcases : b = x ∨ b ∈ xs := by
            simpa only [List.mem_cons] using hbmem
          rcases hcases with hbx | hbxs
          · exact False.elim (hxb hbx.symm)
          · exact hbxs
        have hlt := ih hbxs
        have heq : new x = old x := hne x hxb
        cases hx : old x with
        | false =>
            have hn : new x = false := heq.trans hx
            simpa [hx, hn] using Nat.succ_lt_succ hlt
        | true =>
            have hn : new x = true := heq.trans hx
            simpa [hx, hn] using hlt

lemma gpClear_step_decreases
    (s : State)
    (b a : Obj)
    (h :
      gpFindUnstackCandidate s s.statics.objects =
        some (b, a)) :
    gpNonTableCount s.statics.objects
        (putdown b (unstack b a s)) <
      gpNonTableCount s.statics.objects s := by
  rcases
      gpFindUnstackCandidate_some
        s s.statics.objects b a h with
    ⟨hbmem, _, hbNotTable, _, _⟩

  have hnew :
      (putdown b (unstack b a s)).dynamic.on_table_p b = true :=
    putdown_on_table_p_eq1 b (unstack b a s)

  have hne :
      ∀ x, x ≠ b →
        (putdown b (unstack b a s)).dynamic.on_table_p x =
          s.dynamic.on_table_p x := by
    intro x hxb
    calc
      (putdown b (unstack b a s)).dynamic.on_table_p x =
          (unstack b a s).dynamic.on_table_p x :=
        putdown_on_table_p_ne b (unstack b a s) hxb
      _ = s.dynamic.on_table_p x :=
        congrFun (unstack_on_table_p b a s) x

  unfold gpNonTableCount
  exact
    gp_filter_false_length_lt_of_removed
      s.statics.objects
      s.dynamic.on_table_p
      (putdown b (unstack b a s)).dynamic.on_table_p
      b
      hbmem
      hbNotTable
      hnew
      hne

lemma gpNonTableCount_le_length
    (objects : List Obj)
    (s : State) :
    gpNonTableCount objects s ≤ objects.length := by
  unfold gpNonTableCount
  induction objects with
  | nil =>
      simp
  | cons b rest ih =>
      by_cases hb : s.dynamic.on_table_p b = false
      · simpa [hb] using Nat.succ_le_succ ih
      · have hle :
            (rest.filter
              (fun x => s.dynamic.on_table_p x = false)).length
              ≤ Nat.succ rest.length :=
          Nat.le_trans ih (Nat.le_succ rest.length)
        simpa [hb] using hle

/-!
## Correctness of the clearing phase
-/

lemma gpClearToTableAux_correct
    (fuel : List Obj)
    (s : State)
    (hwf : WellFormed s)
    (harm : s.dynamic.arm_empty_p = true)
    (hbound :
      gpNonTableCount s.statics.objects s ≤ fuel.length) :
    ValidPlan (gpClearToTableAux fuel s) s ∧
    WellFormed (runPlan (gpClearToTableAux fuel s) s) ∧
    GPFlat s.statics.objects
      (runPlan (gpClearToTableAux fuel s) s) := by
  induction fuel generalizing s with
  | nil =>
      have hnone :
          gpFindUnstackCandidate s s.statics.objects = none := by
        cases hfind :
            gpFindUnstackCandidate s s.statics.objects with
        | none =>
            rfl
        | some candidate =>
            rcases candidate with ⟨b, a⟩
            have hdec :=
              gpClear_step_decreases s b a hfind
            have hzero :
                gpNonTableCount s.statics.objects s = 0 := by
              simpa using hbound
            rw [hzero] at hdec
            exact False.elim (Nat.not_lt_zero _ hdec)

      have hflat :
          GPFlat s.statics.objects s :=
        gpFindUnstackCandidate_none_flat s hwf harm hnone

      refine ⟨?_, ?_, ?_⟩
      · simp [gpClearToTableAux, ValidPlan]
      · simpa [gpClearToTableAux, runPlan] using hwf
      · simpa [gpClearToTableAux, runPlan] using hflat

  | cons f fuel ih =>
      cases hfind :
          gpFindUnstackCandidate s s.statics.objects with
      | none =>
          have hflat :
              GPFlat s.statics.objects s :=
            gpFindUnstackCandidate_none_flat s hwf harm hfind

          refine ⟨?_, ?_, ?_⟩
          · simp [gpClearToTableAux, hfind, ValidPlan]
          · simpa [gpClearToTableAux, hfind, runPlan] using hwf
          · simpa [gpClearToTableAux, hfind, runPlan] using hflat

      | some candidate =>
          rcases candidate with ⟨b, a⟩

          rcases
              gpFindUnstackCandidate_some
                s s.statics.objects b a hfind with
            ⟨hbmem, hbClear, hbNotTable, hamem, hba⟩

          have hunstackPre :
              unstackPre b a s :=
            ⟨hbmem, hamem, hba, hbClear, harm⟩

          have hwfUnstack :
              WellFormed (unstack b a s) :=
            unstack_preserves_wf b a s hwf hunstackPre

          have hputdownPre :
              putdownPre b (unstack b a s) := by
            constructor
            · rw [unstack_statics]
              exact hbmem
            · exact unstack_holding_p_eq1 b a s

          have hwfNext :
              WellFormed (putdown b (unstack b a s)) :=
            putdown_preserves_wf
              b (unstack b a s) hwfUnstack hputdownPre

          have harmNext :
              (putdown b (unstack b a s)).dynamic.arm_empty_p =
                true :=
            putdown_arm_empty_p b (unstack b a s)

          have hdec :
              gpNonTableCount s.statics.objects
                  (putdown b (unstack b a s)) <
                gpNonTableCount s.statics.objects s :=
            gpClear_step_decreases s b a hfind

          have hboundOld :
              gpNonTableCount s.statics.objects s ≤
                fuel.length + 1 := by
            simpa using hbound

          have hboundRaw :
              gpNonTableCount s.statics.objects
                  (putdown b (unstack b a s)) ≤
                fuel.length := by
            omega

          have hboundNext :
              gpNonTableCount
                  (putdown b (unstack b a s)).statics.objects
                  (putdown b (unstack b a s)) ≤
                fuel.length := by
            rw [putdown_statics, unstack_statics]
            exact hboundRaw

          rcases
              ih
                (s := putdown b (unstack b a s))
                hwfNext
                harmNext
                hboundNext with
            ⟨hvalidRest, hwfRest, hflatRest⟩

          have hflatRest' :
              GPFlat s.statics.objects
                (runPlan
                  (gpClearToTableAux
                    fuel (putdown b (unstack b a s)))
                  (putdown b (unstack b a s))) := by
            simpa only [putdown_statics, unstack_statics] using
              hflatRest

          have hplan :
              gpClearToTableAux (f :: fuel) s =
                PlanAction.unstack b a ::
                PlanAction.putdown b ::
                gpClearToTableAux
                  fuel (putdown b (unstack b a s)) := by
            simp [gpClearToTableAux, hfind]

          rw [hplan]
          simp only [ValidPlan, runPlan, actionPre, actionApply]

          refine ⟨?_, hwfRest, hflatRest'⟩
          exact ⟨hunstackPre, hputdownPre, hvalidRest⟩

lemma gpClearToTable_correct
    (s : State)
    (hstatic : WellFormedStatic s.statics)
    (hwf : WellFormed s)
    (harm : s.dynamic.arm_empty_p = true) :
    ValidPlan (gpClearToTableAux s.statics.objects s) s ∧
    WellFormed
      (runPlan (gpClearToTableAux s.statics.objects s) s) ∧
    GPFlat s.statics.objects
      (runPlan (gpClearToTableAux s.statics.objects s) s) := by
  exact gpClearToTableAux_correct
    (fuel := s.statics.objects)
    (s := s)
    hwf
    harm
    (gpNonTableCount_le_length s.statics.objects s)

/-!
## Specifications of the goal-search functions
-/

lemma gpFindGoalSupport_some
    (b : Obj)
    (g : Goal)
    (candidates : List Obj)
    (a : Obj)
    (h :
      gpFindGoalSupport b g candidates = some a) :
    a ∈ candidates ∧
    g.dynamic.on_p b a = some true := by
  induction candidates with
  | nil =>
      simp [gpFindGoalSupport] at h
  | cons c rest ih =>
      by_cases hc : g.dynamic.on_p b c = some true
      · simp [gpFindGoalSupport, hc] at h
        subst a
        exact ⟨by simp, hc⟩
      · have hrest :
            gpFindGoalSupport b g rest = some a := by
          simpa [gpFindGoalSupport, hc] using h
        rcases ih hrest with ⟨ha, hgoal⟩
        exact ⟨List.mem_cons_of_mem c ha, hgoal⟩

lemma gpFindGoalSupport_none
    (b : Obj)
    (g : Goal)
    (candidates : List Obj)
    (h :
      gpFindGoalSupport b g candidates = none) :
    ∀ a, a ∈ candidates →
      g.dynamic.on_p b a ≠ some true := by
  induction candidates with
  | nil =>
      simp
  | cons c rest ih =>
      by_cases hc : g.dynamic.on_p b c = some true
      · simp [gpFindGoalSupport, hc] at h
      · have hrest :
            gpFindGoalSupport b g rest = none := by
          simpa [gpFindGoalSupport, hc] using h
        intro a ha
        have haCases : a = c ∨ a ∈ rest := by
          simpa only [List.mem_cons] using ha
        rcases haCases with hac | haRest
        · subst a
          exact hc
        · exact ih hrest a haRest

lemma gpFindGoalSupport_complete
    (b : Obj)
    (g : Goal)
    (candidates : List Obj)
    (a : Obj)
    (ha : a ∈ candidates)
    (hgoal : g.dynamic.on_p b a = some true) :
    ∃ a',
      gpFindGoalSupport b g candidates = some a' := by
  cases hfind : gpFindGoalSupport b g candidates with
  | none =>
      have hnot :=
        gpFindGoalSupport_none b g candidates hfind a ha
      exact False.elim (hnot hgoal)
  | some a' =>
      exact ⟨a', rfl⟩

lemma gpCollectGoalRoots_mem_iff
    (g : Goal)
    (allObjects candidates : List Obj)
    (b : Obj) :
    b ∈ gpCollectGoalRoots g allObjects candidates ↔
      b ∈ candidates ∧
      gpFindGoalSupport b g allObjects = none := by
  induction candidates with
  | nil =>
      simp [gpCollectGoalRoots]
  | cons c rest ih =>
      cases hfind : gpFindGoalSupport c g allObjects with
      | none =>
          constructor
          · intro hmem
            have hcases :
                b = c ∨
                  b ∈ gpCollectGoalRoots g allObjects rest := by
              simpa [gpCollectGoalRoots, hfind] using hmem
            rcases hcases with hbc | hbroot
            · subst b
              exact ⟨by simp, hfind⟩
            · have hspec := ih.mp hbroot
              exact
                ⟨List.mem_cons_of_mem c hspec.1, hspec.2⟩
          · rintro ⟨hbmem, hbnone⟩
            have hcases : b = c ∨ b ∈ rest := by
              simpa only [List.mem_cons] using hbmem
            rcases hcases with hbc | hbrest
            · subst b
              simp [gpCollectGoalRoots, hfind]
            · have hbroot :
                  b ∈ gpCollectGoalRoots g allObjects rest :=
                ih.mpr ⟨hbrest, hbnone⟩
              simpa [gpCollectGoalRoots, hfind] using
                List.mem_cons_of_mem c hbroot
      | some a =>
          constructor
          · intro hmem
            have hbroot :
                b ∈ gpCollectGoalRoots g allObjects rest := by
              simpa [gpCollectGoalRoots, hfind] using hmem
            have hspec := ih.mp hbroot
            exact
              ⟨List.mem_cons_of_mem c hspec.1, hspec.2⟩
          · rintro ⟨hbmem, hbnone⟩
            have hcases : b = c ∨ b ∈ rest := by
              simpa only [List.mem_cons] using hbmem
            rcases hcases with hbc | hbrest
            · subst b
              simp [hfind] at hbnone
            · have hbroot :
                  b ∈ gpCollectGoalRoots g allObjects rest :=
                ih.mpr ⟨hbrest, hbnone⟩
              simpa [gpCollectGoalRoots, hfind] using hbroot

lemma gpCollectGoalRoots_subset
    (g : Goal)
    (allObjects : List Obj) :
    ∀ b,
      b ∈ gpCollectGoalRoots g allObjects allObjects →
      b ∈ allObjects := by
  intro b hb
  exact
    (gpCollectGoalRoots_mem_iff
      g allObjects allObjects b).mp hb |>.1

lemma gpCollectGoalRoots_complete
    (g : Goal)
    (allObjects : List Obj) :
    ∀ b,
      GPGoalRoot g allObjects b →
      b ∈ gpCollectGoalRoots g allObjects allObjects := by
  intro b hb
  apply
    (gpCollectGoalRoots_mem_iff
      g allObjects allObjects b).mpr
  simpa [GPGoalRoot] using hb

/-!
## Build-candidate specifications
-/

lemma gpFindBuildCandidate_some
    (g : Goal)
    (allObjects processed candidates : List Obj)
    (b a : Obj)
    (h :
      gpFindBuildCandidate
        g allObjects processed candidates = some (b, a)) :
    b ∈ candidates ∧
    b ∉ processed ∧
    a ∈ allObjects ∧
    a ∈ processed ∧
    g.dynamic.on_p b a = some true := by
  induction candidates with
  | nil =>
      simp [gpFindBuildCandidate] at h
  | cons c rest ih =>
      by_cases hc : c ∈ processed
      · have hrest :
            gpFindBuildCandidate
              g allObjects processed rest = some (b, a) := by
          simpa [gpFindBuildCandidate, hc] using h
        rcases ih hrest with
          ⟨hbmem, hbNotProcessed, haMem, haProcessed, hgoal⟩
        exact
          ⟨List.mem_cons_of_mem c hbmem,
           hbNotProcessed,
           haMem,
           haProcessed,
           hgoal⟩
      · cases hs : gpFindGoalSupport c g allObjects with
        | none =>
            have hrest :
                gpFindBuildCandidate
                  g allObjects processed rest = some (b, a) := by
              simpa [gpFindBuildCandidate, hc, hs] using h
            rcases ih hrest with
              ⟨hbmem, hbNotProcessed, haMem, haProcessed, hgoal⟩
            exact
              ⟨List.mem_cons_of_mem c hbmem,
               hbNotProcessed,
               haMem,
               haProcessed,
               hgoal⟩
        | some d =>
            by_cases hd : d ∈ processed
            · have hp : (c, d) = (b, a) := by
                simpa [gpFindBuildCandidate, hc, hs, hd] using h
              have hcb : c = b := congrArg Prod.fst hp
              have hda : d = a := congrArg Prod.snd hp
              subst b
              subst a
              rcases
                  gpFindGoalSupport_some
                    c g allObjects d hs with
                ⟨hdmem, hgoal⟩
              exact
                ⟨by simp,
                 hc,
                 hdmem,
                 hd,
                 hgoal⟩
            · have hrest :
                  gpFindBuildCandidate
                    g allObjects processed rest = some (b, a) := by
                simpa [gpFindBuildCandidate, hc, hs, hd] using h
              rcases ih hrest with
                ⟨hbmem, hbNotProcessed, haMem, haProcessed, hgoal⟩
              exact
                ⟨List.mem_cons_of_mem c hbmem,
                 hbNotProcessed,
                 haMem,
                 haProcessed,
                 hgoal⟩

lemma gpFindBuildCandidate_none
    (g : Goal)
    (allObjects processed candidates : List Obj)
    (h :
      gpFindBuildCandidate
        g allObjects processed candidates = none) :
    ∀ b a,
      b ∈ candidates →
      b ∉ processed →
      gpFindGoalSupport b g allObjects = some a →
      a ∈ processed →
      False := by
  induction candidates with
  | nil =>
      intro b a hb
      simp at hb
  | cons c rest ih =>
      by_cases hc : c ∈ processed
      · have hrest :
            gpFindBuildCandidate
              g allObjects processed rest = none := by
          simpa [gpFindBuildCandidate, hc] using h
        intro b a hb hbNotProcessed hsupport haProcessed
        have hbCases : b = c ∨ b ∈ rest := by
          simpa only [List.mem_cons] using hb
        rcases hbCases with hbc | hbRest
        · subst b
          exact hbNotProcessed hc
        · exact
            ih hrest b a hbRest hbNotProcessed
              hsupport haProcessed
      · cases hs : gpFindGoalSupport c g allObjects with
        | none =>
            have hrest :
                gpFindBuildCandidate
                  g allObjects processed rest = none := by
              simpa [gpFindBuildCandidate, hc, hs] using h
            intro b a hb hbNotProcessed hsupport haProcessed
            have hbCases : b = c ∨ b ∈ rest := by
              simpa only [List.mem_cons] using hb
            rcases hbCases with hbc | hbRest
            · subst b
              simp [hs] at hsupport
            · exact
                ih hrest b a hbRest hbNotProcessed
                  hsupport haProcessed
        | some d =>
            by_cases hd : d ∈ processed
            · simp [gpFindBuildCandidate, hc, hs, hd] at h
            · have hrest :
                  gpFindBuildCandidate
                    g allObjects processed rest = none := by
                simpa [gpFindBuildCandidate, hc, hs, hd] using h
              intro b a hb hbNotProcessed hsupport haProcessed
              have hbCases : b = c ∨ b ∈ rest := by
                simpa only [List.mem_cons] using hb
              rcases hbCases with hbc | hbRest
              · subst b
                have hda : d = a :=
                  Option.some.inj (hs.symm.trans hsupport)
                subst a
                exact hd haProcessed
              · exact
                  ih hrest b a hbRest hbNotProcessed
                    hsupport haProcessed

/-!
## Finite goal-graph/topological lemmas
-/

lemma wfGoal_on_mem
    (initial : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (b a : Obj)
    (h : g.dynamic.on_p b a = some true) :
    b ∈ initial.statics.objects ∧
    a ∈ initial.statics.objects := by
  have hon : ValidOnParam initial.statics g.dynamic :=
    hgoal.2.2.2.2.1
  exact hon b a h

lemma gp_transGen_reverse
    {α : Type}
    {r : α → α → Prop}
    {a b : α}
    (h :
      Relation.TransGen (fun x y => r y x) a b) :
    Relation.TransGen r b a := by
  induction h with
  | single hab =>
      exact Relation.TransGen.single hab
  | @tail c d _ hcd ih =>
      exact gp_rt_prepend_to_transGen hcd (tg_to_rt ih)

lemma gp_rt_reverse
    {α : Type}
    {r : α → α → Prop}
    {a b : α}
    (h :
      Relation.ReflTransGen (fun x y => r y x) a b) :
    Relation.ReflTransGen r b a := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
      have hdc :
          Relation.ReflTransGen r d c :=
        Relation.ReflTransGen.tail
          Relation.ReflTransGen.refl hcd
      exact rt_trans hdc ih

lemma gp_rt_has_frontier
    {α : Type}
    {r : α → α → Prop}
    {P : α → Prop}
    {x z : α}
    (hpath : Relation.ReflTransGen r x z) :
    (¬ P x) →
    P z →
    ∃ b a, r b a ∧ ¬ P b ∧ P a := by
  induction hpath with
  | refl =>
      intro hx hz
      exact False.elim (hx hz)
  | @tail b c _ hbc ih =>
      intro hx hc
      by_cases hb : P b
      · exact ih hx hb
      · exact ⟨b, c, hbc, hb, hc⟩

lemma goal_frontier_exists
    (initial : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (processed : List Obj)
    (hsubset :
      ∀ b, b ∈ processed →
        b ∈ initial.statics.objects)
    (hroots :
      ∀ b,
        GPGoalRoot g initial.statics.objects b →
        b ∈ processed)
    (hmissing :
      ∃ b,
        b ∈ initial.statics.objects ∧
        b ∉ processed) :
    ∃ b a,
      b ∈ initial.statics.objects ∧
      b ∉ processed ∧
      a ∈ processed ∧
      g.dynamic.on_p b a = some true := by
  rcases hmissing with ⟨x, hxMem, hxNotProcessed⟩

  have hvalidRev :
      ∀ a b,
        g.dynamic.on_p b a = some true →
          a ∈ initial.statics.objects ∧
          b ∈ initial.statics.objects := by
    intro a b hba
    have hmem := wfGoal_on_mem initial g hgoal b a hba
    exact ⟨hmem.2, hmem.1⟩

  have hNoCyclesRaw :
      NoOnCycles initial.statics g.dynamic :=
    hgoal.2.2.2.2.2.2.2.1

  have hcyclesGoal :
      ∀ a,
        ¬ Relation.TransGen
          (fun x y =>
            g.dynamic.on_p x y = some true) a a := by
    intro a hcycle
    apply hNoCyclesRaw a
    apply transGen_mono
      (fun x y hxy => by
        change g.dynamic.on_p x y = some true
        exact hxy)
      hcycle

  have hcyclesRev :
      ∀ a,
        ¬ Relation.TransGen
          (fun x y =>
            g.dynamic.on_p y x = some true) a a := by
    intro a hcycle
    apply hcyclesGoal a
    exact gp_transGen_reverse hcycle

  rcases
      gp_finite_acyclic_has_source
        (fun a b => g.dynamic.on_p b a = some true)
        initial.statics.objects
        hvalidRev
        hcyclesRev
        x
        hxMem with
    ⟨root, hrootMem, hrootToXRev, hrootNoOut⟩

  have hrootSupportNone :
      gpFindGoalSupport
        root g initial.statics.objects = none := by
    cases hfind :
        gpFindGoalSupport
          root g initial.statics.objects with
    | none =>
        rfl
    | some a =>
        rcases
            gpFindGoalSupport_some
              root g initial.statics.objects a hfind with
          ⟨_, hrootOnA⟩
        exact False.elim (hrootNoOut a hrootOnA)

  have hrootProcessed : root ∈ processed := by
    apply hroots root
    exact ⟨hrootMem, hrootSupportNone⟩

  have hpath :
      Relation.ReflTransGen
        (fun b a =>
          g.dynamic.on_p b a = some true)
        x root :=
    gp_rt_reverse hrootToXRev

  rcases
      gp_rt_has_frontier
        (P := fun b => b ∈ processed)
        hpath
        hxNotProcessed
        hrootProcessed with
    ⟨b, a, hba, hbNotProcessed, haProcessed⟩

  have hbMem :
      b ∈ initial.statics.objects :=
    (wfGoal_on_mem initial g hgoal b a hba).1

  exact
    ⟨b, a, hbMem, hbNotProcessed, haProcessed, hba⟩

lemma gpFindBuildCandidate_complete
    (initial : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (processed : List Obj)
    (hsubset :
      ∀ b, b ∈ processed →
        b ∈ initial.statics.objects)
    (hroots :
      ∀ b,
        GPGoalRoot g initial.statics.objects b →
        b ∈ processed)
    (hmissing :
      ∃ b,
        b ∈ initial.statics.objects ∧
        b ∉ processed) :
    ∃ b a,
      gpFindBuildCandidate
        g
        initial.statics.objects
        processed
        initial.statics.objects = some (b, a) := by
  rcases
      goal_frontier_exists
        initial g hgoal processed hsubset hroots hmissing with
    ⟨b, a, hbMem, hbNotProcessed, haProcessed, hba⟩

  have haMem : a ∈ initial.statics.objects :=
    (wfGoal_on_mem initial g hgoal b a hba).2

  rcases
      gpFindGoalSupport_complete
        b g initial.statics.objects a haMem hba with
    ⟨a', hsupport⟩

  rcases
      gpFindGoalSupport_some
        b g initial.statics.objects a' hsupport with
    ⟨_, hba'⟩

  have hbelow :
      OnUniqueBelow initial.statics g.dynamic :=
    hgoal.2.2.2.2.2.1

  have haEq : a' = a :=
    hbelow b a' a hba' hba

  have ha'Processed : a' ∈ processed := by
    simpa [haEq] using haProcessed

  cases hfind :
      gpFindBuildCandidate
        g
        initial.statics.objects
        processed
        initial.statics.objects with
  | none =>
      exact False.elim
        (gpFindBuildCandidate_none
          g
          initial.statics.objects
          processed
          initial.statics.objects
          hfind
          b
          a'
          hbMem
          hbNotProcessed
          hsupport
          ha'Processed)
  | some candidate =>
      rcases candidate with ⟨b', a''⟩
      exact ⟨b', a'', rfl⟩

/-!
## Build invariant initialization and preservation
-/

lemma gpBuild_initial_inv
    (initial : State)
    (g : Goal)
    (s : State)
    (hgoal : WellFormedGoal initial g)
    (hflat : GPFlat initial.statics.objects s) :
    let roots :=
      gpCollectGoalRoots
        g initial.statics.objects initial.statics.objects
    GPBuildInv initial.statics.objects g roots s ∧
    (∀ b, b ∈ roots →
      b ∈ initial.statics.objects) ∧
    (∀ b,
      GPGoalRoot g initial.statics.objects b →
      b ∈ roots) ∧
    gpUnprocessedCount initial.statics.objects roots ≤
      initial.statics.objects.length := by
  let roots :=
    gpCollectGoalRoots
      g initial.statics.objects initial.statics.objects

  change
    GPBuildInv initial.statics.objects g roots s ∧
    (∀ b, b ∈ roots → b ∈ initial.statics.objects) ∧
    (∀ b,
      GPGoalRoot g initial.statics.objects b → b ∈ roots) ∧
    gpUnprocessedCount initial.statics.objects roots ≤
      initial.statics.objects.length

  rcases hflat with
    ⟨hstatics, harm, hholding, hallOn, hflatObjects⟩

  have hsubset :
      ∀ b, b ∈ roots → b ∈ initial.statics.objects := by
    intro b hb
    apply gpCollectGoalRoots_subset
      g initial.statics.objects b
    simpa only [roots] using hb

  have hroots :
      ∀ b,
        GPGoalRoot g initial.statics.objects b →
        b ∈ roots := by
    intro b hb
    have hmem :=
      gpCollectGoalRoots_complete
        g initial.statics.objects b hb
    simpa only [roots] using hmem

  have hinv :
      GPBuildInv initial.statics.objects g roots s := by
    refine
      ⟨hstatics, harm, hholding, ?_, ?_, ?_⟩

    · intro b hbMem _
      exact hflatObjects b hbMem

    · intro x y
      constructor
      · intro hxy
        have hfalse : s.dynamic.on_p x y = false :=
          hallOn x y
        simp [hfalse] at hxy
      · rintro ⟨hxRoot, hxyGoal⟩
        have hxRoot' :
            x ∈ gpCollectGoalRoots
              g initial.statics.objects
                initial.statics.objects := by
          simpa only [roots] using hxRoot
        have hxNone :
            gpFindGoalSupport
              x g initial.statics.objects = none :=
          (gpCollectGoalRoots_mem_iff
            g
            initial.statics.objects
            initial.statics.objects
            x).mp hxRoot' |>.2
        have hyMem :
            y ∈ initial.statics.objects :=
          (wfGoal_on_mem
            initial g hgoal x y hxyGoal).2
        have hnot :=
          gpFindGoalSupport_none
            x g initial.statics.objects hxNone y hyMem
        exact False.elim (hnot hxyGoal)

    · intro y hyMem
      constructor
      · intro _
        rintro ⟨x, hxRoot, hxyGoal⟩
        have hxRoot' :
            x ∈ gpCollectGoalRoots
              g initial.statics.objects
                initial.statics.objects := by
          simpa only [roots] using hxRoot
        have hxNone :
            gpFindGoalSupport
              x g initial.statics.objects = none :=
          (gpCollectGoalRoots_mem_iff
            g
            initial.statics.objects
            initial.statics.objects
            x).mp hxRoot' |>.2
        exact
          (gpFindGoalSupport_none
            x g initial.statics.objects hxNone y hyMem)
            hxyGoal
      · intro _
        exact (hflatObjects y hyMem).1

  have hcount :
      gpUnprocessedCount initial.statics.objects roots ≤
        initial.statics.objects.length := by
    unfold gpUnprocessedCount
    have haux :
        ∀ objects : List Obj,
          (objects.filter (fun b => b ∉ roots)).length ≤
            objects.length := by
      intro objects
      induction objects with
      | nil =>
          simp
      | cons b rest ih =>
          by_cases hb : b ∈ roots
          · have hle :
                (rest.filter (fun x => x ∉ roots)).length ≤
                  Nat.succ rest.length :=
              Nat.le_trans ih (Nat.le_succ rest.length)
            simpa [hb] using hle
          · simpa [hb] using Nat.succ_le_succ ih
    exact haux initial.statics.objects

  exact ⟨hinv, hsubset, hroots, hcount⟩

lemma gpBuild_step_correct
    (initial : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (processed : List Obj)
    (s : State)
    (b a : Obj)
    (hinv :
      GPBuildInv initial.statics.objects g processed s)
    (hcandidate :
      gpFindBuildCandidate
        g
        initial.statics.objects
        processed
        initial.statics.objects = some (b, a)) :
    ValidPlan
      [PlanAction.pickup b, PlanAction.stack b a] s ∧
    GPBuildInv
      initial.statics.objects
      g
      (b :: processed)
      (stack b a (pickup b s)) := by
  rcases hinv with
    ⟨hstatics, harm, hholding, hflatObjects, honIff,
      hclearIff⟩

  rcases
      gpFindBuildCandidate_some
        g
        initial.statics.objects
        processed
        initial.statics.objects
        b
        a
        hcandidate with
    ⟨hbMem, hbNotProcessed, haMem, haProcessed, hbaGoal⟩

  have hbelow :
      OnUniqueBelow initial.statics g.dynamic :=
    hgoal.2.2.2.2.2.1

  have habove :
      OnUniqueAbove initial.statics g.dynamic :=
    hgoal.2.2.2.2.2.2.1

  have hcycles :
      NoOnCycles initial.statics g.dynamic :=
    hgoal.2.2.2.2.2.2.2.1

  have hba : b ≠ a := by
    intro h
    subst a
    exact hbNotProcessed haProcessed

  have hab : a ≠ b :=
    Ne.symm hba

  have hbMemS : b ∈ s.statics.objects := by
    rw [hstatics]
    exact hbMem

  have haMemS : a ∈ s.statics.objects := by
    rw [hstatics]
    exact haMem

  have hbFlat :
      s.dynamic.clear_p b = true ∧
      s.dynamic.on_table_p b = true :=
    hflatObjects b hbMem hbNotProcessed

  have hclearA : s.dynamic.clear_p a = true := by
    apply (hclearIff a haMem).2
    rintro ⟨x, hxProcessed, hxaGoal⟩
    have hxb : x = b :=
      habove x b a hxaGoal hbaGoal
    subst x
    exact hbNotProcessed hxProcessed

  have hpickupPre : pickupPre b s :=
    ⟨hbMemS, hbFlat.1, hbFlat.2, harm⟩

  have hbMemPickup :
      b ∈ (pickup b s).statics.objects := by
    rw [pickup_statics]
    exact hbMemS

  have haMemPickup :
      a ∈ (pickup b s).statics.objects := by
    rw [pickup_statics]
    exact haMemS

  have hclearAPickup :
      (pickup b s).dynamic.clear_p a = true := by
    calc
      (pickup b s).dynamic.clear_p a =
          s.dynamic.clear_p a :=
        pickup_clear_p_ne b s hab
      _ = true := hclearA

  have hstackPre : stackPre b a (pickup b s) :=
    ⟨hbMemPickup,
     haMemPickup,
     hclearAPickup,
     pickup_holding_p_eq1 b s⟩

  have hvalid :
      ValidPlan
        [PlanAction.pickup b, PlanAction.stack b a] s := by
    simp only [ValidPlan, actionPre, actionApply]
    exact ⟨hpickupPre, hstackPre, True.intro⟩

  have hstaticsNew :
      (stack b a (pickup b s)).statics.objects =
        initial.statics.objects := by
    calc
      (stack b a (pickup b s)).statics.objects =
          (pickup b s).statics.objects :=
        congrArg StaticState.objects
          (stack_statics b a (pickup b s))
      _ = s.statics.objects :=
        congrArg StaticState.objects
          (pickup_statics b s)
      _ = initial.statics.objects :=
        hstatics

  have harmNew :
      (stack b a (pickup b s)).dynamic.arm_empty_p = true :=
    stack_arm_empty_p b a (pickup b s)

  have hholdingNew :
      ∀ x,
        (stack b a (pickup b s)).dynamic.holding_p x = false := by
    intro x
    by_cases hxb : x = b
    · subst x
      exact stack_holding_p_eq1 b a (pickup b s)
    · calc
        (stack b a (pickup b s)).dynamic.holding_p x =
            (pickup b s).dynamic.holding_p x :=
          stack_holding_p_ne b a (pickup b s) hxb
        _ = s.dynamic.holding_p x :=
          pickup_holding_p_ne b s hxb
        _ = false :=
          hholding x

  have hunprocessedNew :
      ∀ x,
        x ∈ initial.statics.objects →
        x ∉ b :: processed →
        (stack b a (pickup b s)).dynamic.clear_p x = true ∧
        (stack b a (pickup b s)).dynamic.on_table_p x = true := by
    intro x hxMem hxNotProcessedNew

    have hxb : x ≠ b := by
      intro h
      subst x
      exact hxNotProcessedNew (by simp)

    have hxNotProcessed : x ∉ processed := by
      intro hxProcessed
      exact hxNotProcessedNew
        (List.mem_cons_of_mem b hxProcessed)

    have hxa : x ≠ a := by
      intro h
      subst x
      exact hxNotProcessed haProcessed

    rcases hflatObjects x hxMem hxNotProcessed with
      ⟨hxClear, hxTable⟩

    constructor
    · calc
        (stack b a (pickup b s)).dynamic.clear_p x =
            (pickup b s).dynamic.clear_p x :=
          stack_clear_p_ne b a (pickup b s) hxb hxa
        _ = s.dynamic.clear_p x :=
          pickup_clear_p_ne b s hxb
        _ = true :=
          hxClear
    · calc
        (stack b a (pickup b s)).dynamic.on_table_p x =
            (pickup b s).dynamic.on_table_p x :=
          congrFun (stack_on_table_p b a (pickup b s)) x
        _ = s.dynamic.on_table_p x :=
          pickup_on_table_p_ne b s hxb
        _ = true :=
          hxTable

  have honNew :
      ∀ x y,
        (stack b a (pickup b s)).dynamic.on_p x y = true ↔
          x ∈ b :: processed ∧
          g.dynamic.on_p x y = some true := by
    intro x y
    constructor
    · intro hxyNew
      by_cases hxb : x = b
      · subst x
        refine ⟨by simp, ?_⟩
        by_cases hya : y = a
        · subst y
          exact hbaGoal
        · have hxyOld :
              s.dynamic.on_p b y = true := by
            calc
              s.dynamic.on_p b y =
                  (pickup b s).dynamic.on_p b y := by
                symm
                exact
                  congrFun
                    (congrFun (pickup_on_p b s) b)
                    y
              _ =
                  (stack b a (pickup b s)).dynamic.on_p b y := by
                symm
                exact
                  stack_on_p_ne_var_y
                    b a (pickup b s) hya
              _ = true :=
                hxyNew
          have hbProcessed :=
            (honIff b y).1 hxyOld |>.1
          exact False.elim (hbNotProcessed hbProcessed)
      · have hxyOld :
            s.dynamic.on_p x y = true := by
          calc
            s.dynamic.on_p x y =
                (pickup b s).dynamic.on_p x y := by
              symm
              exact
                congrFun
                  (congrFun (pickup_on_p b s) x)
                  y
            _ =
                (stack b a (pickup b s)).dynamic.on_p x y := by
              symm
              exact
                stack_on_p_ne b a (pickup b s) hxb
            _ = true :=
              hxyNew
        rcases (honIff x y).1 hxyOld with
          ⟨hxProcessed, hxyGoal⟩
        exact
          ⟨List.mem_cons_of_mem b hxProcessed, hxyGoal⟩

    · rintro ⟨hxNewProcessed, hxyGoal⟩
      rcases List.mem_cons.mp hxNewProcessed with
        hxb | hxProcessed
      · subst x
        have hya : y = a :=
          hbelow b y a hxyGoal hbaGoal
        subst y
        exact stack_on_p_eq1 b a (pickup b s)
      · have hxb : x ≠ b := by
          intro h
          subst x
          exact hbNotProcessed hxProcessed

        have hxyOld :
            s.dynamic.on_p x y = true :=
          (honIff x y).2 ⟨hxProcessed, hxyGoal⟩

        calc
          (stack b a (pickup b s)).dynamic.on_p x y =
              (pickup b s).dynamic.on_p x y :=
            stack_on_p_ne b a (pickup b s) hxb
          _ = s.dynamic.on_p x y :=
            congrFun
              (congrFun (pickup_on_p b s) x)
              y
          _ = true :=
            hxyOld

  have hclearNew :
      ∀ y,
        y ∈ initial.statics.objects →
        ((stack b a (pickup b s)).dynamic.clear_p y = true ↔
          ¬ ∃ x,
            x ∈ b :: processed ∧
            g.dynamic.on_p x y = some true) := by
    intro y hyMem

    by_cases hya : y = a
    · subst y
      constructor
      · intro hclear
        have hfalse :
            (stack b a (pickup b s)).dynamic.clear_p a = false :=
          stack_clear_p_eq2 b a (pickup b s) hab
        have : False := by
          rw [hfalse] at hclear
          simp at hclear
        exact this.elim
      · intro hnone
        exact False.elim
          (hnone ⟨b, by simp, hbaGoal⟩)

    · by_cases hyb : y = b
      · subst y
        constructor
        · intro _
          rintro ⟨x, hxNewProcessed, hxbGoal⟩
          rcases List.mem_cons.mp hxNewProcessed with
            hxb | hxProcessed
          · subst x
            exact
              hcycles b
                (Relation.TransGen.single hxbGoal)
          · have hbClearOld :
                s.dynamic.clear_p b = true :=
              (hflatObjects b hbMem hbNotProcessed).1
            have hnoneOld :=
              (hclearIff b hbMem).1 hbClearOld
            exact hnoneOld
              ⟨x, hxProcessed, hxbGoal⟩
        · intro _
          exact stack_clear_p_eq1 b a (pickup b s)

      · have hclearEq :
            (stack b a (pickup b s)).dynamic.clear_p y =
              s.dynamic.clear_p y := by
          calc
            (stack b a (pickup b s)).dynamic.clear_p y =
                (pickup b s).dynamic.clear_p y :=
              stack_clear_p_ne b a (pickup b s) hyb hya
            _ = s.dynamic.clear_p y :=
              pickup_clear_p_ne b s hyb

        constructor
        · intro hclear
          have hclearOld :
              s.dynamic.clear_p y = true := by
            calc
              s.dynamic.clear_p y =
                  (stack b a (pickup b s)).dynamic.clear_p y :=
                hclearEq.symm
              _ = true :=
                hclear

          have hnoneOld :=
            (hclearIff y hyMem).1 hclearOld

          rintro ⟨x, hxNewProcessed, hxyGoal⟩
          rcases List.mem_cons.mp hxNewProcessed with
            hxb | hxProcessed
          · subst x
            have hya' : y = a :=
              hbelow b y a hxyGoal hbaGoal
            exact hya hya'
          · exact hnoneOld
              ⟨x, hxProcessed, hxyGoal⟩

        · intro hnoneNew
          have hnoneOld :
              ¬ ∃ x,
                x ∈ processed ∧
                g.dynamic.on_p x y = some true := by
            rintro ⟨x, hxProcessed, hxyGoal⟩
            exact hnoneNew
              ⟨x, List.mem_cons_of_mem b hxProcessed, hxyGoal⟩

          have hclearOld :
              s.dynamic.clear_p y = true :=
            (hclearIff y hyMem).2 hnoneOld

          calc
            (stack b a (pickup b s)).dynamic.clear_p y =
                s.dynamic.clear_p y :=
              hclearEq
            _ = true :=
              hclearOld

  refine ⟨hvalid, ?_⟩
  exact
    ⟨hstaticsNew,
     harmNew,
     hholdingNew,
     hunprocessedNew,
     honNew,
     hclearNew⟩

lemma gpUnprocessedCount_cons_lt
    (allObjects processed : List Obj)
    (b : Obj)
    (hbmem : b ∈ allObjects)
    (hbnot : b ∉ processed) :
    gpUnprocessedCount allObjects (b :: processed) <
      gpUnprocessedCount allObjects processed := by
  unfold gpUnprocessedCount

  have h :=
    gp_filter_false_length_lt_of_removed
      allObjects
      (fun x : Obj => decide (x ∈ processed))
      (fun x : Obj => decide (x ∈ b :: processed))
      b
      hbmem
      (by simp [hbnot])
      (by simp)
      (by
        intro x hxb
        simp [hxb])

  simpa using h

lemma gpUnprocessedCount_le_length
    (allObjects processed : List Obj) :
    gpUnprocessedCount allObjects processed ≤
      allObjects.length := by
  unfold gpUnprocessedCount
  induction allObjects with
  | nil =>
      simp
  | cons b rest ih =>
      by_cases hb : b ∈ processed
      · have hle :
            (rest.filter (fun x => x ∉ processed)).length ≤
              Nat.succ rest.length :=
          Nat.le_trans ih (Nat.le_succ rest.length)
        simpa [hb] using hle
      · simpa [hb] using Nat.succ_le_succ ih

/-!
## Correctness of the goal-building phase
-/

lemma gpUnprocessedCount_eq_zero_all_processed
    (allObjects processed : List Obj)
    (hzero :
      gpUnprocessedCount allObjects processed = 0) :
    ∀ b, b ∈ allObjects → b ∈ processed := by
  have aux :
      ∀ xs : List Obj,
        (xs.filter (fun b => b ∉ processed)).length = 0 →
        ∀ b, b ∈ xs → b ∈ processed := by
    intro xs
    induction xs with
    | nil =>
        intro _ b hb
        simp at hb
    | cons x xs ih =>
        intro hz
        by_cases hx : x ∈ processed
        · have hzRest :
              (xs.filter (fun b => b ∉ processed)).length = 0 := by
            simpa [hx] using hz
          intro b hb
          rcases List.mem_cons.mp hb with hbx | hbxs
          · subst b
            exact hx
          · exact ih hzRest b hbxs
        · exfalso
          simpa [hx] using hz

  apply aux allObjects
  simpa [gpUnprocessedCount] using hzero

lemma gpBuildGoalAux_correct
    (initial : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (fuel processed : List Obj)
    (s : State)
    (hinv :
      GPBuildInv initial.statics.objects g processed s)
    (hsubset :
      ∀ b, b ∈ processed →
        b ∈ initial.statics.objects)
    (hroots :
      ∀ b,
        GPGoalRoot g initial.statics.objects b →
        b ∈ processed)
    (hbound :
      gpUnprocessedCount
        initial.statics.objects processed ≤ fuel.length) :
    let plan :=
      gpBuildGoalAux
        initial.statics.objects g fuel processed
    ValidPlan plan s ∧
    ∃ finalProcessed,
      (∀ b, b ∈ processed → b ∈ finalProcessed) ∧
      (∀ b, b ∈ finalProcessed →
        b ∈ initial.statics.objects) ∧
      (∀ b, b ∈ initial.statics.objects →
        b ∈ finalProcessed) ∧
      GPBuildInv
        initial.statics.objects
        g
        finalProcessed
        (runPlan plan s) := by
  dsimp only
  induction fuel generalizing processed s with
  | nil =>
      have hzero :
          gpUnprocessedCount
            initial.statics.objects processed = 0 := by
        have hle :
            gpUnprocessedCount
              initial.statics.objects processed ≤ 0 := by
          simpa using hbound
        omega

      have hallProcessed :
          ∀ b, b ∈ initial.statics.objects → b ∈ processed :=
        gpUnprocessedCount_eq_zero_all_processed
          initial.statics.objects processed hzero

      refine ⟨?_, processed, ?_, ?_, ?_, ?_⟩
      · simp [gpBuildGoalAux, ValidPlan]
      · intro b hb
        exact hb
      · exact hsubset
      · exact hallProcessed
      · simpa [gpBuildGoalAux, runPlan] using hinv

  | cons f fuel ih =>
      cases hfind :
          gpFindBuildCandidate
            g
            initial.statics.objects
            processed
            initial.statics.objects with
      | none =>
          have hallProcessed :
              ∀ b,
                b ∈ initial.statics.objects →
                b ∈ processed := by
            intro b hbMem
            by_contra hbNotProcessed
            rcases
                gpFindBuildCandidate_complete
                  initial
                  g
                  hgoal
                  processed
                  hsubset
                  hroots
                  ⟨b, hbMem, hbNotProcessed⟩ with
              ⟨b', a', hfound⟩
            rw [hfind] at hfound
            simp at hfound

          refine ⟨?_, processed, ?_, ?_, ?_, ?_⟩
          · simp [gpBuildGoalAux, hfind, ValidPlan]
          · intro b hb
            exact hb
          · exact hsubset
          · exact hallProcessed
          · simpa [gpBuildGoalAux, hfind, runPlan] using hinv

      | some candidate =>
          rcases candidate with ⟨b, a⟩

          rcases
              gpFindBuildCandidate_some
                g
                initial.statics.objects
                processed
                initial.statics.objects
                b
                a
                hfind with
            ⟨hbMem, hbNotProcessed, _, _, _⟩

          rcases
              gpBuild_step_correct
                initial
                g
                hgoal
                processed
                s
                b
                a
                hinv
                hfind with
            ⟨hvalidStep, hinvNext⟩

          have hsubsetNext :
              ∀ x,
                x ∈ b :: processed →
                x ∈ initial.statics.objects := by
            intro x hx
            rcases List.mem_cons.mp hx with hxb | hxProcessed
            · subst x
              exact hbMem
            · exact hsubset x hxProcessed

          have hrootsNext :
              ∀ x,
                GPGoalRoot
                    g initial.statics.objects x →
                  x ∈ b :: processed := by
            intro x hxRoot
            exact
              List.mem_cons_of_mem b
                (hroots x hxRoot)

          have hdecrease :
              gpUnprocessedCount
                  initial.statics.objects
                  (b :: processed) <
                gpUnprocessedCount
                  initial.statics.objects
                  processed :=
            gpUnprocessedCount_cons_lt
              initial.statics.objects
              processed
              b
              hbMem
              hbNotProcessed

          have hboundCurrent :
              gpUnprocessedCount
                  initial.statics.objects
                  processed ≤
                Nat.succ fuel.length := by
            simpa using hbound

          have hboundNext :
              gpUnprocessedCount
                  initial.statics.objects
                  (b :: processed) ≤
                fuel.length := by
            omega

          rcases
              ih
                (processed := b :: processed)
                (s := stack b a (pickup b s))
                hinvNext
                hsubsetNext
                hrootsNext
                hboundNext with
            ⟨hvalidRest,
             finalProcessed,
             hprocessedMono,
             hfinalSubset,
             hfinalComplete,
             hfinalInv⟩

          have hstepRun :
              runPlan
                  [PlanAction.pickup b,
                   PlanAction.stack b a]
                  s =
                stack b a (pickup b s) := by
            rfl

          have hvalidAll :
              ValidPlan
                ([PlanAction.pickup b,
                  PlanAction.stack b a] ++
                  gpBuildGoalAux
                    initial.statics.objects
                    g
                    fuel
                    (b :: processed))
                s := by
            apply
              (validPlan_append
                [PlanAction.pickup b,
                 PlanAction.stack b a]
                (gpBuildGoalAux
                  initial.statics.objects
                  g
                  fuel
                  (b :: processed))
                s).2
            refine ⟨hvalidStep, ?_⟩
            rw [hstepRun]
            exact hvalidRest

          have hrunAll :
              runPlan
                  ([PlanAction.pickup b,
                    PlanAction.stack b a] ++
                    gpBuildGoalAux
                      initial.statics.objects
                      g
                      fuel
                      (b :: processed))
                  s =
                runPlan
                  (gpBuildGoalAux
                    initial.statics.objects
                    g
                    fuel
                    (b :: processed))
                  (stack b a (pickup b s)) := by
            rw [runPlan_append, hstepRun]

          have hplan :
              gpBuildGoalAux
                  initial.statics.objects
                  g
                  (f :: fuel)
                  processed =
                [PlanAction.pickup b,
                 PlanAction.stack b a] ++
                  gpBuildGoalAux
                    initial.statics.objects
                    g
                    fuel
                    (b :: processed) := by
            simp [gpBuildGoalAux, hfind]

          rw [hplan]
          refine
            ⟨hvalidAll,
             finalProcessed,
             ?_,
             hfinalSubset,
             hfinalComplete,
             ?_⟩
          · intro x hxProcessed
            apply hprocessedMono
            exact List.mem_cons_of_mem b hxProcessed
          · rw [hrunAll]
            exact hfinalInv

lemma satisfiesGoal_of_positive_on
    (initial : State)
    (g : Goal)
    (s : State)
    (hgoal : WellFormedGoal initial g)
    (hon :
      ∀ x y,
        g.dynamic.on_p x y = some true →
        s.dynamic.on_p x y = true) :
    SatisfiesGoal s g := by
  rcases hgoal with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _,
     hignoreClear, hignoreTable, hignoreArm,
     hignoreHolding, hpositive, _⟩

  unfold GoalIgnoreClear at hignoreClear
  unfold GoalIgnoreOnTable at hignoreTable
  unfold GoalIgnoreArmEmpty at hignoreArm
  unfold GoalIgnoreHolding at hignoreHolding
  unfold GoalOnOnlyPositive at hpositive

  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [hignoreClear x]
  · intro x
    simp [hignoreTable x]
  · simp [hignoreArm]
  · intro x
    simp [hignoreHolding x]
  · intro x y
    cases hxy : g.dynamic.on_p x y with
    | none =>
        simp
    | some b =>
        cases b with
        | false =>
            exact False.elim ((hpositive x y) hxy)
        | true =>
            simpa [hxy] using hon x y hxy

lemma gpBuildGoal_correct
    (initial : State)
    (g : Goal)
    (s : State)
    (hgoal : WellFormedGoal initial g)
    (hflat : GPFlat initial.statics.objects s) :
    let roots :=
      gpCollectGoalRoots
        g initial.statics.objects initial.statics.objects
    let plan :=
      gpBuildGoalAux
        initial.statics.objects
        g
        initial.statics.objects
        roots
    ValidPlan plan s ∧
    SatisfiesGoal (runPlan plan s) g := by
  let roots :=
    gpCollectGoalRoots
      g initial.statics.objects initial.statics.objects
  let plan :=
    gpBuildGoalAux
      initial.statics.objects
      g
      initial.statics.objects
      roots

  change
    ValidPlan plan s ∧
    SatisfiesGoal (runPlan plan s) g

  have hinitial :
      GPBuildInv initial.statics.objects g roots s ∧
      (∀ b, b ∈ roots →
        b ∈ initial.statics.objects) ∧
      (∀ b,
        GPGoalRoot g initial.statics.objects b →
        b ∈ roots) ∧
      gpUnprocessedCount initial.statics.objects roots ≤
        initial.statics.objects.length := by
    simpa only [roots] using
      (gpBuild_initial_inv initial g s hgoal hflat)

  rcases hinitial with
    ⟨hinv, hsubset, hroots, hbound⟩

  have hbuild :
      ValidPlan plan s ∧
      ∃ finalProcessed,
        (∀ b, b ∈ roots → b ∈ finalProcessed) ∧
        (∀ b, b ∈ finalProcessed →
          b ∈ initial.statics.objects) ∧
        (∀ b, b ∈ initial.statics.objects →
          b ∈ finalProcessed) ∧
        GPBuildInv
          initial.statics.objects
          g
          finalProcessed
          (runPlan plan s) := by
    simpa only [plan] using
      (gpBuildGoalAux_correct
        initial
        g
        hgoal
        initial.statics.objects
        roots
        s
        hinv
        hsubset
        hroots
        hbound)

  rcases hbuild with
    ⟨hvalid,
     finalProcessed,
     _,
     _,
     hfinalComplete,
     hfinalInv⟩

  rcases hfinalInv with
    ⟨_, _, _, _, honFinal, _⟩

  have hon :
      ∀ x y,
        g.dynamic.on_p x y = some true →
        (runPlan plan s).dynamic.on_p x y = true := by
    intro x y hxy
    have hxMem :
        x ∈ initial.statics.objects :=
      (wfGoal_on_mem initial g hgoal x y hxy).1
    have hxProcessed :
        x ∈ finalProcessed :=
      hfinalComplete x hxMem
    exact
      (honFinal x y).2
        ⟨hxProcessed, hxy⟩

  exact
    ⟨hvalid,
     satisfiesGoal_of_positive_on
       initial g (runPlan plan s) hgoal hon⟩

-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  rcases hinit with ⟨hwf, harm⟩

  let objects := s.statics.objects
  let clearPlan := gpClearToTableAux objects s
  let afterClear := runPlan clearPlan s
  let roots := gpCollectGoalRoots g objects objects
  let buildPlan :=
    gpBuildGoalAux objects g objects roots

  have hclear :
      ValidPlan clearPlan s ∧
      WellFormed afterClear ∧
      GPFlat objects afterClear := by
    simpa only [objects, clearPlan, afterClear] using
      (gpClearToTable_correct s hstatic hwf harm)

  rcases hclear with
    ⟨hvalidClear, _, hflatAfter⟩

  have hbuild :
      ValidPlan buildPlan afterClear ∧
      SatisfiesGoal
        (runPlan buildPlan afterClear) g := by
    simpa only [objects, roots, buildPlan] using
      (gpBuildGoal_correct
        s g afterClear hgoal hflatAfter)

  rcases hbuild with
    ⟨hvalidBuild, hgoalAfterBuild⟩

  have hsolve :
      solve s g = clearPlan ++ buildPlan := by
    rfl

  rw [hsolve]
  constructor
  · exact
      (validPlan_append clearPlan buildPlan s).2
        ⟨hvalidClear, hvalidBuild⟩
  · rw [runPlan_append]
    simpa only [afterClear] using hgoalAfterBuild

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

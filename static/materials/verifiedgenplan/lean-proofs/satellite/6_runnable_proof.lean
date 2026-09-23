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
  on_board_p : Obj → Obj → Bool
  supports_p : Obj → Obj → Bool
  calibration_target_p : Obj → Obj → Bool
  satellite_t : Obj → Bool
  direction_t : Obj → Bool
  instrument_t : Obj → Bool
  mode_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  pointing_p : Obj → Obj → α
  power_avail_p : Obj → α
  power_on_p : Obj → α
  calibrated_p : Obj → α
  have_image_p : Obj → Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidOnBoardParam (s : StaticState) : Prop :=
  ∀ var_i var_s, s.on_board_p var_i var_s = true → s.instrument_t var_i = true ∧ s.satellite_t var_s = true

def ValidSupportsParam (s : StaticState) : Prop :=
  ∀ var_i var_m, s.supports_p var_i var_m = true → s.instrument_t var_i = true ∧ s.mode_t var_m = true

def ValidCalibrationTargetParam (s : StaticState) : Prop :=
  ∀ var_i var_d, s.calibration_target_p var_i var_d = true → s.instrument_t var_i = true ∧ s.direction_t var_d = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.satellite_t x = true → x ∈ s.objects) ∧
  (∀ x, s.direction_t x = true → x ∈ s.objects) ∧
  (∀ x, s.instrument_t x = true → x ∈ s.objects) ∧
  (∀ x, s.mode_t x = true → x ∈ s.objects) ∧
  (∀ x, s.satellite_t x = true → s.direction_t x = false) ∧
  (∀ x, s.satellite_t x = true → s.instrument_t x = false) ∧
  (∀ x, s.satellite_t x = true → s.mode_t x = false) ∧
  (∀ x, s.direction_t x = true → s.instrument_t x = false) ∧
  (∀ x, s.direction_t x = true → s.mode_t x = false) ∧
  (∀ x, s.instrument_t x = true → s.mode_t x = false)

def ModeSupportedByInstrument (s : StaticState) : Prop :=
  (∀ m, s.mode_t m = true → ∃ i, s.instrument_t i = true ∧ s.supports_p i m = true) ∧
  (∀ i, s.instrument_t i = true → ∃ m, s.mode_t m = true ∧ s.supports_p i m = true)

def InstrumentOnBoardExactlyOneSatellite (s : StaticState) : Prop :=
  ∀ i, s.instrument_t i = true → ∃! sat, s.satellite_t sat = true ∧ s.on_board_p i sat = true

def SatelliteHasAtLeastOneInstrument (s : StaticState) : Prop :=
  ∀ sat, s.satellite_t sat = true → ∃ i, s.instrument_t i = true ∧ s.on_board_p i sat = true

def InstrumentHasCalibrationTarget (s : StaticState) : Prop :=
  ∀ i, s.instrument_t i = true → ∃ d, s.direction_t d = true ∧ s.calibration_target_p i d = true

def MinNumObj (s : StaticState) : Prop :=
  ∃ sat, s.satellite_t sat = true

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidOnBoardParam s ∧
  ValidSupportsParam s ∧
  ValidCalibrationTargetParam s ∧
  ValidTypeHierarchy s ∧
  ModeSupportedByInstrument s ∧
  InstrumentOnBoardExactlyOneSatellite s ∧
  SatelliteHasAtLeastOneInstrument s ∧
  InstrumentHasCalibrationTarget s ∧
  MinNumObj s

def ValidPointingParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_s var_d, Truthy.isTrue (d.pointing_p var_s var_d) → s.satellite_t var_s = true ∧ s.direction_t var_d = true

def ValidPowerAvailParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_s, Truthy.isTrue (d.power_avail_p var_s) → s.satellite_t var_s = true

def ValidPowerOnParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_i, Truthy.isTrue (d.power_on_p var_i) → s.instrument_t var_i = true

def ValidCalibratedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_i, Truthy.isTrue (d.calibrated_p var_i) → s.instrument_t var_i = true

def ValidHaveImageParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_d var_m, Truthy.isTrue (d.have_image_p var_d var_m) → s.direction_t var_d = true ∧ s.mode_t var_m = true

-- consistency constraints

def PowerAvailOnXor {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ sat i, s.satellite_t sat = true → s.instrument_t i = true → s.on_board_p i sat = true →
    ¬ (Truthy.isTrue (d.power_avail_p sat) ∧ Truthy.isTrue (d.power_on_p i))

def PowerOnCapacity {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ sat i1 i2, s.satellite_t sat = true →
    s.on_board_p i1 sat = true → s.on_board_p i2 sat = true →
    Truthy.isTrue (d.power_on_p i1) → Truthy.isTrue (d.power_on_p i2) →
    i1 = i2

def UniqueSatellitePointing {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ sat dir1 dir2, s.satellite_t sat = true →
    Truthy.isTrue (d.pointing_p sat dir1) → Truthy.isTrue (d.pointing_p sat dir2) →
    dir1 = dir2

-- completeness constraints

def PowerAvailOnExhaustive (s : State) : Prop :=
  ∀ sat, s.statics.satellite_t sat = true →
    s.dynamic.power_avail_p sat = true ∨
    ∃ i, s.statics.instrument_t i = true ∧
         s.statics.on_board_p i sat = true ∧
         s.dynamic.power_on_p i = true

def SatelliteHasPointing (s : State) : Prop :=
  ∀ sat, s.statics.satellite_t sat = true →
    ∃ dir, s.statics.direction_t dir = true ∧ s.dynamic.pointing_p sat dir = true

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidPointingParam s.statics s.dynamic ∧
  ValidPowerAvailParam s.statics s.dynamic ∧
  ValidPowerOnParam s.statics s.dynamic ∧
  ValidCalibratedParam s.statics s.dynamic ∧
  ValidHaveImageParam s.statics s.dynamic ∧
  PowerAvailOnXor s.statics s.dynamic ∧
  PowerOnCapacity s.statics s.dynamic ∧
  UniqueSatellitePointing s.statics s.dynamic ∧
  PowerAvailOnExhaustive s ∧
  SatelliteHasPointing s

def InitPowerAvail (s : State) : Prop :=
  ∀ sat, s.statics.satellite_t sat = true → s.dynamic.power_avail_p sat = true

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitPowerAvail s

def GoalHasTarget (initial : State) (g : Goal) : Prop :=
  (∃ sat dir, g.dynamic.pointing_p sat dir = some true) ∨
  (∃ dir mode, g.dynamic.have_image_p dir mode = some true)

def GoalIgnorePowerAvail (initial : State) (g : Goal) : Prop :=
  ∀ sat, g.dynamic.power_avail_p sat = none

def GoalIgnorePowerOn (initial : State) (g : Goal) : Prop :=
  ∀ i, g.dynamic.power_on_p i = none

def GoalIgnoreCalibrated (initial : State) (g : Goal) : Prop :=
  ∀ i, g.dynamic.calibrated_p i = none

def GoalOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ sat dir, g.dynamic.pointing_p sat dir ≠ some false ∧
  ∀ dir mode, g.dynamic.have_image_p dir mode ≠ some false

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidPointingParam initial.statics g.dynamic ∧
  ValidPowerAvailParam initial.statics g.dynamic ∧
  ValidPowerOnParam initial.statics g.dynamic ∧
  ValidCalibratedParam initial.statics g.dynamic ∧
  ValidHaveImageParam initial.statics g.dynamic ∧
  PowerAvailOnXor initial.statics g.dynamic ∧
  PowerOnCapacity initial.statics g.dynamic ∧
  UniqueSatellitePointing initial.statics g.dynamic ∧
  GoalHasTarget initial g ∧
  GoalIgnorePowerAvail initial g ∧
  GoalIgnorePowerOn initial g ∧
  GoalIgnoreCalibrated initial g ∧
  GoalOnlyPositive initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_s var_d,
    match g.dynamic.pointing_p var_s var_d with
    | none => True
    | some b => s.dynamic.pointing_p var_s var_d = b) ∧
  (∀ var_s,
    match g.dynamic.power_avail_p var_s with
    | none => True
    | some b => s.dynamic.power_avail_p var_s = b) ∧
  (∀ var_i,
    match g.dynamic.power_on_p var_i with
    | none => True
    | some b => s.dynamic.power_on_p var_i = b) ∧
  (∀ var_i,
    match g.dynamic.calibrated_p var_i with
    | none => True
    | some b => s.dynamic.calibrated_p var_i = b) ∧
  (∀ var_d var_m,
    match g.dynamic.have_image_p var_d var_m with
    | none => True
    | some b => s.dynamic.have_image_p var_d var_m = b)

def turn_toPre (var_s : Obj) (var_d_new : Obj) (var_d_prev : Obj) (s : State) : Prop :=
  s.statics.satellite_t var_s = true ∧
  s.statics.direction_t var_d_new = true ∧
  s.statics.direction_t var_d_prev = true ∧
  s.dynamic.pointing_p var_s var_d_prev = true ∧
  s.dynamic.pointing_p var_s var_d_new = false

def switch_onPre (var_i : Obj) (var_s : Obj) (s : State) : Prop :=
  s.statics.instrument_t var_i = true ∧
  s.statics.satellite_t var_s = true ∧
  s.statics.on_board_p var_i var_s = true ∧
  s.dynamic.power_avail_p var_s = true

def switch_offPre (var_i : Obj) (var_s : Obj) (s : State) : Prop :=
  s.statics.instrument_t var_i = true ∧
  s.statics.satellite_t var_s = true ∧
  s.statics.on_board_p var_i var_s = true ∧
  s.dynamic.power_on_p var_i = true

def calibratePre (var_s : Obj) (var_i : Obj) (var_d : Obj) (s : State) : Prop :=
  s.statics.satellite_t var_s = true ∧
  s.statics.instrument_t var_i = true ∧
  s.statics.direction_t var_d = true ∧
  s.statics.on_board_p var_i var_s = true ∧
  s.statics.calibration_target_p var_i var_d = true ∧
  s.dynamic.pointing_p var_s var_d = true ∧
  s.dynamic.power_on_p var_i = true

def take_imagePre (var_s : Obj) (var_d : Obj) (var_i : Obj) (var_m : Obj) (s : State) : Prop :=
  s.statics.satellite_t var_s = true ∧
  s.statics.direction_t var_d = true ∧
  s.statics.instrument_t var_i = true ∧
  s.statics.mode_t var_m = true ∧
  s.dynamic.calibrated_p var_i = true ∧
  s.statics.on_board_p var_i var_s = true ∧
  s.statics.supports_p var_i var_m = true ∧
  s.dynamic.power_on_p var_i = true ∧
  s.dynamic.pointing_p var_s var_d = true

def turn_to (var_s : Obj) (var_d_new : Obj) (var_d_prev : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    pointing_p :=
      fun var_s' var_d_new' =>
        if var_s' = var_s ∧ var_d_new' = var_d_new then
          true
        else if var_s' = var_s ∧ var_d_new' = var_d_prev then
          false
        else
          s.dynamic.pointing_p var_s' var_d_new'
  }
}

def switch_on (var_i : Obj) (var_s : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    power_avail_p :=
      fun var_s' =>
        if var_s' = var_s then
          false
        else
          s.dynamic.power_avail_p var_s',
    power_on_p :=
      fun var_i' =>
        if var_i' = var_i then
          true
        else
          s.dynamic.power_on_p var_i',
    calibrated_p :=
      fun var_i' =>
        if var_i' = var_i then
          false
        else
          s.dynamic.calibrated_p var_i'
  }
}

def switch_off (var_i : Obj) (var_s : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    power_avail_p :=
      fun var_s' =>
        if var_s' = var_s then
          true
        else
          s.dynamic.power_avail_p var_s',
    power_on_p :=
      fun var_i' =>
        if var_i' = var_i then
          false
        else
          s.dynamic.power_on_p var_i'
  }
}

def calibrate (var_s : Obj) (var_i : Obj) (var_d : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    calibrated_p :=
      fun var_i' =>
        if var_i' = var_i then
          true
        else
          s.dynamic.calibrated_p var_i'
  }
}

def take_image (var_s : Obj) (var_d : Obj) (var_i : Obj) (var_m : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    have_image_p :=
      fun var_d' var_m' =>
        if var_d' = var_d ∧ var_m' = var_m then
          true
        else
          s.dynamic.have_image_p var_d' var_m'
  }
}

inductive PlanAction where
  | turn_to    (var_s : Obj) (var_d_new : Obj) (var_d_prev : Obj)
  | switch_on  (var_i : Obj) (var_s : Obj)
  | switch_off (var_i : Obj) (var_s : Obj)
  | calibrate  (var_s : Obj) (var_i : Obj) (var_d : Obj)
  | take_image (var_s : Obj) (var_d : Obj) (var_i : Obj) (var_m : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .turn_to    var_s var_d_new var_d_prev, s => turn_toPre var_s var_d_new var_d_prev s
  | .switch_on  var_i var_s               , s => switch_onPre var_i var_s s
  | .switch_off var_i var_s               , s => switch_offPre var_i var_s s
  | .calibrate  var_s var_i var_d         , s => calibratePre var_s var_i var_d s
  | .take_image var_s var_d var_i var_m   , s => take_imagePre var_s var_d var_i var_m s

def actionApply : PlanAction → State → State
  | .turn_to    var_s var_d_new var_d_prev, s => turn_to var_s var_d_new var_d_prev s
  | .switch_on  var_i var_s               , s => switch_on var_i var_s s
  | .switch_off var_i var_s               , s => switch_off var_i var_s s
  | .calibrate  var_s var_i var_d         , s => calibrate var_s var_i var_d s
  | .take_image var_s var_d var_i var_m   , s => take_image var_s var_d var_i var_m s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Find an instrument supporting the requested mode.
def findInstrumentForMode (st : StaticState) (mode : Obj) : Obj :=
  (st.objects.find? fun instrument =>
    st.instrument_t instrument && st.supports_p instrument mode).getD 0

-- Find the satellite carrying an instrument.
def findSatelliteForInstrument (st : StaticState) (instrument : Obj) : Obj :=
  (st.objects.find? fun satellite =>
    st.satellite_t satellite && st.on_board_p instrument satellite).getD 0

-- Find a calibration target for an instrument.
def findCalibrationTarget (st : StaticState) (instrument : Obj) : Obj :=
  (st.objects.find? fun direction =>
    st.direction_t direction &&
      st.calibration_target_p instrument direction).getD 0

-- Find the direction in which a satellite currently points.
def findCurrentDirection (s : State) (satellite : Obj) : Obj :=
  (s.statics.objects.find? fun direction =>
    s.statics.direction_t direction &&
      s.dynamic.pointing_p satellite direction).getD 0

-- Enumerate all requested image goals.
def requiredImages (s : State) (g : Goal) : List (Obj × Obj) :=
  s.statics.objects.flatMap fun direction =>
    s.statics.objects.filterMap fun mode =>
      if g.dynamic.have_image_p direction mode = some true then
        some (direction, mode)
      else
        none

-- Enumerate all requested final satellite orientations.
def requiredPointings (s : State) (g : Goal) : List (Obj × Obj) :=
  s.statics.objects.flatMap fun satellite =>
    s.statics.objects.filterMap fun direction =>
      if g.dynamic.pointing_p satellite direction = some true then
        some (satellite, direction)
      else
        none

-- Construct the actions needed to capture one image.
def makeImagePlan (s : State) (direction mode : Obj) : List PlanAction :=
  let instrument := findInstrumentForMode s.statics mode
  let satellite := findSatelliteForInstrument s.statics instrument
  let calibrationDirection :=
    findCalibrationTarget s.statics instrument
  let currentDirection := findCurrentDirection s satellite
  let turnToCalibration : List PlanAction :=
    if currentDirection = calibrationDirection then
      []
    else
      [.turn_to satellite calibrationDirection currentDirection]
  let turnToImage : List PlanAction :=
    if calibrationDirection = direction then
      []
    else
      [.turn_to satellite direction calibrationDirection]
  [.switch_on instrument satellite] ++
    turnToCalibration ++
    [.calibrate satellite instrument calibrationDirection] ++
    turnToImage ++
    [.take_image satellite direction instrument mode,
     .switch_off instrument satellite]

-- Sequentially solve all image goals while tracking the resulting state.
def solveImageGoals : List (Obj × Obj) → State → List PlanAction
  | [], _ => []
  | (direction, mode) :: goals, s =>
      let imagePlan := makeImagePlan s direction mode
      let nextState := runPlan imagePlan s
      imagePlan ++ solveImageGoals goals nextState

-- Construct a plan for one final orientation goal.
def makePointingPlan
    (s : State) (satellite direction : Obj) : List PlanAction :=
  let currentDirection := findCurrentDirection s satellite
  if currentDirection = direction then
    []
  else
    [.turn_to satellite direction currentDirection]

-- Sequentially establish all final orientation goals.
def solvePointingGoals : List (Obj × Obj) → State → List PlanAction
  | [], _ => []
  | (satellite, direction) :: goals, s =>
      let pointingPlan := makePointingPlan s satellite direction
      let nextState := runPlan pointingPlan s
      pointingPlan ++ solvePointingGoals goals nextState

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  let imagePlan := solveImageGoals (requiredImages s g) s
  let stateAfterImages := runPlan imagePlan s
  let pointingPlan :=
    solvePointingGoals (requiredPointings s g) stateAfterImages
  imagePlan ++ pointingPlan

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

lemma turn_to_statics (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).statics = s.statics := rfl

lemma switch_on_statics (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).statics = s.statics := rfl

lemma switch_off_statics (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).statics = s.statics := rfl

lemma calibrate_statics (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).statics = s.statics := rfl

lemma take_image_statics (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | turn_to var_s var_d_new var_d_prev => exact turn_to_statics var_s var_d_new var_d_prev s
      | switch_on var_i var_s              => exact switch_on_statics var_i var_s s
      | switch_off var_i var_s             => exact switch_off_statics var_i var_s s
      | calibrate var_s var_i var_d        => exact calibrate_statics var_s var_i var_d s
      | take_image var_s var_d var_i var_m => exact take_image_statics var_s var_d var_i var_m s

-- turn_to only touches pointing_p
lemma turn_to_pointing_p_ne_var_d (var_s var_d_new var_d_prev : Obj) (s : State) {var_d_new' : Obj} (h1 : var_d_new' ≠ var_d_new) (h2 : var_d_new' ≠ var_d_prev) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p var_s var_d_new' = s.dynamic.pointing_p var_s var_d_new' := by
  unfold turn_to
  simp [h1, h2]

-- turn_to never touches power_avail_p
lemma turn_to_power_avail_p (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.power_avail_p = s.dynamic.power_avail_p := rfl

-- turn_to never touches power_on_p
lemma turn_to_power_on_p (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.power_on_p = s.dynamic.power_on_p := rfl

-- turn_to never touches calibrated_p
lemma turn_to_calibrated_p (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- turn_to never touches have_image_p
lemma turn_to_have_image_p (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- switch_on only touches power_on_p, calibrated_p, power_avail_p
lemma switch_on_power_avail_p_ne (var_i var_s : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (switch_on var_i var_s s).dynamic.power_avail_p var_s' = s.dynamic.power_avail_p var_s' := by
  unfold switch_on
  simp [h1]

lemma switch_on_power_on_p_ne (var_i var_s : Obj) (s : State) {var_i' : Obj} (h1 : var_i' ≠ var_i) :
    (switch_on var_i var_s s).dynamic.power_on_p var_i' = s.dynamic.power_on_p var_i' := by
  unfold switch_on
  simp [h1]

lemma switch_on_calibrated_p_ne (var_i var_s : Obj) (s : State) {var_i' : Obj} (h1 : var_i' ≠ var_i) :
    (switch_on var_i var_s s).dynamic.calibrated_p var_i' = s.dynamic.calibrated_p var_i' := by
  unfold switch_on
  simp [h1]

-- switch_on never touches pointing_p
lemma switch_on_pointing_p (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).dynamic.pointing_p = s.dynamic.pointing_p := rfl

-- switch_on never touches have_image_p
lemma switch_on_have_image_p (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- switch_off only touches power_avail_p, power_on_p
lemma switch_off_power_avail_p_ne (var_i var_s : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (switch_off var_i var_s s).dynamic.power_avail_p var_s' = s.dynamic.power_avail_p var_s' := by
  unfold switch_off
  simp [h1]

lemma switch_off_power_on_p_ne (var_i var_s : Obj) (s : State) {var_i' : Obj} (h1 : var_i' ≠ var_i) :
    (switch_off var_i var_s s).dynamic.power_on_p var_i' = s.dynamic.power_on_p var_i' := by
  unfold switch_off
  simp [h1]

-- switch_off never touches pointing_p
lemma switch_off_pointing_p (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).dynamic.pointing_p = s.dynamic.pointing_p := rfl

-- switch_off never touches calibrated_p
lemma switch_off_calibrated_p (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- switch_off never touches have_image_p
lemma switch_off_have_image_p (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- calibrate only touches calibrated_p
lemma calibrate_calibrated_p_ne (var_s var_i var_d : Obj) (s : State) {var_i' : Obj} (h1 : var_i' ≠ var_i) :
    (calibrate var_s var_i var_d s).dynamic.calibrated_p var_i' = s.dynamic.calibrated_p var_i' := by
  unfold calibrate
  simp [h1]

-- calibrate never touches pointing_p
lemma calibrate_pointing_p (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).dynamic.pointing_p = s.dynamic.pointing_p := rfl

-- calibrate never touches power_avail_p
lemma calibrate_power_avail_p (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).dynamic.power_avail_p = s.dynamic.power_avail_p := rfl

-- calibrate never touches power_on_p
lemma calibrate_power_on_p (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).dynamic.power_on_p = s.dynamic.power_on_p := rfl

-- calibrate never touches have_image_p
lemma calibrate_have_image_p (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- take_image only touches have_image_p
lemma take_image_have_image_p_ne (var_s var_d var_i var_m : Obj) (s : State) {var_d' var_m' : Obj} (h1 : var_d' ≠ var_d) :
    (take_image var_s var_d var_i var_m s).dynamic.have_image_p var_d' var_m' = s.dynamic.have_image_p var_d' var_m' := by
  unfold take_image
  simp [h1]

lemma take_image_have_image_p_ne_var_m (var_s var_d var_i var_m : Obj) (s : State) {var_m' : Obj} (h1 : var_m' ≠ var_m) :
    (take_image var_s var_d var_i var_m s).dynamic.have_image_p var_d var_m' = s.dynamic.have_image_p var_d var_m' := by
  unfold take_image
  simp [h1]

-- take_image never touches pointing_p
lemma take_image_pointing_p (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).dynamic.pointing_p = s.dynamic.pointing_p := rfl

-- take_image never touches power_avail_p
lemma take_image_power_avail_p (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).dynamic.power_avail_p = s.dynamic.power_avail_p := rfl

-- take_image never touches power_on_p
lemma take_image_power_on_p (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).dynamic.power_on_p = s.dynamic.power_on_p := rfl

-- take_image never touches calibrated_p
lemma take_image_calibrated_p (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

lemma turn_to_pointing_p_eq1 (var_s var_d_new var_d_prev : Obj) (s : State) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p var_s var_d_new = true := by
  unfold turn_to
  simp

lemma turn_to_pointing_p_eq2 (var_s var_d_new var_d_prev : Obj) (s : State) (h1 : var_d_prev ≠ var_d_new) :
    (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p var_s var_d_prev = false := by
  unfold turn_to
  simp [h1]

lemma switch_on_power_avail_p_eq1 (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).dynamic.power_avail_p var_s = false := by
  unfold switch_on
  simp

lemma switch_on_power_on_p_eq1 (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).dynamic.power_on_p var_i = true := by
  unfold switch_on
  simp

lemma switch_on_calibrated_p_eq1 (var_i var_s : Obj) (s : State) :
    (switch_on var_i var_s s).dynamic.calibrated_p var_i = false := by
  unfold switch_on
  simp

lemma switch_off_power_avail_p_eq1 (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).dynamic.power_avail_p var_s = true := by
  unfold switch_off
  simp

lemma switch_off_power_on_p_eq1 (var_i var_s : Obj) (s : State) :
    (switch_off var_i var_s s).dynamic.power_on_p var_i = false := by
  unfold switch_off
  simp

lemma calibrate_calibrated_p_eq1 (var_s var_i var_d : Obj) (s : State) :
    (calibrate var_s var_i var_d s).dynamic.calibrated_p var_i = true := by
  unfold calibrate
  simp

lemma take_image_have_image_p_eq1 (var_s var_d var_i var_m : Obj) (s : State) :
    (take_image var_s var_d var_i var_m s).dynamic.have_image_p var_d var_m = true := by
  unfold take_image
  simp

lemma turn_to_preserves_wf
    (var_s var_d_new var_d_prev)
    (s : State)
    (hwf : WellFormed s)
    (hpre : turn_toPre var_s var_d_new var_d_prev s) :
    WellFormed (turn_to var_s var_d_new var_d_prev s) := by
  rcases hwf with
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩
  rcases hpre with
    ⟨hSat, hDirNew, hDirPrev, hPointPrev, hPointNewFalse⟩

  have hpoint' :
      ValidPointingParam s.statics
        (turn_to var_s var_d_new var_d_prev s).dynamic := by
    intro sat dir ht
    change
      (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p sat dir =
        true at ht
    by_cases hs : sat = var_s
    · subst sat
      by_cases hdNew : dir = var_d_new
      · subst dir
        exact ⟨hSat, hDirNew⟩
      · by_cases hdPrev : dir = var_d_prev
        · subst dir
          simp [turn_to, hdNew] at ht
        · have hold :
              s.dynamic.pointing_p var_s dir = true := by
            simpa [turn_to, hdNew, hdPrev] using ht
          exact hpoint var_s dir hold
    · have hold :
          s.dynamic.pointing_p sat dir = true := by
        simpa [turn_to, hs] using ht
      exact hpoint sat dir hold

  have hupdatedDir :
      ∀ dir,
        (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p
            var_s dir = true →
        dir = var_d_new := by
    intro dir ht
    by_cases hdNew : dir = var_d_new
    · exact hdNew
    · by_cases hdPrev : dir = var_d_prev
      · subst dir
        simp [turn_to, hdNew] at ht
      · have hold :
            s.dynamic.pointing_p var_s dir = true := by
          simpa [turn_to, hdNew, hdPrev] using ht
        have heq :
            dir = var_d_prev :=
          huniq var_s dir var_d_prev hSat hold hPointPrev
        exact (hdPrev heq).elim

  have huniq' :
      UniqueSatellitePointing s.statics
        (turn_to var_s var_d_new var_d_prev s).dynamic := by
    intro sat dir₁ dir₂ hSat' hPoint₁ hPoint₂
    change
      (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p
          sat dir₁ = true at hPoint₁
    change
      (turn_to var_s var_d_new var_d_prev s).dynamic.pointing_p
          sat dir₂ = true at hPoint₂
    by_cases hs : sat = var_s
    · subst sat
      exact (hupdatedDir dir₁ hPoint₁).trans
        (hupdatedDir dir₂ hPoint₂).symm
    · have hPoint₁Old :
          s.dynamic.pointing_p sat dir₁ = true := by
        simpa [turn_to, hs] using hPoint₁
      have hPoint₂Old :
          s.dynamic.pointing_p sat dir₂ = true := by
        simpa [turn_to, hs] using hPoint₂
      exact huniq sat dir₁ dir₂ hSat' hPoint₁Old hPoint₂Old

  have hhasPointing' :
      SatelliteHasPointing
        (turn_to var_s var_d_new var_d_prev s) := by
    intro sat hSat'
    by_cases hs : sat = var_s
    · subst sat
      refine ⟨var_d_new, hDirNew, ?_⟩
      simp [turn_to]
    · rcases hhasPointing sat hSat' with
        ⟨dir, hDir, hPointOld⟩
      refine ⟨dir, hDir, ?_⟩
      simpa [turn_to, hs] using hPointOld

  exact
    ⟨hstatic, hpoint', hpavail, hpon, hcal, himg,
     hxor, hcap, huniq', hexhaustive, hhasPointing'⟩


lemma switch_on_preserves_wf
    (var_i var_s)
    (s : State)
    (hwf : WellFormed s)
    (hpre : switch_onPre var_i var_s s) :
    WellFormed (switch_on var_i var_s s) := by
  rcases hwf with
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩
  rcases hpre with
    ⟨hInstrument, hSatellite, hOnBoard, hPowerAvail⟩

  have hvalidOnBoard :
      ValidOnBoardParam s.statics :=
    hstatic.2.1

  have hexact :
      InstrumentOnBoardExactlyOneSatellite s.statics :=
    hstatic.2.2.2.2.2.2.1

  have honly :
      ∀ sat,
        s.statics.satellite_t sat = true →
        s.statics.on_board_p var_i sat = true →
        sat = var_s := by
    intro sat hSat hBoard
    rcases hexact var_i hInstrument with
      ⟨sat₀, hSat₀, hUnique⟩
    exact
      (hUnique sat ⟨hSat, hBoard⟩).trans
        (hUnique var_s ⟨hSatellite, hOnBoard⟩).symm

  have hpavail' :
      ValidPowerAvailParam s.statics
        (switch_on var_i var_s s).dynamic := by
    intro sat ht
    change
      (switch_on var_i var_s s).dynamic.power_avail_p sat = true at ht
    by_cases hs : sat = var_s
    · subst sat
      simp [switch_on] at ht
    · have hold :
          s.dynamic.power_avail_p sat = true := by
        simpa [switch_on, hs] using ht
      exact hpavail sat hold

  have hpon' :
      ValidPowerOnParam s.statics
        (switch_on var_i var_s s).dynamic := by
    intro i ht
    change
      (switch_on var_i var_s s).dynamic.power_on_p i = true at ht
    by_cases hi : i = var_i
    · subst i
      exact hInstrument
    · have hold :
          s.dynamic.power_on_p i = true := by
        simpa [switch_on, hi] using ht
      exact hpon i hold

  have hcal' :
      ValidCalibratedParam s.statics
        (switch_on var_i var_s s).dynamic := by
    intro i ht
    change
      (switch_on var_i var_s s).dynamic.calibrated_p i = true at ht
    by_cases hi : i = var_i
    · subst i
      simp [switch_on] at ht
    · have hold :
          s.dynamic.calibrated_p i = true := by
        simpa [switch_on, hi] using ht
      exact hcal i hold

  have hxor' :
      PowerAvailOnXor s.statics
        (switch_on var_i var_s s).dynamic := by
    intro sat i hSat hInstrument' hBoard hBoth
    rcases hBoth with ⟨hAvailNew, hOnNew⟩
    change
      (switch_on var_i var_s s).dynamic.power_avail_p sat = true
        at hAvailNew
    change
      (switch_on var_i var_s s).dynamic.power_on_p i = true
        at hOnNew
    by_cases hs : sat = var_s
    · subst sat
      simp [switch_on] at hAvailNew
    · by_cases hi : i = var_i
      · subst i
        exact hs (honly sat hSat hBoard)
      · have hAvailOld :
            s.dynamic.power_avail_p sat = true := by
          simpa [switch_on, hs] using hAvailNew
        have hOnOld :
            s.dynamic.power_on_p i = true := by
          simpa [switch_on, hi] using hOnNew
        exact
          (hxor sat i hSat hInstrument' hBoard)
            ⟨hAvailOld, hOnOld⟩

  have hcap' :
      PowerOnCapacity s.statics
        (switch_on var_i var_s s).dynamic := by
    intro sat i₁ i₂ hSat hBoard₁ hBoard₂ hOn₁ hOn₂
    change
      (switch_on var_i var_s s).dynamic.power_on_p i₁ = true at hOn₁
    change
      (switch_on var_i var_s s).dynamic.power_on_p i₂ = true at hOn₂
    by_cases hi₁ : i₁ = var_i
    · subst i₁
      by_cases hi₂ : i₂ = var_i
      · exact hi₂.symm
      · have hs : sat = var_s :=
          honly sat hSat hBoard₁
        have hOn₂Old :
            s.dynamic.power_on_p i₂ = true := by
          simpa [switch_on, hi₂] using hOn₂
        have hInstrument₂ :
            s.statics.instrument_t i₂ = true :=
          (hvalidOnBoard i₂ sat hBoard₂).1
        have hAvailOld :
            s.dynamic.power_avail_p sat = true := by
          rw [hs]
          exact hPowerAvail
        exfalso
        exact
          (hxor sat i₂ hSat hInstrument₂ hBoard₂)
            ⟨hAvailOld, hOn₂Old⟩
    · by_cases hi₂ : i₂ = var_i
      · subst i₂
        have hs : sat = var_s :=
          honly sat hSat hBoard₂
        have hOn₁Old :
            s.dynamic.power_on_p i₁ = true := by
          simpa [switch_on, hi₁] using hOn₁
        have hInstrument₁ :
            s.statics.instrument_t i₁ = true :=
          (hvalidOnBoard i₁ sat hBoard₁).1
        have hAvailOld :
            s.dynamic.power_avail_p sat = true := by
          rw [hs]
          exact hPowerAvail
        exfalso
        exact
          (hxor sat i₁ hSat hInstrument₁ hBoard₁)
            ⟨hAvailOld, hOn₁Old⟩
      · have hOn₁Old :
            s.dynamic.power_on_p i₁ = true := by
          simpa [switch_on, hi₁] using hOn₁
        have hOn₂Old :
            s.dynamic.power_on_p i₂ = true := by
          simpa [switch_on, hi₂] using hOn₂
        exact
          hcap sat i₁ i₂ hSat hBoard₁ hBoard₂ hOn₁Old hOn₂Old

  have hexhaustive' :
      PowerAvailOnExhaustive (switch_on var_i var_s s) := by
    intro sat hSat
    by_cases hs : sat = var_s
    · subst sat
      right
      refine ⟨var_i, hInstrument, hOnBoard, ?_⟩
      simp [switch_on]
    · rcases hexhaustive sat hSat with
        hAvailOld | ⟨i, hInstrument', hBoard, hOnOld⟩
      · left
        simpa [switch_on, hs] using hAvailOld
      · right
        refine ⟨i, hInstrument', hBoard, ?_⟩
        by_cases hi : i = var_i
        · subst i
          simp [switch_on]
        · simpa [switch_on, hi] using hOnOld

  exact
    ⟨hstatic, hpoint, hpavail', hpon', hcal', himg,
     hxor', hcap', huniq, hexhaustive', hhasPointing⟩


lemma switch_off_preserves_wf
    (var_i var_s)
    (s : State)
    (hwf : WellFormed s)
    (hpre : switch_offPre var_i var_s s) :
    WellFormed (switch_off var_i var_s s) := by
  rcases hwf with
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩
  rcases hpre with
    ⟨hInstrument, hSatellite, hOnBoard, hPowerOn⟩

  have hexact :
      InstrumentOnBoardExactlyOneSatellite s.statics :=
    hstatic.2.2.2.2.2.2.1

  have honly :
      ∀ sat,
        s.statics.satellite_t sat = true →
        s.statics.on_board_p var_i sat = true →
        sat = var_s := by
    intro sat hSat hBoard
    rcases hexact var_i hInstrument with
      ⟨sat₀, hSat₀, hUnique⟩
    exact
      (hUnique sat ⟨hSat, hBoard⟩).trans
        (hUnique var_s ⟨hSatellite, hOnBoard⟩).symm

  have hpavail' :
      ValidPowerAvailParam s.statics
        (switch_off var_i var_s s).dynamic := by
    intro sat ht
    change
      (switch_off var_i var_s s).dynamic.power_avail_p sat = true at ht
    by_cases hs : sat = var_s
    · subst sat
      exact hSatellite
    · have hold :
          s.dynamic.power_avail_p sat = true := by
        simpa [switch_off, hs] using ht
      exact hpavail sat hold

  have hpon' :
      ValidPowerOnParam s.statics
        (switch_off var_i var_s s).dynamic := by
    intro i ht
    change
      (switch_off var_i var_s s).dynamic.power_on_p i = true at ht
    by_cases hi : i = var_i
    · subst i
      simp [switch_off] at ht
    · have hold :
          s.dynamic.power_on_p i = true := by
        simpa [switch_off, hi] using ht
      exact hpon i hold

  have hxor' :
      PowerAvailOnXor s.statics
        (switch_off var_i var_s s).dynamic := by
    intro sat i hSat hInstrument' hBoard hBoth
    rcases hBoth with ⟨hAvailNew, hOnNew⟩
    change
      (switch_off var_i var_s s).dynamic.power_avail_p sat = true
        at hAvailNew
    change
      (switch_off var_i var_s s).dynamic.power_on_p i = true
        at hOnNew
    by_cases hs : sat = var_s
    · subst sat
      by_cases hi : i = var_i
      · subst i
        simp [switch_off] at hOnNew
      · have hOnOld :
            s.dynamic.power_on_p i = true := by
          simpa [switch_off, hi] using hOnNew
        have heq :
            var_i = i :=
          hcap var_s var_i i hSatellite hOnBoard hBoard
            hPowerOn hOnOld
        exact hi heq.symm
    · by_cases hi : i = var_i
      · subst i
        simp [switch_off] at hOnNew
      · have hAvailOld :
            s.dynamic.power_avail_p sat = true := by
          simpa [switch_off, hs] using hAvailNew
        have hOnOld :
            s.dynamic.power_on_p i = true := by
          simpa [switch_off, hi] using hOnNew
        exact
          (hxor sat i hSat hInstrument' hBoard)
            ⟨hAvailOld, hOnOld⟩

  have hcap' :
      PowerOnCapacity s.statics
        (switch_off var_i var_s s).dynamic := by
    intro sat i₁ i₂ hSat hBoard₁ hBoard₂ hOn₁ hOn₂
    change
      (switch_off var_i var_s s).dynamic.power_on_p i₁ = true at hOn₁
    change
      (switch_off var_i var_s s).dynamic.power_on_p i₂ = true at hOn₂
    by_cases hi₁ : i₁ = var_i
    · subst i₁
      simp [switch_off] at hOn₁
    · by_cases hi₂ : i₂ = var_i
      · subst i₂
        simp [switch_off] at hOn₂
      · have hOn₁Old :
            s.dynamic.power_on_p i₁ = true := by
          simpa [switch_off, hi₁] using hOn₁
        have hOn₂Old :
            s.dynamic.power_on_p i₂ = true := by
          simpa [switch_off, hi₂] using hOn₂
        exact
          hcap sat i₁ i₂ hSat hBoard₁ hBoard₂ hOn₁Old hOn₂Old

  have hexhaustive' :
      PowerAvailOnExhaustive (switch_off var_i var_s s) := by
    intro sat hSat
    by_cases hs : sat = var_s
    · subst sat
      left
      simp [switch_off]
    · rcases hexhaustive sat hSat with
        hAvailOld | ⟨i, hInstrument', hBoard, hOnOld⟩
      · left
        simpa [switch_off, hs] using hAvailOld
      · by_cases hi : i = var_i
        · subst i
          exact (hs (honly sat hSat hBoard)).elim
        · right
          refine ⟨i, hInstrument', hBoard, ?_⟩
          simpa [switch_off, hi] using hOnOld

  exact
    ⟨hstatic, hpoint, hpavail', hpon', hcal, himg,
     hxor', hcap', huniq, hexhaustive', hhasPointing⟩


lemma calibrate_preserves_wf
    (var_s var_i var_d)
    (s : State)
    (hwf : WellFormed s)
    (hpre : calibratePre var_s var_i var_d s) :
    WellFormed (calibrate var_s var_i var_d s) := by
  rcases hwf with
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩
  rcases hpre with
    ⟨hSatellite, hInstrument, hDirection, hOnBoard,
     hCalibrationTarget, hPointing, hPowerOn⟩

  have hcal' :
      ValidCalibratedParam s.statics
        (calibrate var_s var_i var_d s).dynamic := by
    intro i ht
    change
      (calibrate var_s var_i var_d s).dynamic.calibrated_p i = true at ht
    by_cases hi : i = var_i
    · subst i
      exact hInstrument
    · have hold :
          s.dynamic.calibrated_p i = true := by
        simpa [calibrate, hi] using ht
      exact hcal i hold

  exact
    ⟨hstatic, hpoint, hpavail, hpon, hcal', himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩


lemma take_image_preserves_wf
    (var_s var_d var_i var_m)
    (s : State)
    (hwf : WellFormed s)
    (hpre : take_imagePre var_s var_d var_i var_m s) :
    WellFormed (take_image var_s var_d var_i var_m s) := by
  rcases hwf with
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg,
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩
  rcases hpre with
    ⟨hSatellite, hDirection, hInstrument, hMode,
     hCalibrated, hOnBoard, hSupports, hPowerOn, hPointing⟩

  have himg' :
      ValidHaveImageParam s.statics
        (take_image var_s var_d var_i var_m s).dynamic := by
    intro dir mode ht
    change
      (take_image var_s var_d var_i var_m s).dynamic.have_image_p
          dir mode = true at ht
    by_cases hPair : dir = var_d ∧ mode = var_m
    · rcases hPair with ⟨rfl, rfl⟩
      exact ⟨hDirection, hMode⟩
    · have hold :
          s.dynamic.have_image_p dir mode = true := by
        simpa [take_image, hPair] using ht
      exact himg dir mode hold

  exact
    ⟨hstatic, hpoint, hpavail, hpon, hcal, himg',
     hxor, hcap, huniq, hexhaustive, hhasPointing⟩

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | turn_to var_s var_d_new var_d_prev =>
      exact turn_to_preserves_wf var_s var_d_new var_d_prev s hwf hpre
  | switch_on var_i var_s =>
      exact switch_on_preserves_wf var_i var_s s hwf hpre
  | switch_off var_i var_s =>
      exact switch_off_preserves_wf var_i var_s s hwf hpre
  | calibrate var_s var_i var_d =>
      exact calibrate_preserves_wf var_s var_i var_d s hwf hpre
  | take_image var_s var_d var_i var_m =>
      exact take_image_preserves_wf var_s var_d var_i var_m s hwf hpre

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

def AllPowerAvailable (s : State) : Prop :=
  ∀ sat, s.statics.satellite_t sat = true →
    s.dynamic.power_avail_p sat = true

def turnSegment
    (satellite target current : Obj) : List PlanAction :=
  if current = target then
    []
  else
    [.turn_to satellite target current]

lemma find?_getD_of_exists
    {α : Type}
    (xs : List α)
    (p : α → Bool)
    (default : α)
    (h : ∃ x, x ∈ xs ∧ p x = true) :
    p ((xs.find? p).getD default) = true := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · simp [List.find?, ha]
      · rcases h with ⟨x, hx, hpx⟩
        have hxa : x ≠ a := by
          intro heq
          subst x
          exact ha hpx
        have hmem : x ∈ xs :=
          (List.mem_cons.mp hx).resolve_left hxa
        simpa [List.find?, ha] using
          ih ⟨x, hmem, hpx⟩

lemma findInstrumentForMode_spec
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    {mode : Obj}
    (hmode : st.mode_t mode = true) :
    st.instrument_t (findInstrumentForMode st mode) = true ∧
    st.supports_p (findInstrumentForMode st mode) mode = true := by
  have hmodes : ModeSupportedByInstrument st :=
    hstatic.2.2.2.2.2.1
  have hhier : ValidTypeHierarchy st :=
    hstatic.2.2.2.2.1
  rcases hmodes.1 mode hmode with ⟨i, hi, hsupports⟩
  have himem : i ∈ st.objects :=
    hhier.2.2.1 i hi
  have hfound :
      (st.instrument_t (findInstrumentForMode st mode) &&
        st.supports_p (findInstrumentForMode st mode) mode) = true := by
    unfold findInstrumentForMode
    exact find?_getD_of_exists
      st.objects
      (fun instrument =>
        st.instrument_t instrument &&
          st.supports_p instrument mode)
      0
      ⟨i, himem, by simp [hi, hsupports]⟩
  simpa only [Bool.and_eq_true] using hfound

lemma findSatelliteForInstrument_spec
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    {instrument : Obj}
    (hinstrument : st.instrument_t instrument = true) :
    st.satellite_t (findSatelliteForInstrument st instrument) = true ∧
    st.on_board_p instrument
      (findSatelliteForInstrument st instrument) = true := by
  have hexact : InstrumentOnBoardExactlyOneSatellite st :=
    hstatic.2.2.2.2.2.2.1
  have hhier : ValidTypeHierarchy st :=
    hstatic.2.2.2.2.1
  rcases hexact instrument hinstrument with
    ⟨sat, ⟨hsat, honBoard⟩, _⟩
  have hmem : sat ∈ st.objects :=
    hhier.1 sat hsat
  have hfound :
      (st.satellite_t (findSatelliteForInstrument st instrument) &&
        st.on_board_p instrument
          (findSatelliteForInstrument st instrument)) = true := by
    unfold findSatelliteForInstrument
    exact find?_getD_of_exists
      st.objects
      (fun satellite =>
        st.satellite_t satellite &&
          st.on_board_p instrument satellite)
      0
      ⟨sat, hmem, by simp [hsat, honBoard]⟩
  simpa only [Bool.and_eq_true] using hfound

lemma findCalibrationTarget_spec
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    {instrument : Obj}
    (hinstrument : st.instrument_t instrument = true) :
    st.direction_t (findCalibrationTarget st instrument) = true ∧
    st.calibration_target_p instrument
      (findCalibrationTarget st instrument) = true := by
  have htargets : InstrumentHasCalibrationTarget st :=
    hstatic.2.2.2.2.2.2.2.2.1
  have hhier : ValidTypeHierarchy st :=
    hstatic.2.2.2.2.1
  rcases htargets instrument hinstrument with
    ⟨dir, hdir, htarget⟩
  have hmem : dir ∈ st.objects :=
    hhier.2.1 dir hdir
  have hfound :
      (st.direction_t (findCalibrationTarget st instrument) &&
        st.calibration_target_p instrument
          (findCalibrationTarget st instrument)) = true := by
    unfold findCalibrationTarget
    exact find?_getD_of_exists
      st.objects
      (fun direction =>
        st.direction_t direction &&
          st.calibration_target_p instrument direction)
      0
      ⟨dir, hmem, by simp [hdir, htarget]⟩
  simpa only [Bool.and_eq_true] using hfound

lemma findCurrentDirection_spec
    (s : State)
    (hwf : WellFormed s)
    {satellite : Obj}
    (hsatellite : s.statics.satellite_t satellite = true) :
    s.statics.direction_t (findCurrentDirection s satellite) = true ∧
    s.dynamic.pointing_p satellite
      (findCurrentDirection s satellite) = true := by
  have hhas : SatelliteHasPointing s := by
    rcases hwf with
      ⟨_, _, _, _, _, _, _, _, _, _, hhas⟩
    exact hhas
  have hhier : ValidTypeHierarchy s.statics :=
    hwf.1.2.2.2.2.1
  rcases hhas satellite hsatellite with
    ⟨dir, hdir, hpoint⟩
  have hmem : dir ∈ s.statics.objects :=
    hhier.2.1 dir hdir
  have hfound :
      (s.statics.direction_t (findCurrentDirection s satellite) &&
        s.dynamic.pointing_p satellite
          (findCurrentDirection s satellite)) = true := by
    unfold findCurrentDirection
    exact find?_getD_of_exists
      s.statics.objects
      (fun direction =>
        s.statics.direction_t direction &&
          s.dynamic.pointing_p satellite direction)
      0
      ⟨dir, hmem, by simp [hdir, hpoint]⟩
  simpa only [Bool.and_eq_true] using hfound

lemma pointing_false_of_ne
    (s : State)
    (hwf : WellFormed s)
    {sat current target : Obj}
    (hsat : s.statics.satellite_t sat = true)
    (hcurrent : s.dynamic.pointing_p sat current = true)
    (hne : target ≠ current) :
    s.dynamic.pointing_p sat target = false := by
  have huniq : UniqueSatellitePointing s.statics s.dynamic := by
    rcases hwf with
      ⟨_, _, _, _, _, _, _, _, huniq, _, _⟩
    exact huniq
  cases htarget : s.dynamic.pointing_p sat target with
  | false =>
      rfl
  | true =>
      exfalso
      exact hne
        (huniq sat target current hsat htarget hcurrent)

lemma turnSegment_correct
    (s : State)
    (satellite target current : Obj)
    (hwf : WellFormed s)
    (hsat : s.statics.satellite_t satellite = true)
    (htarget : s.statics.direction_t target = true)
    (hcurrentDir : s.statics.direction_t current = true)
    (hcurrent :
      s.dynamic.pointing_p satellite current = true) :
    let p := turnSegment satellite target current
    let s' := runPlan p s
    ValidPlan p s ∧
    WellFormed s' ∧
    s'.dynamic.pointing_p satellite target = true ∧
    s'.dynamic.power_avail_p = s.dynamic.power_avail_p ∧
    s'.dynamic.power_on_p = s.dynamic.power_on_p ∧
    s'.dynamic.calibrated_p = s.dynamic.calibrated_p ∧
    s'.dynamic.have_image_p = s.dynamic.have_image_p ∧
    (∀ sat' dir',
      s.dynamic.pointing_p sat' dir' = true →
      (sat' ≠ satellite ∨ dir' = target) →
      s'.dynamic.pointing_p sat' dir' = true) := by
  dsimp only
  by_cases heq : current = target
  · subst target
    have hp :
        turnSegment satellite current current = [] := by
      simp [turnSegment]
    rw [hp]
    simp only [runPlan]
    refine
      ⟨by simp [ValidPlan],
       hwf,
       hcurrent,
       by trivial,
       by trivial,
       by trivial,
       by trivial,
       ?_⟩
    intro sat' dir' hpoint _
    exact hpoint
  · have htargetFalse :
        s.dynamic.pointing_p satellite target = false :=
      pointing_false_of_ne
        s hwf hsat hcurrent (fun h => heq h.symm)
    have hpre :
        turn_toPre satellite target current s :=
      ⟨hsat, htarget, hcurrentDir, hcurrent, htargetFalse⟩
    have hwf' :
        WellFormed (turn_to satellite target current s) :=
      turn_to_preserves_wf
        satellite target current s hwf hpre
    have hvalid :
        ValidPlan (turnSegment satellite target current) s := by
      simp [turnSegment, heq, ValidPlan, actionPre, hpre]
    have hrun :
        runPlan (turnSegment satellite target current) s =
          turn_to satellite target current s := by
      simp [turnSegment, heq, runPlan, actionApply]
    rw [hrun]
    refine
      ⟨hvalid,
       hwf',
       turn_to_pointing_p_eq1 satellite target current s,
       rfl,
       rfl,
       rfl,
       rfl,
       ?_⟩
    intro sat' dir' hpoint hcompatible
    rcases hcompatible with hsatNe | hdirEq
    · simpa [turn_to, hsatNe] using hpoint
    · subst dir'
      by_cases hs : sat' = satellite
      · subst sat'
        exact turn_to_pointing_p_eq1 satellite target current s
      · simpa [turn_to, hs] using hpoint

lemma makeImagePlan_correct
    (s : State)
    (direction mode : Obj)
    (hwf : WellFormed s)
    (havail : AllPowerAvailable s)
    (hdirection : s.statics.direction_t direction = true)
    (hmode : s.statics.mode_t mode = true) :
    let p := makeImagePlan s direction mode
    let s' := runPlan p s
    ValidPlan p s ∧
    WellFormed s' ∧
    AllPowerAvailable s' ∧
    s'.dynamic.have_image_p direction mode = true ∧
    (∀ d m,
      s.dynamic.have_image_p d m = true →
      s'.dynamic.have_image_p d m = true) := by
  let instrument := findInstrumentForMode s.statics mode
  let satellite :=
    findSatelliteForInstrument s.statics instrument
  let calibrationDirection :=
    findCalibrationTarget s.statics instrument
  let currentDirection :=
    findCurrentDirection s satellite

  have hi :
      s.statics.instrument_t instrument = true ∧
      s.statics.supports_p instrument mode = true :=
    findInstrumentForMode_spec s.statics hwf.1 hmode

  have hsat :
      s.statics.satellite_t satellite = true ∧
      s.statics.on_board_p instrument satellite = true :=
    findSatelliteForInstrument_spec s.statics hwf.1 hi.1

  have hcal :
      s.statics.direction_t calibrationDirection = true ∧
      s.statics.calibration_target_p instrument
        calibrationDirection = true :=
    findCalibrationTarget_spec s.statics hwf.1 hi.1

  have hcur :
      s.statics.direction_t currentDirection = true ∧
      s.dynamic.pointing_p satellite currentDirection = true :=
    findCurrentDirection_spec s hwf hsat.1

  let s₁ := switch_on instrument satellite s

  have hstat₁ : s₁.statics = s.statics := by
    rfl

  have hpreOn : switch_onPre instrument satellite s :=
    ⟨hi.1, hsat.1, hsat.2, havail satellite hsat.1⟩

  have hwf₁ : WellFormed s₁ :=
    switch_on_preserves_wf instrument satellite s hwf hpreOn

  have hcur₁ :
      s₁.dynamic.pointing_p satellite currentDirection = true := by
    simpa [s₁, switch_on] using hcur.2

  have hsat₁ :
      s₁.statics.satellite_t satellite = true := by
    rw [hstat₁]
    exact hsat.1

  have hcalDir₁ :
      s₁.statics.direction_t calibrationDirection = true := by
    rw [hstat₁]
    exact hcal.1

  have hcurDir₁ :
      s₁.statics.direction_t currentDirection = true := by
    rw [hstat₁]
    exact hcur.1

  let calibrationPlan :=
    turnSegment satellite calibrationDirection currentDirection
  let s₂ := runPlan calibrationPlan s₁

  have hcalTurn :=
    turnSegment_correct
      s₁ satellite calibrationDirection currentDirection
      hwf₁ hsat₁ hcalDir₁ hcurDir₁ hcur₁

  have hvalidCalTurn : ValidPlan calibrationPlan s₁ := by
    simpa [calibrationPlan, s₂] using hcalTurn.1

  have hwf₂ : WellFormed s₂ := by
    simpa [calibrationPlan, s₂] using hcalTurn.2.1

  have hpointCal :
      s₂.dynamic.pointing_p satellite calibrationDirection = true := by
    simpa [calibrationPlan, s₂] using hcalTurn.2.2.1

  have hpowerOn₂ :
      s₂.dynamic.power_on_p instrument = true := by
    have heq :
        s₂.dynamic.power_on_p = s₁.dynamic.power_on_p := by
      simpa [calibrationPlan, s₂] using
        hcalTurn.2.2.2.2.1
    rw [heq]
    simp [s₁, switch_on]

  have hstat₂ : s₂.statics = s.statics := by
    exact
      (runPlan_statics calibrationPlan s₁).trans hstat₁

  let s₃ :=
    calibrate satellite instrument calibrationDirection s₂

  have hpreCal :
      calibratePre satellite instrument calibrationDirection s₂ := by
    unfold calibratePre
    rw [hstat₂]
    exact
      ⟨hsat.1, hi.1, hcal.1, hsat.2, hcal.2,
       hpointCal, hpowerOn₂⟩

  have hwf₃ : WellFormed s₃ :=
    calibrate_preserves_wf
      satellite instrument calibrationDirection
      s₂ hwf₂ hpreCal

  have hstat₃ : s₃.statics = s.statics := by
    change s₂.statics = s.statics
    exact hstat₂

  have hcalibrated₃ :
      s₃.dynamic.calibrated_p instrument = true := by
    simp [s₃, calibrate]

  have hpowerOn₃ :
      s₃.dynamic.power_on_p instrument = true := by
    simpa [s₃, calibrate] using hpowerOn₂

  have hpointCal₃ :
      s₃.dynamic.pointing_p satellite calibrationDirection = true := by
    simpa [s₃, calibrate] using hpointCal

  have hsat₃ :
      s₃.statics.satellite_t satellite = true := by
    rw [hstat₃]
    exact hsat.1

  have hdir₃ :
      s₃.statics.direction_t direction = true := by
    rw [hstat₃]
    exact hdirection

  have hcalDir₃ :
      s₃.statics.direction_t calibrationDirection = true := by
    rw [hstat₃]
    exact hcal.1

  let imageTurnPlan :=
    turnSegment satellite direction calibrationDirection
  let s₄ := runPlan imageTurnPlan s₃

  have himageTurn :=
    turnSegment_correct
      s₃ satellite direction calibrationDirection
      hwf₃ hsat₃ hdir₃ hcalDir₃ hpointCal₃

  have hvalidImageTurn : ValidPlan imageTurnPlan s₃ := by
    simpa [imageTurnPlan, s₄] using himageTurn.1

  have hwf₄ : WellFormed s₄ := by
    simpa [imageTurnPlan, s₄] using himageTurn.2.1

  have hpointImage :
      s₄.dynamic.pointing_p satellite direction = true := by
    simpa [imageTurnPlan, s₄] using himageTurn.2.2.1

  have hpowerOn₄ :
      s₄.dynamic.power_on_p instrument = true := by
    have heq :
        s₄.dynamic.power_on_p = s₃.dynamic.power_on_p := by
      simpa [imageTurnPlan, s₄] using
        himageTurn.2.2.2.2.1
    rw [heq]
    exact hpowerOn₃

  have hcalibrated₄ :
      s₄.dynamic.calibrated_p instrument = true := by
    have heq :
        s₄.dynamic.calibrated_p = s₃.dynamic.calibrated_p := by
      simpa [imageTurnPlan, s₄] using
        himageTurn.2.2.2.2.2.1
    rw [heq]
    exact hcalibrated₃

  have hstat₄ : s₄.statics = s.statics := by
    exact
      (runPlan_statics imageTurnPlan s₃).trans hstat₃

  let s₅ :=
    take_image satellite direction instrument mode s₄

  have hpreImage :
      take_imagePre satellite direction instrument mode s₄ := by
    unfold take_imagePre
    rw [hstat₄]
    exact
      ⟨hsat.1, hdirection, hi.1, hmode, hcalibrated₄,
       hsat.2, hi.2, hpowerOn₄, hpointImage⟩

  have hwf₅ : WellFormed s₅ :=
    take_image_preserves_wf
      satellite direction instrument mode
      s₄ hwf₄ hpreImage

  have hstat₅ : s₅.statics = s.statics := by
    change s₄.statics = s.statics
    exact hstat₄

  have hpowerOn₅ :
      s₅.dynamic.power_on_p instrument = true := by
    simpa [s₅, take_image] using hpowerOn₄

  let s₆ := switch_off instrument satellite s₅

  have hpreOff :
      switch_offPre instrument satellite s₅ := by
    unfold switch_offPre
    rw [hstat₅]
    exact ⟨hi.1, hsat.1, hsat.2, hpowerOn₅⟩

  have hwf₆ : WellFormed s₆ :=
    switch_off_preserves_wf
      instrument satellite s₅ hwf₅ hpreOff

  have hstat₆ : s₆.statics = s.statics := by
    change s₅.statics = s.statics
    exact hstat₅

  have hvalidOn :
      ValidPlan [.switch_on instrument satellite] s := by
    exact ⟨hpreOn, trivial⟩

  have hvalidCal :
      ValidPlan
        [.calibrate satellite instrument calibrationDirection] s₂ := by
    exact ⟨hpreCal, trivial⟩

  have hvalidTail :
      ValidPlan
        [.take_image satellite direction instrument mode,
         .switch_off instrument satellite] s₄ := by
    exact ⟨hpreImage, hpreOff, trivial⟩

  have hplanEq :
      makeImagePlan s direction mode =
        [.switch_on instrument satellite] ++
          (calibrationPlan ++
            ([.calibrate satellite instrument calibrationDirection] ++
              (imageTurnPlan ++
                [.take_image satellite direction instrument mode,
                 .switch_off instrument satellite]))) := by
    simp [makeImagePlan, instrument, satellite,
      calibrationDirection, currentDirection,
      calibrationPlan, imageTurnPlan, turnSegment,
      List.append_assoc]

  have hvalid :
      ValidPlan (makeImagePlan s direction mode) s := by
    rw [hplanEq]
    apply (validPlan_append _ _ _).2
    refine ⟨hvalidOn, ?_⟩
    change
      ValidPlan
        (calibrationPlan ++
          ([.calibrate satellite instrument calibrationDirection] ++
            (imageTurnPlan ++
              [.take_image satellite direction instrument mode,
               .switch_off instrument satellite]))) s₁
    apply (validPlan_append _ _ _).2
    refine ⟨hvalidCalTurn, ?_⟩
    change
      ValidPlan
        ([.calibrate satellite instrument calibrationDirection] ++
          (imageTurnPlan ++
            [.take_image satellite direction instrument mode,
             .switch_off instrument satellite])) s₂
    apply (validPlan_append _ _ _).2
    refine ⟨hvalidCal, ?_⟩
    change
      ValidPlan
        (imageTurnPlan ++
          [.take_image satellite direction instrument mode,
           .switch_off instrument satellite]) s₃
    exact
      (validPlan_append _ _ _).2
        ⟨hvalidImageTurn, hvalidTail⟩

  have hrun :
      runPlan (makeImagePlan s direction mode) s = s₆ := by
    rw [hplanEq]
    rw [runPlan_append]
    change
      runPlan
        (calibrationPlan ++
          ([.calibrate satellite instrument calibrationDirection] ++
            (imageTurnPlan ++
              [.take_image satellite direction instrument mode,
               .switch_off instrument satellite]))) s₁ = s₆
    rw [runPlan_append]
    change
      runPlan
        ([.calibrate satellite instrument calibrationDirection] ++
          (imageTurnPlan ++
            [.take_image satellite direction instrument mode,
             .switch_off instrument satellite])) s₂ = s₆
    rw [runPlan_append]
    change
      runPlan
        (imageTurnPlan ++
          [.take_image satellite direction instrument mode,
           .switch_off instrument satellite]) s₃ = s₆
    rw [runPlan_append]
    change
      runPlan
        [.take_image satellite direction instrument mode,
         .switch_off instrument satellite] s₄ = s₆
    simp [runPlan, actionApply, s₅, s₆]

  have havailable₆ : AllPowerAvailable s₆ := by
    intro sat' hsat'
    have hsatOld :
        s.statics.satellite_t sat' = true := by
      rw [← hstat₆]
      exact hsat'
    by_cases heq : sat' = satellite
    · subst sat'
      simp [s₆, switch_off]
    · have hAvailOld :
          s.dynamic.power_avail_p sat' = true :=
        havail sat' hsatOld
      have hCalTurnPower :
          s₂.dynamic.power_avail_p =
            s₁.dynamic.power_avail_p := by
        simpa [calibrationPlan, s₂] using
          hcalTurn.2.2.2.1
      have hImageTurnPower :
          s₄.dynamic.power_avail_p =
            s₃.dynamic.power_avail_p := by
        simpa [imageTurnPlan, s₄] using
          himageTurn.2.2.2.1
      change
        (switch_off instrument satellite s₅).dynamic.power_avail_p
          sat' = true
      simp only [switch_off]
      simp [heq]
      change s₅.dynamic.power_avail_p sat' = true
      change s₄.dynamic.power_avail_p sat' = true
      rw [hImageTurnPower]
      change s₂.dynamic.power_avail_p sat' = true
      rw [hCalTurnPower]
      change
        (switch_on instrument satellite s).dynamic.power_avail_p
          sat' = true
      simpa [switch_on, heq] using hAvailOld

  have himage₆ :
      s₆.dynamic.have_image_p direction mode = true := by
    simp [s₆, switch_off, s₅, take_image]

  have hpreserves :
      ∀ d m,
        s.dynamic.have_image_p d m = true →
        s₆.dynamic.have_image_p d m = true := by
    intro d m himage
    have hCalTurnImages :
        s₂.dynamic.have_image_p = s₁.dynamic.have_image_p := by
      simpa [calibrationPlan, s₂] using
        hcalTurn.2.2.2.2.2.2.1
    have hImageTurnImages :
        s₄.dynamic.have_image_p = s₃.dynamic.have_image_p := by
      simpa [imageTurnPlan, s₄] using
        himageTurn.2.2.2.2.2.2.1
    change
      (switch_off instrument satellite s₅).dynamic.have_image_p
        d m = true
    change s₅.dynamic.have_image_p d m = true
    change
      (take_image satellite direction instrument mode s₄).dynamic.have_image_p
        d m = true
    by_cases hpair : d = direction ∧ m = mode
    · simp [take_image, hpair]
    · simp [take_image, hpair]
      rw [hImageTurnImages]
      change s₂.dynamic.have_image_p d m = true
      rw [hCalTurnImages]
      simpa [s₁, switch_on] using himage

  dsimp only
  rw [hrun]
  exact
    ⟨hvalid, hwf₆, havailable₆, himage₆, hpreserves⟩

lemma requiredImages_spec
    (s : State)
    (g : Goal)
    (direction mode : Obj) :
    (direction, mode) ∈ requiredImages s g ↔
      direction ∈ s.statics.objects ∧
      mode ∈ s.statics.objects ∧
      g.dynamic.have_image_p direction mode = some true := by
  simp [requiredImages]

lemma requiredPointings_spec
    (s : State)
    (g : Goal)
    (satellite direction : Obj) :
    (satellite, direction) ∈ requiredPointings s g ↔
      satellite ∈ s.statics.objects ∧
      direction ∈ s.statics.objects ∧
      g.dynamic.pointing_p satellite direction = some true := by
  simp [requiredPointings]

lemma solveImageGoals_correct
    (goals : List (Obj × Obj))
    (s : State)
    (hwf : WellFormed s)
    (havail : AllPowerAvailable s)
    (htyped :
      ∀ p ∈ goals,
        s.statics.direction_t p.1 = true ∧
        s.statics.mode_t p.2 = true) :
    let plan := solveImageGoals goals s
    let s' := runPlan plan s
    ValidPlan plan s ∧
    WellFormed s' ∧
    AllPowerAvailable s' ∧
    (∀ p ∈ goals,
      s'.dynamic.have_image_p p.1 p.2 = true) ∧
    (∀ d m,
      s.dynamic.have_image_p d m = true →
      s'.dynamic.have_image_p d m = true) := by
  induction goals generalizing s with
  | nil =>
      simp [solveImageGoals, runPlan, ValidPlan, hwf, havail]
  | cons goal goals ih =>
      rcases goal with ⟨direction, mode⟩
      have hhead :=
        htyped (direction, mode) (by simp)

      let imagePlan := makeImagePlan s direction mode
      let nextState := runPlan imagePlan s

      have himage :=
        makeImagePlan_correct
          s direction mode hwf havail hhead.1 hhead.2

      have hvalidImage : ValidPlan imagePlan s := by
        simpa [imagePlan, nextState] using himage.1

      have hwfNext : WellFormed nextState := by
        simpa [imagePlan, nextState] using himage.2.1

      have havailNext : AllPowerAvailable nextState := by
        simpa [imagePlan, nextState] using himage.2.2.1

      have hheadImage :
          nextState.dynamic.have_image_p direction mode = true := by
        simpa [imagePlan, nextState] using himage.2.2.2.1

      have himagePreserved :
          ∀ d m,
            s.dynamic.have_image_p d m = true →
            nextState.dynamic.have_image_p d m = true := by
        simpa [imagePlan, nextState] using himage.2.2.2.2

      have htypedTail :
          ∀ p ∈ goals,
            nextState.statics.direction_t p.1 = true ∧
            nextState.statics.mode_t p.2 = true := by
        intro p hp
        have h := htyped p (by simp [hp])
        have hstat :
            nextState.statics = s.statics := by
          exact runPlan_statics imagePlan s
        rw [hstat]
        exact h

      have htail :=
        ih nextState hwfNext havailNext htypedTail

      let tailPlan := solveImageGoals goals nextState
      let finalState := runPlan tailPlan nextState

      have hvalidTail : ValidPlan tailPlan nextState := by
        simpa [tailPlan, finalState] using htail.1

      have hwfFinal : WellFormed finalState := by
        simpa [tailPlan, finalState] using htail.2.1

      have havailFinal : AllPowerAvailable finalState := by
        simpa [tailPlan, finalState] using htail.2.2.1

      have htailGoals :
          ∀ p ∈ goals,
            finalState.dynamic.have_image_p p.1 p.2 = true := by
        simpa [tailPlan, finalState] using htail.2.2.2.1

      have htailPreserves :
          ∀ d m,
            nextState.dynamic.have_image_p d m = true →
            finalState.dynamic.have_image_p d m = true := by
        simpa [tailPlan, finalState] using htail.2.2.2.2

      dsimp only
      simp only [solveImageGoals]
      change
        ValidPlan (imagePlan ++ tailPlan) s ∧
        WellFormed (runPlan (imagePlan ++ tailPlan) s) ∧
        AllPowerAvailable (runPlan (imagePlan ++ tailPlan) s) ∧
        (∀ p ∈ (direction, mode) :: goals,
          (runPlan (imagePlan ++ tailPlan) s).dynamic.have_image_p
            p.1 p.2 = true) ∧
        ∀ d m,
          s.dynamic.have_image_p d m = true →
          (runPlan (imagePlan ++ tailPlan) s).dynamic.have_image_p
            d m = true
      rw [runPlan_append]
      change
        ValidPlan (imagePlan ++ tailPlan) s ∧
        WellFormed finalState ∧
        AllPowerAvailable finalState ∧
        (∀ p ∈ (direction, mode) :: goals,
          finalState.dynamic.have_image_p p.1 p.2 = true) ∧
        ∀ d m,
          s.dynamic.have_image_p d m = true →
          finalState.dynamic.have_image_p d m = true
      refine
        ⟨(validPlan_append _ _ _).2
            ⟨hvalidImage, hvalidTail⟩,
         hwfFinal,
         havailFinal,
         ?_,
         ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact
            htailPreserves direction mode hheadImage
        · exact htailGoals p hp
      · intro d m hOld
        exact
          htailPreserves d m
            (himagePreserved d m hOld)

lemma makePointingPlan_correct
    (s : State)
    (satellite direction : Obj)
    (hwf : WellFormed s)
    (hsat : s.statics.satellite_t satellite = true)
    (hdir : s.statics.direction_t direction = true) :
    let p := makePointingPlan s satellite direction
    let s' := runPlan p s
    ValidPlan p s ∧
    WellFormed s' ∧
    s'.dynamic.pointing_p satellite direction = true ∧
    (∀ sat' dir',
      s.dynamic.pointing_p sat' dir' = true →
      (sat' ≠ satellite ∨ dir' = direction) →
      s'.dynamic.pointing_p sat' dir' = true) := by
  let current := findCurrentDirection s satellite
  have hcurrent :=
    findCurrentDirection_spec s hwf hsat
  have hturn :=
    turnSegment_correct
      s satellite direction current
      hwf hsat hdir hcurrent.1 hcurrent.2
  have heq :
      makePointingPlan s satellite direction =
        turnSegment satellite direction current := by
    rfl
  dsimp only
  rw [heq]
  exact
    ⟨hturn.1,
     hturn.2.1,
     hturn.2.2.1,
     hturn.2.2.2.2.2.2.2⟩

lemma solvePointingGoals_correct
    (goals : List (Obj × Obj))
    (s : State)
    (hwf : WellFormed s)
    (htyped :
      ∀ p ∈ goals,
        s.statics.satellite_t p.1 = true ∧
        s.statics.direction_t p.2 = true)
    (hcompatible :
      ∀ p ∈ goals, ∀ q ∈ goals,
        p.1 = q.1 → p.2 = q.2) :
    let plan := solvePointingGoals goals s
    let s' := runPlan plan s
    ValidPlan plan s ∧
    WellFormed s' ∧
    (∀ p ∈ goals,
      s'.dynamic.pointing_p p.1 p.2 = true) ∧
    (∀ sat dir,
      s.dynamic.pointing_p sat dir = true →
      (∀ p ∈ goals, sat ≠ p.1 ∨ dir = p.2) →
      s'.dynamic.pointing_p sat dir = true) := by
  induction goals generalizing s with
  | nil =>
      simp [solvePointingGoals, runPlan, ValidPlan, hwf]
  | cons goal goals ih =>
      rcases goal with ⟨satellite, direction⟩
      have hhead :=
        htyped (satellite, direction) (by simp)

      let pointingPlan :=
        makePointingPlan s satellite direction
      let nextState := runPlan pointingPlan s

      have hpointing :=
        makePointingPlan_correct
          s satellite direction hwf hhead.1 hhead.2

      have hvalidPointing : ValidPlan pointingPlan s := by
        simpa [pointingPlan, nextState] using hpointing.1

      have hwfNext : WellFormed nextState := by
        simpa [pointingPlan, nextState] using hpointing.2.1

      have hheadPoint :
          nextState.dynamic.pointing_p satellite direction = true := by
        simpa [pointingPlan, nextState] using
          hpointing.2.2.1

      have hpointPreserves :
          ∀ sat' dir',
            s.dynamic.pointing_p sat' dir' = true →
            (sat' ≠ satellite ∨ dir' = direction) →
            nextState.dynamic.pointing_p sat' dir' = true := by
        simpa [pointingPlan, nextState] using
          hpointing.2.2.2

      have htypedTail :
          ∀ p ∈ goals,
            nextState.statics.satellite_t p.1 = true ∧
            nextState.statics.direction_t p.2 = true := by
        intro p hp
        have h := htyped p (by simp [hp])
        have hstat :
            nextState.statics = s.statics := by
          exact runPlan_statics pointingPlan s
        rw [hstat]
        exact h

      have hcompatibleTail :
          ∀ p ∈ goals, ∀ q ∈ goals,
            p.1 = q.1 → p.2 = q.2 := by
        intro p hp q hq
        exact
          hcompatible p (by simp [hp]) q (by simp [hq])

      have htail :=
        ih nextState hwfNext htypedTail hcompatibleTail

      let tailPlan :=
        solvePointingGoals goals nextState
      let finalState := runPlan tailPlan nextState

      have hvalidTail : ValidPlan tailPlan nextState := by
        simpa [tailPlan, finalState] using htail.1

      have hwfFinal : WellFormed finalState := by
        simpa [tailPlan, finalState] using htail.2.1

      have htailGoals :
          ∀ p ∈ goals,
            finalState.dynamic.pointing_p p.1 p.2 = true := by
        simpa [tailPlan, finalState] using htail.2.2.1

      have htailPreserves :
          ∀ sat dir,
            nextState.dynamic.pointing_p sat dir = true →
            (∀ p ∈ goals, sat ≠ p.1 ∨ dir = p.2) →
            finalState.dynamic.pointing_p sat dir = true := by
        simpa [tailPlan, finalState] using htail.2.2.2

      have hheadCompatible :
          ∀ p ∈ goals,
            satellite ≠ p.1 ∨ direction = p.2 := by
        intro p hp
        by_cases hs : satellite = p.1
        · right
          exact
            hcompatible
              (satellite, direction) (by simp)
              p (by simp [hp]) hs
        · exact Or.inl hs

      dsimp only
      simp only [solvePointingGoals]
      change
        ValidPlan (pointingPlan ++ tailPlan) s ∧
        WellFormed (runPlan (pointingPlan ++ tailPlan) s) ∧
        (∀ p ∈ (satellite, direction) :: goals,
          (runPlan (pointingPlan ++ tailPlan) s).dynamic.pointing_p
            p.1 p.2 = true) ∧
        ∀ sat dir,
          s.dynamic.pointing_p sat dir = true →
          (∀ p ∈ (satellite, direction) :: goals,
            sat ≠ p.1 ∨ dir = p.2) →
          (runPlan (pointingPlan ++ tailPlan) s).dynamic.pointing_p
            sat dir = true
      rw [runPlan_append]
      change
        ValidPlan (pointingPlan ++ tailPlan) s ∧
        WellFormed finalState ∧
        (∀ p ∈ (satellite, direction) :: goals,
          finalState.dynamic.pointing_p p.1 p.2 = true) ∧
        ∀ sat dir,
          s.dynamic.pointing_p sat dir = true →
          (∀ p ∈ (satellite, direction) :: goals,
            sat ≠ p.1 ∨ dir = p.2) →
          finalState.dynamic.pointing_p sat dir = true
      refine
        ⟨(validPlan_append _ _ _).2
            ⟨hvalidPointing, hvalidTail⟩,
         hwfFinal,
         ?_,
         ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact
            htailPreserves satellite direction
              hheadPoint hheadCompatible
        · exact htailGoals p hp
      · intro sat dir hOld hcompat
        have hheadCompat :
            sat ≠ satellite ∨ dir = direction :=
          hcompat (satellite, direction) (by simp)
        have hnext :=
          hpointPreserves sat dir hOld hheadCompat
        apply htailPreserves sat dir hnext
        intro p hp
        exact hcompat p (by simp [hp])

lemma runPlan_preserves_have_image_true
    (plan : List PlanAction)
    (s : State)
    {direction mode : Obj}
    (himage : s.dynamic.have_image_p direction mode = true) :
    (runPlan plan s).dynamic.have_image_p direction mode = true := by
  induction plan generalizing s with
  | nil =>
      simpa [runPlan] using himage
  | cons action plan ih =>
      apply ih
      cases action with
      | turn_to sat target current =>
          simpa [actionApply, turn_to] using himage
      | switch_on instrument sat =>
          simpa [actionApply, switch_on] using himage
      | switch_off instrument sat =>
          simpa [actionApply, switch_off] using himage
      | calibrate sat instrument direction' =>
          simpa [actionApply, calibrate] using himage
      | take_image sat d instrument m =>
          by_cases hpair : direction = d ∧ mode = m
          · simp [actionApply, take_image, hpair]
          · simpa [actionApply, take_image, hpair] using himage


-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  have hwf : WellFormed s :=
    hinit.1

  have havail : AllPowerAvailable s := by
    intro sat hsat
    exact hinit.2 sat hsat

  have hgoalImageValid :
      ValidHaveImageParam s.statics g.dynamic :=
    hgoal.2.2.2.2.2.1

  have hgoalPointValid :
      ValidPointingParam s.statics g.dynamic :=
    hgoal.2.1

  have hgoalUnique :
      UniqueSatellitePointing s.statics g.dynamic :=
    hgoal.2.2.2.2.2.2.2.2.1

  have hignoreAvail : GoalIgnorePowerAvail s g :=
    hgoal.2.2.2.2.2.2.2.2.2.2.1

  have hignoreOn : GoalIgnorePowerOn s g :=
    hgoal.2.2.2.2.2.2.2.2.2.2.2.1

  have hignoreCal : GoalIgnoreCalibrated s g :=
    hgoal.2.2.2.2.2.2.2.2.2.2.2.2.1

  have hpositive : GoalOnlyPositive s g :=
    hgoal.2.2.2.2.2.2.2.2.2.2.2.2.2

  let imageGoals := requiredImages s g
  let imagePlan := solveImageGoals imageGoals s
  let stateAfterImages := runPlan imagePlan s

  have himageTyped :
      ∀ p ∈ imageGoals,
        s.statics.direction_t p.1 = true ∧
        s.statics.mode_t p.2 = true := by
    intro p hp
    rcases p with ⟨direction, mode⟩
    have hrequested :
        g.dynamic.have_image_p direction mode = some true :=
      ((requiredImages_spec s g direction mode).1 hp).2.2
    exact hgoalImageValid direction mode hrequested

  have himageSolve :=
    solveImageGoals_correct
      imageGoals s hwf havail himageTyped

  have hvalidImages : ValidPlan imagePlan s := by
    simpa [imagePlan, imageGoals, stateAfterImages] using
      himageSolve.1

  have hwfAfterImages : WellFormed stateAfterImages := by
    simpa [imagePlan, imageGoals, stateAfterImages] using
      himageSolve.2.1

  have himageGoals :
      ∀ p ∈ imageGoals,
        stateAfterImages.dynamic.have_image_p p.1 p.2 = true := by
    simpa [imagePlan, imageGoals, stateAfterImages] using
      himageSolve.2.2.2.1

  let pointingGoals := requiredPointings s g
  let pointingPlan :=
    solvePointingGoals pointingGoals stateAfterImages
  let finalState := runPlan pointingPlan stateAfterImages

  have hpointTyped :
      ∀ p ∈ pointingGoals,
        stateAfterImages.statics.satellite_t p.1 = true ∧
        stateAfterImages.statics.direction_t p.2 = true := by
    intro p hp
    rcases p with ⟨satellite, direction⟩
    have hrequested :
        g.dynamic.pointing_p satellite direction = some true :=
      ((requiredPointings_spec s g satellite direction).1 hp).2.2
    have htypes :=
      hgoalPointValid satellite direction hrequested
    have hstat :
        stateAfterImages.statics = s.statics := by
      exact runPlan_statics imagePlan s
    rw [hstat]
    exact htypes

  have hpointCompatible :
      ∀ p ∈ pointingGoals, ∀ q ∈ pointingGoals,
        p.1 = q.1 → p.2 = q.2 := by
    intro p hp q hq hsatEq
    rcases p with ⟨sat₁, dir₁⟩
    rcases q with ⟨sat₂, dir₂⟩
    simp only at hsatEq
    subst sat₂
    have hpReq :
        g.dynamic.pointing_p sat₁ dir₁ = some true :=
      ((requiredPointings_spec s g sat₁ dir₁).1 hp).2.2
    have hqReq :
        g.dynamic.pointing_p sat₁ dir₂ = some true :=
      ((requiredPointings_spec s g sat₁ dir₂).1 hq).2.2
    have hsatType :=
      (hgoalPointValid sat₁ dir₁ hpReq).1
    exact
      hgoalUnique sat₁ dir₁ dir₂
        hsatType hpReq hqReq

  have hpointSolve :=
    solvePointingGoals_correct
      pointingGoals stateAfterImages
      hwfAfterImages hpointTyped hpointCompatible

  have hvalidPointings :
      ValidPlan pointingPlan stateAfterImages := by
    simpa [pointingPlan, pointingGoals, finalState] using
      hpointSolve.1

  have hfinalPointings :
      ∀ p ∈ pointingGoals,
        finalState.dynamic.pointing_p p.1 p.2 = true := by
    simpa [pointingPlan, pointingGoals, finalState] using
      hpointSolve.2.2.1

  have hvalidSolve : ValidPlan (solve s g) s := by
    unfold solve
    change ValidPlan (imagePlan ++ pointingPlan) s
    exact
      (validPlan_append _ _ _).2
        ⟨hvalidImages, hvalidPointings⟩

  have hrunSolve :
      runPlan (solve s g) s = finalState := by
    unfold solve
    change
      runPlan (imagePlan ++ pointingPlan) s = finalState
    rw [runPlan_append]

  have hfinalImages :
      ∀ p ∈ imageGoals,
        finalState.dynamic.have_image_p p.1 p.2 = true := by
    intro p hp
    exact
      runPlan_preserves_have_image_true
        pointingPlan stateAfterImages
        (himageGoals p hp)

  have hpointGoal :
      ∀ satellite direction,
        match g.dynamic.pointing_p satellite direction with
        | none => True
        | some b =>
            finalState.dynamic.pointing_p satellite direction = b := by
    intro satellite direction
    by_cases htrue :
        g.dynamic.pointing_p satellite direction = some true
    · have htypes :=
        hgoalPointValid satellite direction htrue
      have hhier : ValidTypeHierarchy s.statics :=
        hstatic.2.2.2.2.1
      have hsatMem : satellite ∈ s.statics.objects :=
        hhier.1 satellite htypes.1
      have hdirMem : direction ∈ s.statics.objects :=
        hhier.2.1 direction htypes.2
      have hmem :
          (satellite, direction) ∈ pointingGoals := by
        apply
          (requiredPointings_spec
            s g satellite direction).2
        exact ⟨hsatMem, hdirMem, htrue⟩
      rw [htrue]
      exact
        hfinalPointings
          (satellite, direction) hmem
    · have hfalse :
          g.dynamic.pointing_p satellite direction ≠ some false :=
        (hpositive satellite direction).1
      have hnone :
          g.dynamic.pointing_p satellite direction = none := by
        cases hopt :
            g.dynamic.pointing_p satellite direction with
        | none =>
            rfl
        | some b =>
            cases b with
            | false =>
                exact False.elim (hfalse hopt)
            | true =>
                exact False.elim (htrue hopt)
      simp [hnone]

  have hpavailGoal :
      ∀ satellite,
        match g.dynamic.power_avail_p satellite with
        | none => True
        | some b =>
            finalState.dynamic.power_avail_p satellite = b := by
    intro satellite
    simp [hignoreAvail satellite]

  have hponGoal :
      ∀ instrument,
        match g.dynamic.power_on_p instrument with
        | none => True
        | some b =>
            finalState.dynamic.power_on_p instrument = b := by
    intro instrument
    simp [hignoreOn instrument]

  have hcalGoal :
      ∀ instrument,
        match g.dynamic.calibrated_p instrument with
        | none => True
        | some b =>
            finalState.dynamic.calibrated_p instrument = b := by
    intro instrument
    simp [hignoreCal instrument]

  have himageGoal :
      ∀ direction mode,
        match g.dynamic.have_image_p direction mode with
        | none => True
        | some b =>
            finalState.dynamic.have_image_p direction mode = b := by
    intro direction mode
    by_cases htrue :
        g.dynamic.have_image_p direction mode = some true
    · have htypes :=
        hgoalImageValid direction mode htrue
      have hhier : ValidTypeHierarchy s.statics :=
        hstatic.2.2.2.2.1
      have hdirMem : direction ∈ s.statics.objects :=
        hhier.2.1 direction htypes.1
      have hmodeMem : mode ∈ s.statics.objects :=
        hhier.2.2.2.1 mode htypes.2
      have hmem :
          (direction, mode) ∈ imageGoals := by
        apply
          (requiredImages_spec
            s g direction mode).2
        exact ⟨hdirMem, hmodeMem, htrue⟩
      rw [htrue]
      exact hfinalImages (direction, mode) hmem
    · have hfalse :
          g.dynamic.have_image_p direction mode ≠ some false :=
        (hpositive direction mode).2 direction mode
      have hnone :
          g.dynamic.have_image_p direction mode = none := by
        cases hopt :
            g.dynamic.have_image_p direction mode with
        | none =>
            rfl
        | some b =>
            cases b with
            | false =>
                exact False.elim (hfalse hopt)
            | true =>
                exact False.elim (htrue hopt)
      simp [hnone]

  refine ⟨hvalidSolve, ?_⟩
  rw [hrunSolve]
  exact
    ⟨hpointGoal, hpavailGoal, hponGoal, hcalGoal, himageGoal⟩

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

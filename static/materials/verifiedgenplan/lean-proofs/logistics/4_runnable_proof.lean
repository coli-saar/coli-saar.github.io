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
  obj_p : Obj → Bool
  truck_p : Obj → Bool
  location_p : Obj → Bool
  airplane_p : Obj → Bool
  city_p : Obj → Bool
  airport_p : Obj → Bool
  in_city_p : Obj → Obj → Bool

structure DynamicStateGen (α : Type) where
  at_p : Obj → Obj → α
  in_p : Obj → Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidObjParam (s : StaticState) : Prop :=
  ∀ var_obj, s.obj_p var_obj = true → var_obj ∈ s.objects

def ValidTruckParam (s : StaticState) : Prop :=
  ∀ var_truck, s.truck_p var_truck = true → var_truck ∈ s.objects

def ValidLocationParam (s : StaticState) : Prop :=
  ∀ var_loc, s.location_p var_loc = true → var_loc ∈ s.objects

def ValidAirplaneParam (s : StaticState) : Prop :=
  ∀ var_airplane, s.airplane_p var_airplane = true → var_airplane ∈ s.objects

def ValidCityParam (s : StaticState) : Prop :=
  ∀ var_city, s.city_p var_city = true → var_city ∈ s.objects

def ValidAirportParam (s : StaticState) : Prop :=
  ∀ var_airport, s.airport_p var_airport = true → var_airport ∈ s.objects

def ValidInCityParam (s : StaticState) : Prop :=
  ∀ var_obj var_city, s.in_city_p var_obj var_city = true → s.location_p var_obj = true ∧ s.city_p var_city = true

def TypesPairwiseDisjoint (s : StaticState) : Prop :=
  (∀ x, s.obj_p x = true → s.truck_p x = false ∧ s.airplane_p x = false ∧
        s.location_p x = false ∧ s.city_p x = false) ∧
  (∀ x, s.truck_p x = true → s.obj_p x = false ∧ s.airplane_p x = false ∧
        s.location_p x = false ∧ s.city_p x = false) ∧
  (∀ x, s.airplane_p x = true → s.obj_p x = false ∧ s.truck_p x = false ∧
        s.location_p x = false ∧ s.city_p x = false) ∧
  (∀ x, s.location_p x = true → s.obj_p x = false ∧ s.truck_p x = false ∧
        s.airplane_p x = false ∧ s.city_p x = false) ∧
  (∀ x, s.city_p x = true → s.obj_p x = false ∧ s.truck_p x = false ∧
        s.airplane_p x = false ∧ s.location_p x = false) ∧
  (∀ x ∈ s.objects,
    s.obj_p x = true ∨ s.truck_p x = true ∨ s.airplane_p x = true ∨
    s.location_p x = true ∨ s.city_p x = true)

def AirportsAreLocs (s : StaticState) : Prop :=
  ∀ var_a, s.airport_p var_a = true → s.location_p var_a = true

def CityHasExactlyOneAirport (s : StaticState) : Prop :=
  ∀ c, s.city_p c = true →
    ∃! l, s.location_p l = true ∧ s.in_city_p l c = true ∧ s.airport_p l = true

def CityHasAtLeastOneLocation (s : StaticState) : Prop :=
  ∀ c, s.city_p c = true →
    ∃ l1, s.location_p l1 = true ∧ s.in_city_p l1 c = true

def EachLocInOneCity (s : StaticState) : Prop :=
  ∀ l, s.location_p l = true → ∃! c, s.in_city_p l c = true ∧ s.city_p c = true

def MinNumObj (s : StaticState) : Prop :=
  ∃ c, s.city_p c = true ∧
  ∃ o, s.obj_p o = true ∧
  ∃ p, s.airplane_p p = true

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidObjParam s ∧
  ValidTruckParam s ∧
  ValidLocationParam s ∧
  ValidAirplaneParam s ∧
  ValidCityParam s ∧
  ValidAirportParam s ∧
  ValidInCityParam s ∧
  TypesPairwiseDisjoint s ∧
  AirportsAreLocs s ∧
  CityHasExactlyOneAirport s ∧
  CityHasAtLeastOneLocation s ∧
  EachLocInOneCity s ∧
  MinNumObj s

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_obj var_loc, Truthy.isTrue (d.at_p var_obj var_loc) →
    var_obj ∈ s.objects ∧ var_loc ∈ s.objects ∧ s.location_p var_loc = true ∧
    (s.truck_p var_obj = true ∨ s.airplane_p var_obj = true ∨ s.obj_p var_obj = true)

def ValidInParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_obj1 var_obj2, Truthy.isTrue (d.in_p var_obj1 var_obj2) →
    var_obj1 ∈ s.objects ∧ var_obj2 ∈ s.objects ∧ s.obj_p var_obj1 = true ∧ (s.truck_p var_obj2 = true ∨ s.airplane_p var_obj2 = true)

def AirplanesOnlyAtAirports {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ p l, s.airplane_p p = true → Truthy.isTrue (d.at_p p l) → s.airport_p l = true

def VehicleUniqueLoc {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ v l1 l2, (s.truck_p v = true ∨ s.airplane_p v = true) →
    Truthy.isTrue (d.at_p v l1) → Truthy.isTrue (d.at_p v l2) → l1 = l2

def PackageAtXorIn {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o, s.obj_p o = true →
    ¬ ((∃ l, Truthy.isTrue (d.at_p o l)) ∧ (∃ v, Truthy.isTrue (d.in_p o v)))

def PackageUniqueAt {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o l1 l2, s.obj_p o = true →
    Truthy.isTrue (d.at_p o l1) → Truthy.isTrue (d.at_p o l2) → l1 = l2

def PackageUniqueIn {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ o v1 v2, s.obj_p o = true →
    Truthy.isTrue (d.in_p o v1) → Truthy.isTrue (d.in_p o v2) → v1 = v2

def AtLeastOneTruckPerCity (s : State) : Prop :=
  ∀ c, s.statics.city_p c = true →
    ∃ t l, s.statics.truck_p t = true ∧ s.statics.location_p l = true ∧
      s.statics.in_city_p l c = true ∧ s.dynamic.at_p t l = true

def VehicleHasLocation (s : State) : Prop :=
  ∀ v, (s.statics.truck_p v = true ∨ s.statics.airplane_p v = true) →
    ∃ l, s.statics.location_p l = true ∧ s.dynamic.at_p v l = true

def PackageHasLocationOrVehicle (s : State) : Prop :=
  ∀ o, s.statics.obj_p o = true →
    (∃ l, s.statics.location_p l = true ∧ s.dynamic.at_p o l = true) ∨
    (∃ v, (s.statics.truck_p v = true ∨ s.statics.airplane_p v = true) ∧ s.dynamic.in_p o v = true)

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidInParam s.statics s.dynamic ∧
  AirplanesOnlyAtAirports s.statics s.dynamic ∧
  VehicleUniqueLoc s.statics s.dynamic ∧
  PackageAtXorIn s.statics s.dynamic ∧
  PackageUniqueAt s.statics s.dynamic ∧
  PackageUniqueIn s.statics s.dynamic ∧
  AtLeastOneTruckPerCity s ∧
  VehicleHasLocation s ∧
  PackageHasLocationOrVehicle s

def InitialVehiclesEmpty (s : State) : Prop :=
  ∀ x v, s.dynamic.in_p x v = false

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitialVehiclesEmpty s

def GoalAtOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ o l, g.dynamic.at_p o l ≠ some false

def GoalPackageHasTargetLoc (initial : State) (g : Goal) : Prop :=
  ∀ o, initial.statics.obj_p o = true →
    ∃! l, initial.statics.location_p l = true ∧ g.dynamic.at_p o l = some true

def GoalIgnoreVehicleAt (initial : State) (g : Goal) : Prop :=
  ∀ v l, (initial.statics.truck_p v = true ∨ initial.statics.airplane_p v = true) →
    g.dynamic.at_p v l = none

def GoalIgnoreIn (initial : State) (g : Goal) : Prop :=
  ∀ o v, g.dynamic.in_p o v = none

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidInParam initial.statics g.dynamic ∧
  AirplanesOnlyAtAirports initial.statics g.dynamic ∧
  VehicleUniqueLoc initial.statics g.dynamic ∧
  PackageAtXorIn initial.statics g.dynamic ∧
  PackageUniqueAt initial.statics g.dynamic ∧
  PackageUniqueIn initial.statics g.dynamic ∧
  GoalAtOnlyPositive initial g ∧
  GoalPackageHasTargetLoc initial g ∧
  GoalIgnoreVehicleAt initial g ∧
  GoalIgnoreIn initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_obj var_loc,
    match g.dynamic.at_p var_obj var_loc with
    | none => True
    | some b => s.dynamic.at_p var_obj var_loc = b) ∧
  (∀ var_obj1 var_obj2,
    match g.dynamic.in_p var_obj1 var_obj2 with
    | none => True
    | some b => s.dynamic.in_p var_obj1 var_obj2 = b)

def load_truckPre (var_obj : Obj) (var_truck : Obj) (var_loc : Obj) (s : State) : Prop :=
  var_obj ∈ s.statics.objects ∧
  var_truck ∈ s.statics.objects ∧
  var_loc ∈ s.statics.objects ∧
  s.statics.obj_p var_obj = true ∧
  s.statics.truck_p var_truck = true ∧
  s.statics.location_p var_loc = true ∧
  s.dynamic.at_p var_truck var_loc = true ∧
  s.dynamic.at_p var_obj var_loc = true

def load_airplanePre (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj) (s : State) : Prop :=
  var_obj ∈ s.statics.objects ∧
  var_airplane ∈ s.statics.objects ∧
  var_loc ∈ s.statics.objects ∧
  s.statics.obj_p var_obj = true ∧
  s.statics.airplane_p var_airplane = true ∧
  s.statics.location_p var_loc = true ∧
  s.dynamic.at_p var_obj var_loc = true ∧
  s.dynamic.at_p var_airplane var_loc = true

def unload_truckPre (var_obj : Obj) (var_truck : Obj) (var_loc : Obj) (s : State) : Prop :=
  var_obj ∈ s.statics.objects ∧
  var_truck ∈ s.statics.objects ∧
  var_loc ∈ s.statics.objects ∧
  s.statics.obj_p var_obj = true ∧
  s.statics.truck_p var_truck = true ∧
  s.statics.location_p var_loc = true ∧
  s.dynamic.at_p var_truck var_loc = true ∧
  s.dynamic.in_p var_obj var_truck = true

def unload_airplanePre (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj) (s : State) : Prop :=
  var_obj ∈ s.statics.objects ∧
  var_airplane ∈ s.statics.objects ∧
  var_loc ∈ s.statics.objects ∧
  s.statics.obj_p var_obj = true ∧
  s.statics.airplane_p var_airplane = true ∧
  s.statics.location_p var_loc = true ∧
  s.dynamic.in_p var_obj var_airplane = true ∧
  s.dynamic.at_p var_airplane var_loc = true

def drive_truckPre (var_truck : Obj) (var_loc_from : Obj) (var_loc_to : Obj) (var_city : Obj) (s : State) : Prop :=
  var_truck ∈ s.statics.objects ∧
  var_loc_from ∈ s.statics.objects ∧
  var_loc_to ∈ s.statics.objects ∧
  var_city ∈ s.statics.objects ∧
  s.statics.truck_p var_truck = true ∧
  s.statics.location_p var_loc_from = true ∧
  s.statics.location_p var_loc_to = true ∧
  s.statics.city_p var_city = true ∧
  s.dynamic.at_p var_truck var_loc_from = true ∧
  s.statics.in_city_p var_loc_from var_city = true ∧
  s.statics.in_city_p var_loc_to var_city = true

def fly_airplanePre (var_airplane : Obj) (var_loc_from : Obj) (var_loc_to : Obj) (s : State) : Prop :=
  var_airplane ∈ s.statics.objects ∧
  var_loc_from ∈ s.statics.objects ∧
  var_loc_to ∈ s.statics.objects ∧
  s.statics.airplane_p var_airplane = true ∧
  s.statics.airport_p var_loc_from = true ∧
  s.statics.airport_p var_loc_to = true ∧
  s.dynamic.at_p var_airplane var_loc_from = true

def load_truck (var_obj : Obj) (var_truck : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_loc' =>
        if var_obj' = var_obj ∧ var_loc' = var_loc then
          false
        else
          s.dynamic.at_p var_obj' var_loc',
    in_p :=
      fun var_obj' var_truck' =>
        if var_obj' = var_obj ∧ var_truck' = var_truck then
          true
        else
          s.dynamic.in_p var_obj' var_truck'
  }
}

def load_airplane (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_loc' =>
        if var_obj' = var_obj ∧ var_loc' = var_loc then
          false
        else
          s.dynamic.at_p var_obj' var_loc',
    in_p :=
      fun var_obj' var_airplane' =>
        if var_obj' = var_obj ∧ var_airplane' = var_airplane then
          true
        else
          s.dynamic.in_p var_obj' var_airplane'
  }
}

def unload_truck (var_obj : Obj) (var_truck : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_loc' =>
        if var_obj' = var_obj ∧ var_loc' = var_loc then
          true
        else
          s.dynamic.at_p var_obj' var_loc',
    in_p :=
      fun var_obj' var_truck' =>
        if var_obj' = var_obj ∧ var_truck' = var_truck then
          false
        else
          s.dynamic.in_p var_obj' var_truck'
  }
}

def unload_airplane (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_obj' var_loc' =>
        if var_obj' = var_obj ∧ var_loc' = var_loc then
          true
        else
          s.dynamic.at_p var_obj' var_loc',
    in_p :=
      fun var_obj' var_airplane' =>
        if var_obj' = var_obj ∧ var_airplane' = var_airplane then
          false
        else
          s.dynamic.in_p var_obj' var_airplane'
  }
}

def drive_truck (var_truck : Obj) (var_loc_from : Obj) (var_loc_to : Obj) (var_city : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_truck' var_loc_to' =>
        if var_truck' = var_truck ∧ var_loc_to' = var_loc_to then
          true
        else if var_truck' = var_truck ∧ var_loc_to' = var_loc_from then
          false
        else
          s.dynamic.at_p var_truck' var_loc_to'
  }
}

def fly_airplane (var_airplane : Obj) (var_loc_from : Obj) (var_loc_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_airplane' var_loc_to' =>
        if var_airplane' = var_airplane ∧ var_loc_to' = var_loc_to then
          true
        else if var_airplane' = var_airplane ∧ var_loc_to' = var_loc_from then
          false
        else
          s.dynamic.at_p var_airplane' var_loc_to'
  }
}

inductive PlanAction where
  | load_truck      (var_obj : Obj) (var_truck : Obj) (var_loc : Obj)
  | load_airplane   (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj)
  | unload_truck    (var_obj : Obj) (var_truck : Obj) (var_loc : Obj)
  | unload_airplane (var_obj : Obj) (var_airplane : Obj) (var_loc : Obj)
  | drive_truck     (var_truck : Obj) (var_loc_from : Obj) (var_loc_to : Obj) (var_city : Obj)
  | fly_airplane    (var_airplane : Obj) (var_loc_from : Obj) (var_loc_to : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .load_truck      var_obj var_truck var_loc                 , s => load_truckPre var_obj var_truck var_loc s
  | .load_airplane   var_obj var_airplane var_loc              , s => load_airplanePre var_obj var_airplane var_loc s
  | .unload_truck    var_obj var_truck var_loc                 , s => unload_truckPre var_obj var_truck var_loc s
  | .unload_airplane var_obj var_airplane var_loc              , s => unload_airplanePre var_obj var_airplane var_loc s
  | .drive_truck     var_truck var_loc_from var_loc_to var_city, s => drive_truckPre var_truck var_loc_from var_loc_to var_city s
  | .fly_airplane    var_airplane var_loc_from var_loc_to      , s => fly_airplanePre var_airplane var_loc_from var_loc_to s

def actionApply : PlanAction → State → State
  | .load_truck      var_obj var_truck var_loc                 , s => load_truck var_obj var_truck var_loc s
  | .load_airplane   var_obj var_airplane var_loc              , s => load_airplane var_obj var_airplane var_loc s
  | .unload_truck    var_obj var_truck var_loc                 , s => unload_truck var_obj var_truck var_loc s
  | .unload_airplane var_obj var_airplane var_loc              , s => unload_airplane var_obj var_airplane var_loc s
  | .drive_truck     var_truck var_loc_from var_loc_to var_city, s => drive_truck var_truck var_loc_from var_loc_to var_city s
  | .fly_airplane    var_airplane var_loc_from var_loc_to      , s => fly_airplane var_airplane var_loc_from var_loc_to s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

-- Return the first object satisfying a Boolean predicate.
def gpFind (xs : List Obj) (p : Obj → Bool) : Option Obj :=
  match xs with
  | [] => none
  | x :: rest =>
      if p x = true then
        some x
      else
        gpFind rest p

def gpAny (xs : List Obj) (p : Obj → Bool) : Bool :=
  match xs with
  | [] => false
  | x :: rest =>
      if p x = true then
        true
      else
        gpAny rest p

-- This default is unreachable on well-formed instances.
def gpChoose (xs : List Obj) (p : Obj → Bool) : Obj :=
  (gpFind xs p).getD 0

def gpGoalAt (g : Goal) (o l : Obj) : Bool :=
  match g.dynamic.at_p o l with
  | some true => true
  | _ => false

def gpGoalTarget (s : State) (g : Goal) (o : Obj) : Obj :=
  gpChoose s.statics.objects (fun l =>
    s.statics.location_p l &&
    gpGoalAt g o l)

def gpCityOfLocation (s : State) (l : Obj) : Obj :=
  gpChoose s.statics.objects (fun c =>
    s.statics.city_p c &&
    s.statics.in_city_p l c)

def gpAirportInCity (s : State) (c : Obj) : Obj :=
  gpChoose s.statics.objects (fun l =>
    s.statics.location_p l &&
    s.statics.airport_p l &&
    s.statics.in_city_p l c)

def gpVehicleLocation (s : State) (v : Obj) : Obj :=
  gpChoose s.statics.objects (fun l =>
    s.statics.location_p l &&
    s.dynamic.at_p v l)

def gpTruckHasLocationInCity (s : State) (t c : Obj) : Bool :=
  s.statics.truck_p t &&
  gpAny s.statics.objects (fun l =>
    s.statics.location_p l &&
    s.statics.in_city_p l c &&
    s.dynamic.at_p t l)

def gpTruckInCity (s : State) (c : Obj) : Obj :=
  gpChoose s.statics.objects (fun t =>
    gpTruckHasLocationInCity s t c)

def gpAirplane (s : State) : Obj :=
  gpChoose s.statics.objects (fun p =>
    s.statics.airplane_p p)

def gpCarrierOf (s : State) (o : Obj) : Obj :=
  gpChoose s.statics.objects (fun v =>
    (s.statics.truck_p v || s.statics.airplane_p v) &&
    s.dynamic.in_p o v)

structure GPLocatedPackage where
  actions : List PlanAction
  state   : State
  loc     : Obj

-- If a package initially lies inside a vehicle, first unload it at the
-- vehicle's current location.
def gpLocatePackage (o : Obj) (s : State) : GPLocatedPackage :=
  match gpFind s.statics.objects (fun l =>
    s.statics.location_p l &&
    s.dynamic.at_p o l) with
  | some l =>
      {
        actions := []
        state := s
        loc := l
      }
  | none =>
      let v := gpCarrierOf s o
      let l := gpVehicleLocation s v
      let a : PlanAction :=
        if s.statics.truck_p v = true then
          PlanAction.unload_truck o v l
        else
          PlanAction.unload_airplane o v l
      let actions := [a]
      {
        actions := actions
        state := runPlan actions s
        loc := l
      }

-- Move a package between two locations in one city.
def gpTruckTransfer
    (o src dst city : Obj) (s : State) : List PlanAction × State :=
  if src = dst then
    ([], s)
  else
    let truck := gpTruckInCity s city
    let truckLoc := gpVehicleLocation s truck
    let position : List PlanAction :=
      if truckLoc = src then
        []
      else
        [PlanAction.drive_truck truck truckLoc src city]
    let actions :=
      position ++
        [PlanAction.load_truck o truck src,
         PlanAction.drive_truck truck src dst city,
         PlanAction.unload_truck o truck dst]
    (actions, runPlan actions s)

-- Move a package between two airports.
def gpAirTransfer
    (o srcAirport dstAirport : Obj) (s : State) :
    List PlanAction × State :=
  if srcAirport = dstAirport then
    ([], s)
  else
    let airplane := gpAirplane s
    let airplaneLoc := gpVehicleLocation s airplane
    let position : List PlanAction :=
      if airplaneLoc = srcAirport then
        []
      else
        [PlanAction.fly_airplane airplane airplaneLoc srcAirport]
    let actions :=
      position ++
        [PlanAction.load_airplane o airplane srcAirport,
         PlanAction.fly_airplane airplane srcAirport dstAirport,
         PlanAction.unload_airplane o airplane dstAirport]
    (actions, runPlan actions s)

def gpDeliverPackage
    (o : Obj) (s : State) (g : Goal) : List PlanAction × State :=
  let prepared := gpLocatePackage o s
  let src := prepared.loc
  let dst := gpGoalTarget prepared.state g o

  if src = dst then
    (prepared.actions, prepared.state)
  else
    let srcCity := gpCityOfLocation prepared.state src
    let dstCity := gpCityOfLocation prepared.state dst

    if srcCity = dstCity then
      let result := gpTruckTransfer o src dst srcCity prepared.state
      (prepared.actions ++ result.1, result.2)
    else
      let srcAirport := gpAirportInCity prepared.state srcCity
      let dstAirport := gpAirportInCity prepared.state dstCity

      let originResult : List PlanAction × State :=
        if src = srcAirport then
          ([], prepared.state)
        else
          gpTruckTransfer o src srcAirport srcCity prepared.state

      let airResult :=
        gpAirTransfer o srcAirport dstAirport originResult.2

      let destinationResult : List PlanAction × State :=
        if dst = dstAirport then
          ([], airResult.2)
        else
          gpTruckTransfer o dstAirport dst dstCity airResult.2

      (prepared.actions ++
         originResult.1 ++
         airResult.1 ++
         destinationResult.1,
       destinationResult.2)

def gpSolveObjects :
    List Obj → State → Goal → List PlanAction
  | [], _, _ => []
  | o :: rest, s, g =>
      if s.statics.obj_p o = true then
        let result := gpDeliverPackage o s g
        result.1 ++ gpSolveObjects rest result.2 g
      else
        gpSolveObjects rest s g

-- The main solve function
def solve (s : State) (g : Goal) : List PlanAction :=
  gpSolveObjects s.statics.objects s g

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

lemma load_truck_statics (var_obj var_truck var_loc : Obj) (s : State) :
    (load_truck var_obj var_truck var_loc s).statics = s.statics := rfl

lemma load_airplane_statics (var_obj var_airplane var_loc : Obj) (s : State) :
    (load_airplane var_obj var_airplane var_loc s).statics = s.statics := rfl

lemma unload_truck_statics (var_obj var_truck var_loc : Obj) (s : State) :
    (unload_truck var_obj var_truck var_loc s).statics = s.statics := rfl

lemma unload_airplane_statics (var_obj var_airplane var_loc : Obj) (s : State) :
    (unload_airplane var_obj var_airplane var_loc s).statics = s.statics := rfl

lemma drive_truck_statics (var_truck var_loc_from var_loc_to var_city : Obj) (s : State) :
    (drive_truck var_truck var_loc_from var_loc_to var_city s).statics = s.statics := rfl

lemma fly_airplane_statics (var_airplane var_loc_from var_loc_to : Obj) (s : State) :
    (fly_airplane var_airplane var_loc_from var_loc_to s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | load_truck var_obj var_truck var_loc                   => exact load_truck_statics var_obj var_truck var_loc s
      | load_airplane var_obj var_airplane var_loc             => exact load_airplane_statics var_obj var_airplane var_loc s
      | unload_truck var_obj var_truck var_loc                 => exact unload_truck_statics var_obj var_truck var_loc s
      | unload_airplane var_obj var_airplane var_loc           => exact unload_airplane_statics var_obj var_airplane var_loc s
      | drive_truck var_truck var_loc_from var_loc_to var_city => exact drive_truck_statics var_truck var_loc_from var_loc_to var_city s
      | fly_airplane var_airplane var_loc_from var_loc_to      => exact fly_airplane_statics var_airplane var_loc_from var_loc_to s

-- load_truck only touches in_p, at_p
lemma load_truck_at_p_ne (var_obj var_truck var_loc : Obj) (s : State) {var_obj' var_loc' : Obj} (h1 : var_obj' ≠ var_obj) :
    (load_truck var_obj var_truck var_loc s).dynamic.at_p var_obj' var_loc' = s.dynamic.at_p var_obj' var_loc' := by
  unfold load_truck
  simp [h1]

lemma load_truck_at_p_ne_var_loc (var_obj var_truck var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (load_truck var_obj var_truck var_loc s).dynamic.at_p var_obj var_loc' = s.dynamic.at_p var_obj var_loc' := by
  unfold load_truck
  simp [h1]

lemma load_truck_in_p_ne (var_obj var_truck var_loc : Obj) (s : State) {var_obj' var_truck' : Obj} (h1 : var_obj' ≠ var_obj) :
    (load_truck var_obj var_truck var_loc s).dynamic.in_p var_obj' var_truck' = s.dynamic.in_p var_obj' var_truck' := by
  unfold load_truck
  simp [h1]

lemma load_truck_in_p_ne_var_obj2 (var_obj var_truck var_loc : Obj) (s : State) {var_truck' : Obj} (h1 : var_truck' ≠ var_truck) :
    (load_truck var_obj var_truck var_loc s).dynamic.in_p var_obj var_truck' = s.dynamic.in_p var_obj var_truck' := by
  unfold load_truck
  simp [h1]

-- load_airplane only touches in_p, at_p
lemma load_airplane_at_p_ne (var_obj var_airplane var_loc : Obj) (s : State) {var_obj' var_loc' : Obj} (h1 : var_obj' ≠ var_obj) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj' var_loc' = s.dynamic.at_p var_obj' var_loc' := by
  unfold load_airplane
  simp [h1]

lemma load_airplane_at_p_ne_var_loc (var_obj var_airplane var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj var_loc' = s.dynamic.at_p var_obj var_loc' := by
  unfold load_airplane
  simp [h1]

lemma load_airplane_in_p_ne (var_obj var_airplane var_loc : Obj) (s : State) {var_obj' var_airplane' : Obj} (h1 : var_obj' ≠ var_obj) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj' var_airplane' = s.dynamic.in_p var_obj' var_airplane' := by
  unfold load_airplane
  simp [h1]

lemma load_airplane_in_p_ne_var_obj2 (var_obj var_airplane var_loc : Obj) (s : State) {var_airplane' : Obj} (h1 : var_airplane' ≠ var_airplane) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj var_airplane' = s.dynamic.in_p var_obj var_airplane' := by
  unfold load_airplane
  simp [h1]

-- unload_truck only touches at_p, in_p
lemma unload_truck_at_p_ne (var_obj var_truck var_loc : Obj) (s : State) {var_obj' var_loc' : Obj} (h1 : var_obj' ≠ var_obj) :
    (unload_truck var_obj var_truck var_loc s).dynamic.at_p var_obj' var_loc' = s.dynamic.at_p var_obj' var_loc' := by
  unfold unload_truck
  simp [h1]

lemma unload_truck_at_p_ne_var_loc (var_obj var_truck var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (unload_truck var_obj var_truck var_loc s).dynamic.at_p var_obj var_loc' = s.dynamic.at_p var_obj var_loc' := by
  unfold unload_truck
  simp [h1]

lemma unload_truck_in_p_ne (var_obj var_truck var_loc : Obj) (s : State) {var_obj' var_truck' : Obj} (h1 : var_obj' ≠ var_obj) :
    (unload_truck var_obj var_truck var_loc s).dynamic.in_p var_obj' var_truck' = s.dynamic.in_p var_obj' var_truck' := by
  unfold unload_truck
  simp [h1]

lemma unload_truck_in_p_ne_var_obj2 (var_obj var_truck var_loc : Obj) (s : State) {var_truck' : Obj} (h1 : var_truck' ≠ var_truck) :
    (unload_truck var_obj var_truck var_loc s).dynamic.in_p var_obj var_truck' = s.dynamic.in_p var_obj var_truck' := by
  unfold unload_truck
  simp [h1]

-- unload_airplane only touches at_p, in_p
lemma unload_airplane_at_p_ne (var_obj var_airplane var_loc : Obj) (s : State) {var_obj' var_loc' : Obj} (h1 : var_obj' ≠ var_obj) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj' var_loc' = s.dynamic.at_p var_obj' var_loc' := by
  unfold unload_airplane
  simp [h1]

lemma unload_airplane_at_p_ne_var_loc (var_obj var_airplane var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj var_loc' = s.dynamic.at_p var_obj var_loc' := by
  unfold unload_airplane
  simp [h1]

lemma unload_airplane_in_p_ne (var_obj var_airplane var_loc : Obj) (s : State) {var_obj' var_airplane' : Obj} (h1 : var_obj' ≠ var_obj) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj' var_airplane' = s.dynamic.in_p var_obj' var_airplane' := by
  unfold unload_airplane
  simp [h1]

lemma unload_airplane_in_p_ne_var_obj2 (var_obj var_airplane var_loc : Obj) (s : State) {var_airplane' : Obj} (h1 : var_airplane' ≠ var_airplane) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj var_airplane' = s.dynamic.in_p var_obj var_airplane' := by
  unfold unload_airplane
  simp [h1]

-- drive_truck only touches at_p
lemma drive_truck_at_p_ne_var_loc (var_truck var_loc_from var_loc_to var_city : Obj) (s : State) {var_loc_to' : Obj} (h1 : var_loc_to' ≠ var_loc_to) (h2 : var_loc_to' ≠ var_loc_from) :
    (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p var_truck var_loc_to' = s.dynamic.at_p var_truck var_loc_to' := by
  unfold drive_truck
  simp [h1, h2]

-- drive_truck never touches in_p
lemma drive_truck_in_p (var_truck var_loc_from var_loc_to var_city : Obj) (s : State) :
    (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.in_p = s.dynamic.in_p := rfl

-- fly_airplane only touches at_p
lemma fly_airplane_at_p_ne_var_loc (var_airplane var_loc_from var_loc_to : Obj) (s : State) {var_loc_to' : Obj} (h1 : var_loc_to' ≠ var_loc_to) (h2 : var_loc_to' ≠ var_loc_from) :
    (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p var_airplane var_loc_to' = s.dynamic.at_p var_airplane var_loc_to' := by
  unfold fly_airplane
  simp [h1, h2]

-- fly_airplane never touches in_p
lemma fly_airplane_in_p (var_airplane var_loc_from var_loc_to : Obj) (s : State) :
    (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.in_p = s.dynamic.in_p := rfl

lemma load_truck_at_p_eq1 (var_obj var_truck var_loc : Obj) (s : State) :
    (load_truck var_obj var_truck var_loc s).dynamic.at_p var_obj var_loc = false := by
  unfold load_truck
  simp

lemma load_truck_in_p_eq1 (var_obj var_truck var_loc : Obj) (s : State) :
    (load_truck var_obj var_truck var_loc s).dynamic.in_p var_obj var_truck = true := by
  unfold load_truck
  simp

lemma load_airplane_at_p_eq1 (var_obj var_airplane var_loc : Obj) (s : State) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj var_loc = false := by
  unfold load_airplane
  simp

lemma load_airplane_in_p_eq1 (var_obj var_airplane var_loc : Obj) (s : State) :
    (load_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj var_airplane = true := by
  unfold load_airplane
  simp

lemma unload_truck_at_p_eq1 (var_obj var_truck var_loc : Obj) (s : State) :
    (unload_truck var_obj var_truck var_loc s).dynamic.at_p var_obj var_loc = true := by
  unfold unload_truck
  simp

lemma unload_truck_in_p_eq1 (var_obj var_truck var_loc : Obj) (s : State) :
    (unload_truck var_obj var_truck var_loc s).dynamic.in_p var_obj var_truck = false := by
  unfold unload_truck
  simp

lemma unload_airplane_at_p_eq1 (var_obj var_airplane var_loc : Obj) (s : State) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj var_loc = true := by
  unfold unload_airplane
  simp

lemma unload_airplane_in_p_eq1 (var_obj var_airplane var_loc : Obj) (s : State) :
    (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p var_obj var_airplane = false := by
  unfold unload_airplane
  simp

lemma drive_truck_at_p_eq1 (var_truck var_loc_from var_loc_to var_city : Obj) (s : State) :
    (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p var_truck var_loc_to = true := by
  unfold drive_truck
  simp

lemma drive_truck_at_p_eq2 (var_truck var_loc_from var_loc_to var_city : Obj) (s : State) (h1 : var_loc_from ≠ var_loc_to) :
    (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p var_truck var_loc_from = false := by
  unfold drive_truck
  simp [h1]

lemma fly_airplane_at_p_eq1 (var_airplane var_loc_from var_loc_to : Obj) (s : State) :
    (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p var_airplane var_loc_to = true := by
  unfold fly_airplane
  simp

lemma fly_airplane_at_p_eq2 (var_airplane var_loc_from var_loc_to : Obj) (s : State) (h1 : var_loc_from ≠ var_loc_to) :
    (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p var_airplane var_loc_from = false := by
  unfold fly_airplane
  simp [h1]

@[simp] lemma truthy_bool_eq_true (b : Bool) :
    Truthy.isTrue b ↔ b = true := by
  rfl

lemma wfStatic_disjoint (s : StaticState) (h : WellFormedStatic s) :
    TypesPairwiseDisjoint s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hdis, _, _, _, _, _⟩
  exact hdis

lemma wfStatic_airportsAreLocs (s : StaticState) (h : WellFormedStatic s) :
    AirportsAreLocs s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hAirports, _, _, _, _⟩
  exact hAirports

lemma wfStatic_eachLocInOneCity (s : StaticState) (h : WellFormedStatic s) :
    EachLocInOneCity s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hEach, _⟩
  exact hEach

lemma obj_ne_truck_of_disjoint
    {s : StaticState} {o t : Obj}
    (hdis : TypesPairwiseDisjoint s)
    (ho : s.obj_p o = true)
    (ht : s.truck_p t = true) :
    o ≠ t := by
  intro h
  subst t
  have hf : s.truck_p o = false := (hdis.1 o ho).1
  simp_all

lemma obj_ne_airplane_of_disjoint
    {s : StaticState} {o p : Obj}
    (hdis : TypesPairwiseDisjoint s)
    (ho : s.obj_p o = true)
    (hp : s.airplane_p p = true) :
    o ≠ p := by
  intro h
  subst p
  have hf : s.airplane_p o = false := (hdis.1 o ho).2.1
  simp_all

lemma truck_ne_airplane_of_disjoint
    {s : StaticState} {t p : Obj}
    (hdis : TypesPairwiseDisjoint s)
    (ht : s.truck_p t = true)
    (hp : s.airplane_p p = true) :
    t ≠ p := by
  intro h
  subst p
  have hf : s.airplane_p t = false := (hdis.2.1 t ht).2.1
  simp_all

lemma load_truck_preserves_wf
    (var_obj var_truck var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : load_truckPre var_obj var_truck var_loc s) :
    WellFormed (load_truck var_obj var_truck var_loc s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hObjMem, hTruckMem, hLocMem, hObjType, hTruckType,
      hLocType, hTruckAt, hObjAt⟩
  have hdis := wfStatic_disjoint s.statics hstatic

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change (load_truck var_obj var_truck var_loc s).dynamic.at_p o l = true at hat
    by_cases ho : o = var_obj
    · subst o
      by_cases hl : l = var_loc
      · subst l
        simp [load_truck] at hat
      · apply hAt var_obj l
        simpa [load_truck, hl] using hat
    · apply hAt o l
      simpa [load_truck, ho] using hat

  · intro o v hin
    change (load_truck var_obj var_truck var_loc s).dynamic.in_p o v = true at hin
    by_cases ho : o = var_obj
    · subst o
      by_cases hv : v = var_truck
      · subst v
        exact ⟨hObjMem, hTruckMem, hObjType, Or.inl hTruckType⟩
      · apply hIn var_obj v
        simpa [load_truck, hv] using hin
    · apply hIn o v
      simpa [load_truck, ho] using hin

  · intro p l hp hat
    have hne : p ≠ var_obj :=
      (obj_ne_airplane_of_disjoint hdis hObjType hp).symm
    apply hAir p l hp
    change (load_truck var_obj var_truck var_loc s).dynamic.at_p p l = true at hat
    simpa [load_truck, hne] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    apply hVehicleUnique v l₁ l₂ hv
    · change
        (load_truck var_obj var_truck var_loc s).dynamic.at_p v l₁ = true at hat₁
      simpa [load_truck, hne] using hat₁
    · change
        (load_truck var_obj var_truck var_loc s).dynamic.at_p v l₂ = true at hat₂
      simpa [load_truck, hne] using hat₂

  · intro o ho hboth
    by_cases hEq : o = var_obj
    · subst o
      rcases hboth.1 with ⟨l, hat⟩
      change
        (load_truck var_obj var_truck var_loc s).dynamic.at_p var_obj l = true at hat
      by_cases hl : l = var_loc
      · subst l
        simp [load_truck] at hat
      · have hOldAt : s.dynamic.at_p var_obj l = true := by
          simpa [load_truck, hl] using hat
        have hLocEq :=
          hUniqueAt var_obj l var_loc hObjType hOldAt hObjAt
        exact hl hLocEq
    · apply hXor o ho
      constructor
      · rcases hboth.1 with ⟨l, hat⟩
        refine ⟨l, ?_⟩
        change
          (load_truck var_obj var_truck var_loc s).dynamic.at_p o l = true at hat
        simpa [load_truck, hEq] using hat
      · rcases hboth.2 with ⟨v, hin⟩
        refine ⟨v, ?_⟩
        change
          (load_truck var_obj var_truck var_loc s).dynamic.in_p o v = true at hin
        simpa [load_truck, hEq] using hin

  · intro o l₁ l₂ ho hat₁ hat₂
    by_cases hEq : o = var_obj
    · subst o
      have oldOfNew :
          ∀ l,
            (load_truck var_obj var_truck var_loc s).dynamic.at_p var_obj l = true →
            s.dynamic.at_p var_obj l = true := by
        intro l hat
        by_cases hl : l = var_loc
        · subst l
          simp [load_truck] at hat
        · simpa [load_truck, hl] using hat
      apply hUniqueAt var_obj l₁ l₂ hObjType
      · change s.dynamic.at_p var_obj l₁ = true
        exact oldOfNew l₁ hat₁
      · change s.dynamic.at_p var_obj l₂ = true
        exact oldOfNew l₂ hat₂
    · apply hUniqueAt o l₁ l₂ ho
      · change
          (load_truck var_obj var_truck var_loc s).dynamic.at_p o l₁ = true at hat₁
        simpa [load_truck, hEq] using hat₁
      · change
          (load_truck var_obj var_truck var_loc s).dynamic.at_p o l₂ = true at hat₂
        simpa [load_truck, hEq] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    by_cases hEq : o = var_obj
    · subst o
      have forceCarrier :
          ∀ v,
            (load_truck var_obj var_truck var_loc s).dynamic.in_p var_obj v = true →
            v = var_truck := by
        intro v hin
        by_contra hv
        have hOldIn : s.dynamic.in_p var_obj v = true := by
          simpa [load_truck, hv] using hin
        exact (hXor var_obj hObjType)
          ⟨⟨var_loc, hObjAt⟩, ⟨v, hOldIn⟩⟩
      exact (forceCarrier v₁ hin₁).trans (forceCarrier v₂ hin₂).symm
    · apply hUniqueIn o v₁ v₂ ho
      · change
          (load_truck var_obj var_truck var_loc s).dynamic.in_p o v₁ = true at hin₁
        simpa [load_truck, hEq] using hin₁
      · change
          (load_truck var_obj var_truck var_loc s).dynamic.in_p o v₂ = true at hin₂
        simpa [load_truck, hEq] using hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    refine ⟨t, l, ht, hl, hil, ?_⟩
    have hne : t ≠ var_obj :=
      (obj_ne_truck_of_disjoint hdis hObjType ht).symm
    simpa [load_truck, hne] using hat

  · intro v hv
    rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
    refine ⟨l, hl, ?_⟩
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    simpa [load_truck, hne] using hat

  · intro o ho
    by_cases hEq : o = var_obj
    · subst o
      exact Or.inr
        ⟨var_truck, Or.inl hTruckType,
          load_truck_in_p_eq1 var_obj var_truck var_loc s⟩
    · rcases hPackageLoc o ho with hAtLoc | hInVehicle
      · left
        rcases hAtLoc with ⟨l, hl, hat⟩
        refine ⟨l, hl, ?_⟩
        simpa [load_truck, hEq] using hat
      · right
        rcases hInVehicle with ⟨v, hv, hin⟩
        refine ⟨v, hv, ?_⟩
        simpa [load_truck, hEq] using hin

lemma load_airplane_preserves_wf
    (var_obj var_airplane var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : load_airplanePre var_obj var_airplane var_loc s) :
    WellFormed (load_airplane var_obj var_airplane var_loc s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hObjMem, hAirplaneMem, hLocMem, hObjType, hAirplaneType,
      hLocType, hObjAt, hAirplaneAt⟩
  have hdis := wfStatic_disjoint s.statics hstatic

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change
      (load_airplane var_obj var_airplane var_loc s).dynamic.at_p o l = true at hat
    by_cases ho : o = var_obj
    · subst o
      by_cases hl : l = var_loc
      · subst l
        simp [load_airplane] at hat
      · apply hAt var_obj l
        simpa [load_airplane, hl] using hat
    · apply hAt o l
      simpa [load_airplane, ho] using hat

  · intro o v hin
    change
      (load_airplane var_obj var_airplane var_loc s).dynamic.in_p o v = true at hin
    by_cases ho : o = var_obj
    · subst o
      by_cases hv : v = var_airplane
      · subst v
        exact ⟨hObjMem, hAirplaneMem, hObjType, Or.inr hAirplaneType⟩
      · apply hIn var_obj v
        simpa [load_airplane, hv] using hin
    · apply hIn o v
      simpa [load_airplane, ho] using hin

  · intro p l hp hat
    have hne : p ≠ var_obj :=
      (obj_ne_airplane_of_disjoint hdis hObjType hp).symm
    apply hAir p l hp
    change
      (load_airplane var_obj var_airplane var_loc s).dynamic.at_p p l = true at hat
    simpa [load_airplane, hne] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    apply hVehicleUnique v l₁ l₂ hv
    · change
        (load_airplane var_obj var_airplane var_loc s).dynamic.at_p v l₁ = true
          at hat₁
      simpa [load_airplane, hne] using hat₁
    · change
        (load_airplane var_obj var_airplane var_loc s).dynamic.at_p v l₂ = true
          at hat₂
      simpa [load_airplane, hne] using hat₂

  · intro o ho hboth
    by_cases hEq : o = var_obj
    · subst o
      rcases hboth.1 with ⟨l, hat⟩
      change
        (load_airplane var_obj var_airplane var_loc s).dynamic.at_p var_obj l =
          true at hat
      by_cases hl : l = var_loc
      · subst l
        simp [load_airplane] at hat
      · have hOldAt : s.dynamic.at_p var_obj l = true := by
          simpa [load_airplane, hl] using hat
        have hLocEq :=
          hUniqueAt var_obj l var_loc hObjType hOldAt hObjAt
        exact hl hLocEq
    · apply hXor o ho
      constructor
      · rcases hboth.1 with ⟨l, hat⟩
        refine ⟨l, ?_⟩
        change
          (load_airplane var_obj var_airplane var_loc s).dynamic.at_p o l = true
            at hat
        simpa [load_airplane, hEq] using hat
      · rcases hboth.2 with ⟨v, hin⟩
        refine ⟨v, ?_⟩
        change
          (load_airplane var_obj var_airplane var_loc s).dynamic.in_p o v = true
            at hin
        simpa [load_airplane, hEq] using hin

  · intro o l₁ l₂ ho hat₁ hat₂
    by_cases hEq : o = var_obj
    · subst o
      have oldOfNew :
          ∀ l,
            (load_airplane var_obj var_airplane var_loc s).dynamic.at_p
                var_obj l = true →
            s.dynamic.at_p var_obj l = true := by
        intro l hat
        by_cases hl : l = var_loc
        · subst l
          simp [load_airplane] at hat
        · simpa [load_airplane, hl] using hat
      apply hUniqueAt var_obj l₁ l₂ hObjType
      · change s.dynamic.at_p var_obj l₁ = true
        exact oldOfNew l₁ hat₁
      · change s.dynamic.at_p var_obj l₂ = true
        exact oldOfNew l₂ hat₂
    · apply hUniqueAt o l₁ l₂ ho
      · change
          (load_airplane var_obj var_airplane var_loc s).dynamic.at_p o l₁ = true
            at hat₁
        simpa [load_airplane, hEq] using hat₁
      · change
          (load_airplane var_obj var_airplane var_loc s).dynamic.at_p o l₂ = true
            at hat₂
        simpa [load_airplane, hEq] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    by_cases hEq : o = var_obj
    · subst o
      have forceCarrier :
          ∀ v,
            (load_airplane var_obj var_airplane var_loc s).dynamic.in_p
                var_obj v = true →
            v = var_airplane := by
        intro v hin
        by_contra hv
        have hOldIn : s.dynamic.in_p var_obj v = true := by
          simpa [load_airplane, hv] using hin
        exact (hXor var_obj hObjType)
          ⟨⟨var_loc, hObjAt⟩, ⟨v, hOldIn⟩⟩
      exact (forceCarrier v₁ hin₁).trans (forceCarrier v₂ hin₂).symm
    · apply hUniqueIn o v₁ v₂ ho
      · change
          (load_airplane var_obj var_airplane var_loc s).dynamic.in_p o v₁ = true
            at hin₁
        simpa [load_airplane, hEq] using hin₁
      · change
          (load_airplane var_obj var_airplane var_loc s).dynamic.in_p o v₂ = true
            at hin₂
        simpa [load_airplane, hEq] using hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    refine ⟨t, l, ht, hl, hil, ?_⟩
    have hne : t ≠ var_obj :=
      (obj_ne_truck_of_disjoint hdis hObjType ht).symm
    simpa [load_airplane, hne] using hat

  · intro v hv
    rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
    refine ⟨l, hl, ?_⟩
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    simpa [load_airplane, hne] using hat

  · intro o ho
    by_cases hEq : o = var_obj
    · subst o
      exact Or.inr
        ⟨var_airplane, Or.inr hAirplaneType,
          load_airplane_in_p_eq1 var_obj var_airplane var_loc s⟩
    · rcases hPackageLoc o ho with hAtLoc | hInVehicle
      · left
        rcases hAtLoc with ⟨l, hl, hat⟩
        refine ⟨l, hl, ?_⟩
        simpa [load_airplane, hEq] using hat
      · right
        rcases hInVehicle with ⟨v, hv, hin⟩
        refine ⟨v, hv, ?_⟩
        simpa [load_airplane, hEq] using hin

lemma unload_truck_preserves_wf
    (var_obj var_truck var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : unload_truckPre var_obj var_truck var_loc s) :
    WellFormed (unload_truck var_obj var_truck var_loc s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hObjMem, hTruckMem, hLocMem, hObjType, hTruckType,
      hLocType, hTruckAt, hObjIn⟩
  have hdis := wfStatic_disjoint s.statics hstatic

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change
      (unload_truck var_obj var_truck var_loc s).dynamic.at_p o l = true at hat
    by_cases ho : o = var_obj
    · subst o
      by_cases hl : l = var_loc
      · subst l
        exact ⟨hObjMem, hLocMem, hLocType, Or.inr (Or.inr hObjType)⟩
      · apply hAt var_obj l
        simpa [unload_truck, hl] using hat
    · apply hAt o l
      simpa [unload_truck, ho] using hat

  · intro o v hin
    apply hIn o v
    change s.dynamic.in_p o v = true
    change
      (unload_truck var_obj var_truck var_loc s).dynamic.in_p o v = true at hin
    by_cases ho : o = var_obj
    · subst o
      by_cases hv : v = var_truck
      · subst v
        simp [unload_truck] at hin
      · simpa [unload_truck, hv] using hin
    · simpa [unload_truck, ho] using hin

  · intro p l hp hat
    apply hAir p l hp
    have hne : p ≠ var_obj :=
      (obj_ne_airplane_of_disjoint hdis hObjType hp).symm
    change
      (unload_truck var_obj var_truck var_loc s).dynamic.at_p p l = true at hat
    simpa [unload_truck, hne] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    apply hVehicleUnique v l₁ l₂ hv
    · change
        (unload_truck var_obj var_truck var_loc s).dynamic.at_p v l₁ = true at hat₁
      simpa [unload_truck, hne] using hat₁
    · change
        (unload_truck var_obj var_truck var_loc s).dynamic.at_p v l₂ = true at hat₂
      simpa [unload_truck, hne] using hat₂

  · intro o ho hboth
    by_cases hEq : o = var_obj
    · subst o
      rcases hboth.2 with ⟨v, hin⟩
      change
        (unload_truck var_obj var_truck var_loc s).dynamic.in_p var_obj v = true
          at hin
      by_cases hv : v = var_truck
      · subst v
        simp [unload_truck] at hin
      · have hOldIn : s.dynamic.in_p var_obj v = true := by
          simpa [unload_truck, hv] using hin
        have hCarrierEq :=
          hUniqueIn var_obj v var_truck hObjType hOldIn hObjIn
        exact hv hCarrierEq
    · apply hXor o ho
      constructor
      · rcases hboth.1 with ⟨l, hat⟩
        refine ⟨l, ?_⟩
        change
          (unload_truck var_obj var_truck var_loc s).dynamic.at_p o l = true at hat
        simpa [unload_truck, hEq] using hat
      · rcases hboth.2 with ⟨v, hin⟩
        refine ⟨v, ?_⟩
        change
          (unload_truck var_obj var_truck var_loc s).dynamic.in_p o v = true at hin
        simpa [unload_truck, hEq] using hin

  · intro o l₁ l₂ ho hat₁ hat₂
    by_cases hEq : o = var_obj
    · subst o
      have forceLoc :
          ∀ l,
            (unload_truck var_obj var_truck var_loc s).dynamic.at_p
                var_obj l = true →
            l = var_loc := by
        intro l hat
        by_contra hl
        have hOldAt : s.dynamic.at_p var_obj l = true := by
          simpa [unload_truck, hl] using hat
        exact (hXor var_obj hObjType)
          ⟨⟨l, hOldAt⟩, ⟨var_truck, hObjIn⟩⟩
      exact (forceLoc l₁ hat₁).trans (forceLoc l₂ hat₂).symm
    · apply hUniqueAt o l₁ l₂ ho
      · change
          (unload_truck var_obj var_truck var_loc s).dynamic.at_p o l₁ = true
            at hat₁
        simpa [unload_truck, hEq] using hat₁
      · change
          (unload_truck var_obj var_truck var_loc s).dynamic.at_p o l₂ = true
            at hat₂
        simpa [unload_truck, hEq] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    have oldOfNew :
        ∀ x v,
          (unload_truck var_obj var_truck var_loc s).dynamic.in_p x v = true →
          s.dynamic.in_p x v = true := by
      intro x v hin
      by_cases hx : x = var_obj
      · subst x
        by_cases hv : v = var_truck
        · subst v
          simp [unload_truck] at hin
        · simpa [unload_truck, hv] using hin
      · simpa [unload_truck, hx] using hin
    apply hUniqueIn o v₁ v₂ ho
    · change s.dynamic.in_p o v₁ = true
      exact oldOfNew o v₁ hin₁
    · change s.dynamic.in_p o v₂ = true
      exact oldOfNew o v₂ hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    refine ⟨t, l, ht, hl, hil, ?_⟩
    have hne : t ≠ var_obj :=
      (obj_ne_truck_of_disjoint hdis hObjType ht).symm
    simpa [unload_truck, hne] using hat

  · intro v hv
    rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
    refine ⟨l, hl, ?_⟩
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    simpa [unload_truck, hne] using hat

  · intro o ho
    by_cases hEq : o = var_obj
    · subst o
      exact Or.inl
        ⟨var_loc, hLocType,
          unload_truck_at_p_eq1 var_obj var_truck var_loc s⟩
    · rcases hPackageLoc o ho with hAtLoc | hInVehicle
      · left
        rcases hAtLoc with ⟨l, hl, hat⟩
        exact ⟨l, hl, by simpa [unload_truck, hEq] using hat⟩
      · right
        rcases hInVehicle with ⟨v, hv, hin⟩
        exact ⟨v, hv, by simpa [unload_truck, hEq] using hin⟩

lemma unload_airplane_preserves_wf
    (var_obj var_airplane var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : unload_airplanePre var_obj var_airplane var_loc s) :
    WellFormed (unload_airplane var_obj var_airplane var_loc s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hObjMem, hAirplaneMem, hLocMem, hObjType, hAirplaneType,
      hLocType, hObjIn, hAirplaneAt⟩
  have hdis := wfStatic_disjoint s.statics hstatic

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change
      (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p o l = true
        at hat
    by_cases ho : o = var_obj
    · subst o
      by_cases hl : l = var_loc
      · subst l
        exact ⟨hObjMem, hLocMem, hLocType, Or.inr (Or.inr hObjType)⟩
      · apply hAt var_obj l
        simpa [unload_airplane, hl] using hat
    · apply hAt o l
      simpa [unload_airplane, ho] using hat

  · intro o v hin
    apply hIn o v
    change s.dynamic.in_p o v = true
    change
      (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p o v = true
        at hin
    by_cases ho : o = var_obj
    · subst o
      by_cases hv : v = var_airplane
      · subst v
        simp [unload_airplane] at hin
      · simpa [unload_airplane, hv] using hin
    · simpa [unload_airplane, ho] using hin

  · intro p l hp hat
    apply hAir p l hp
    have hne : p ≠ var_obj :=
      (obj_ne_airplane_of_disjoint hdis hObjType hp).symm
    change
      (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p p l = true
        at hat
    simpa [unload_airplane, hne] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    apply hVehicleUnique v l₁ l₂ hv
    · change
        (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p v l₁ =
          true at hat₁
      simpa [unload_airplane, hne] using hat₁
    · change
        (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p v l₂ =
          true at hat₂
      simpa [unload_airplane, hne] using hat₂

  · intro o ho hboth
    by_cases hEq : o = var_obj
    · subst o
      rcases hboth.2 with ⟨v, hin⟩
      change
        (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p
            var_obj v = true at hin
      by_cases hv : v = var_airplane
      · subst v
        simp [unload_airplane] at hin
      · have hOldIn : s.dynamic.in_p var_obj v = true := by
          simpa [unload_airplane, hv] using hin
        have hCarrierEq :=
          hUniqueIn var_obj v var_airplane hObjType hOldIn hObjIn
        exact hv hCarrierEq
    · apply hXor o ho
      constructor
      · rcases hboth.1 with ⟨l, hat⟩
        refine ⟨l, ?_⟩
        change
          (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p o l =
            true at hat
        simpa [unload_airplane, hEq] using hat
      · rcases hboth.2 with ⟨v, hin⟩
        refine ⟨v, ?_⟩
        change
          (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p o v =
            true at hin
        simpa [unload_airplane, hEq] using hin

  · intro o l₁ l₂ ho hat₁ hat₂
    by_cases hEq : o = var_obj
    · subst o
      have forceLoc :
          ∀ l,
            (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p
                var_obj l = true →
            l = var_loc := by
        intro l hat
        by_contra hl
        have hOldAt : s.dynamic.at_p var_obj l = true := by
          simpa [unload_airplane, hl] using hat
        exact (hXor var_obj hObjType)
          ⟨⟨l, hOldAt⟩, ⟨var_airplane, hObjIn⟩⟩
      exact (forceLoc l₁ hat₁).trans (forceLoc l₂ hat₂).symm
    · apply hUniqueAt o l₁ l₂ ho
      · change
          (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p o l₁ =
            true at hat₁
        simpa [unload_airplane, hEq] using hat₁
      · change
          (unload_airplane var_obj var_airplane var_loc s).dynamic.at_p o l₂ =
            true at hat₂
        simpa [unload_airplane, hEq] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    have oldOfNew :
        ∀ x v,
          (unload_airplane var_obj var_airplane var_loc s).dynamic.in_p x v =
              true →
          s.dynamic.in_p x v = true := by
      intro x v hin
      by_cases hx : x = var_obj
      · subst x
        by_cases hv : v = var_airplane
        · subst v
          simp [unload_airplane] at hin
        · simpa [unload_airplane, hv] using hin
      · simpa [unload_airplane, hx] using hin
    apply hUniqueIn o v₁ v₂ ho
    · change s.dynamic.in_p o v₁ = true
      exact oldOfNew o v₁ hin₁
    · change s.dynamic.in_p o v₂ = true
      exact oldOfNew o v₂ hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    refine ⟨t, l, ht, hl, hil, ?_⟩
    have hne : t ≠ var_obj :=
      (obj_ne_truck_of_disjoint hdis hObjType ht).symm
    simpa [unload_airplane, hne] using hat

  · intro v hv
    rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
    refine ⟨l, hl, ?_⟩
    have hne : v ≠ var_obj := by
      intro hEq
      subst v
      rcases hv with ht | hp
      · exact (obj_ne_truck_of_disjoint hdis hObjType ht) rfl
      · exact (obj_ne_airplane_of_disjoint hdis hObjType hp) rfl
    simpa [unload_airplane, hne] using hat

  · intro o ho
    by_cases hEq : o = var_obj
    · subst o
      exact Or.inl
        ⟨var_loc, hLocType,
          unload_airplane_at_p_eq1 var_obj var_airplane var_loc s⟩
    · rcases hPackageLoc o ho with hAtLoc | hInVehicle
      · left
        rcases hAtLoc with ⟨l, hl, hat⟩
        exact ⟨l, hl, by simpa [unload_airplane, hEq] using hat⟩
      · right
        rcases hInVehicle with ⟨v, hv, hin⟩
        exact ⟨v, hv, by simpa [unload_airplane, hEq] using hin⟩

lemma drive_truck_preserves_wf
    (var_truck var_loc_from var_loc_to var_city)
    (s : State)
    (hwf : WellFormed s)
    (hpre : drive_truckPre var_truck var_loc_from var_loc_to var_city s) :
    WellFormed (drive_truck var_truck var_loc_from var_loc_to var_city s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hTruckMem, hFromMem, hToMem, hCityMem, hTruckType,
      hFromType, hToType, hCityType, hTruckAtFrom,
      hFromInCity, hToInCity⟩
  have hdis := wfStatic_disjoint s.statics hstatic
  have hEach := wfStatic_eachLocInOneCity s.statics hstatic

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change
      (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p
          o l = true at hat
    by_cases ho : o = var_truck
    · subst o
      by_cases hTo : l = var_loc_to
      · subst l
        exact ⟨hTruckMem, hToMem, hToType, Or.inl hTruckType⟩
      · by_cases hFrom : l = var_loc_from
        · subst l
          simp [drive_truck, hTo] at hat
        · apply hAt var_truck l
          simpa [drive_truck, hTo, hFrom] using hat
    · apply hAt o l
      simpa [drive_truck, ho] using hat

  · intro o v hin
    apply hIn o v
    change Truthy.isTrue (s.dynamic.in_p o v)
    exact hin

  · intro p l hp hat
    apply hAir p l hp
    have hne : p ≠ var_truck :=
      (truck_ne_airplane_of_disjoint hdis hTruckType hp).symm
    change
      (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p
          p l = true at hat
    simpa [drive_truck, hne] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    by_cases hEq : v = var_truck
    · subst v
      have forceTo :
          ∀ l,
            (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p
                var_truck l = true →
            l = var_loc_to := by
        intro l hat
        by_contra hTo
        by_cases hFrom : l = var_loc_from
        · subst l
          simp [drive_truck, hTo] at hat
        · have hOldAt : s.dynamic.at_p var_truck l = true := by
            simpa [drive_truck, hTo, hFrom] using hat
          have hLocEq :=
            hVehicleUnique var_truck l var_loc_from
              (Or.inl hTruckType) hOldAt hTruckAtFrom
          exact hFrom hLocEq
      exact (forceTo l₁ hat₁).trans (forceTo l₂ hat₂).symm
    · apply hVehicleUnique v l₁ l₂ hv
      · change
          (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p
              v l₁ = true at hat₁
        simpa [drive_truck, hEq] using hat₁
      · change
          (drive_truck var_truck var_loc_from var_loc_to var_city s).dynamic.at_p
              v l₂ = true at hat₂
        simpa [drive_truck, hEq] using hat₂

  · intro o ho hboth
    have hne : o ≠ var_truck :=
      obj_ne_truck_of_disjoint hdis ho hTruckType
    apply hXor o ho
    rcases hboth with ⟨⟨l, hat⟩, ⟨v, hin⟩⟩
    constructor
    · exact ⟨l, by simpa [drive_truck, hne] using hat⟩
    · exact ⟨v, hin⟩

  · intro o l₁ l₂ ho hat₁ hat₂
    have hne : o ≠ var_truck :=
      obj_ne_truck_of_disjoint hdis ho hTruckType
    apply hUniqueAt o l₁ l₂ ho
    · simpa [drive_truck, hne] using hat₁
    · simpa [drive_truck, hne] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    apply hUniqueIn o v₁ v₂ ho
    · exact hin₁
    · exact hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    by_cases hEq : t = var_truck
    · subst t
      have hLocEq : l = var_loc_from :=
        hVehicleUnique var_truck l var_loc_from
          (Or.inl hTruckType) hat hTruckAtFrom
      subst l
      rcases hEach var_loc_from hFromType with
        ⟨c₀, hc₀, hUniqueCity⟩
      have hcEq : c = var_city := by
        have h₁ : c = c₀ :=
          hUniqueCity c ⟨hil, hc⟩
        have h₂ : var_city = c₀ :=
          hUniqueCity var_city ⟨hFromInCity, hCityType⟩
        exact h₁.trans h₂.symm
      subst c
      exact
        ⟨var_truck, var_loc_to, hTruckType, hToType, hToInCity,
          drive_truck_at_p_eq1
            var_truck var_loc_from var_loc_to var_city s⟩
    · exact
        ⟨t, l, ht, hl, hil, by
          simpa [drive_truck, hEq] using hat⟩

  · intro v hv
    by_cases hEq : v = var_truck
    · subst v
      exact
        ⟨var_loc_to, hToType,
          drive_truck_at_p_eq1
            var_truck var_loc_from var_loc_to var_city s⟩
    · rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
      exact
        ⟨l, hl, by
          simpa [drive_truck, hEq] using hat⟩

  · intro o ho
    have hne : o ≠ var_truck :=
      obj_ne_truck_of_disjoint hdis ho hTruckType
    rcases hPackageLoc o ho with hAtLoc | hInVehicle
    · left
      rcases hAtLoc with ⟨l, hl, hat⟩
      exact
        ⟨l, hl, by
          simpa [drive_truck, hne] using hat⟩
    · right
      rcases hInVehicle with ⟨v, hv, hin⟩
      exact ⟨v, hv, hin⟩

lemma fly_airplane_preserves_wf
    (var_airplane var_loc_from var_loc_to)
    (s : State)
    (hwf : WellFormed s)
    (hpre : fly_airplanePre var_airplane var_loc_from var_loc_to s) :
    WellFormed (fly_airplane var_airplane var_loc_from var_loc_to s) := by
  rcases hwf with
    ⟨hstatic, hAt, hIn, hAir, hVehicleUnique, hXor,
      hUniqueAt, hUniqueIn, hTrucks, hVehicleLoc, hPackageLoc⟩
  rcases hpre with
    ⟨hAirplaneMem, hFromMem, hToMem, hAirplaneType,
      hFromAirport, hToAirport, hAirplaneAtFrom⟩
  have hdis := wfStatic_disjoint s.statics hstatic
  have hAirports := wfStatic_airportsAreLocs s.statics hstatic
  have hFromType : s.statics.location_p var_loc_from = true :=
    hAirports var_loc_from hFromAirport
  have hToType : s.statics.location_p var_loc_to = true :=
    hAirports var_loc_to hToAirport

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro o l hat
    change
      (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p o l =
        true at hat
    by_cases ho : o = var_airplane
    · subst o
      by_cases hTo : l = var_loc_to
      · subst l
        exact
          ⟨hAirplaneMem, hToMem, hToType,
            Or.inr (Or.inl hAirplaneType)⟩
      · by_cases hFrom : l = var_loc_from
        · subst l
          simp [fly_airplane, hTo] at hat
        · apply hAt var_airplane l
          simpa [fly_airplane, hTo, hFrom] using hat
    · apply hAt o l
      simpa [fly_airplane, ho] using hat

  · intro o v hin
    apply hIn o v
    change Truthy.isTrue (s.dynamic.in_p o v)
    exact hin

  · intro p l hp hat
    by_cases hEq : p = var_airplane
    · subst p
      by_cases hTo : l = var_loc_to
      · subst l
        exact hToAirport
      · by_cases hFrom : l = var_loc_from
        · subst l
          simp [fly_airplane, hTo] at hat
        · apply hAir var_airplane l hAirplaneType
          change
            (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p
                var_airplane l = true at hat
          simpa [fly_airplane, hTo, hFrom] using hat
    · apply hAir p l hp
      change
        (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p p l =
          true at hat
      simpa [fly_airplane, hEq] using hat

  · intro v l₁ l₂ hv hat₁ hat₂
    by_cases hEq : v = var_airplane
    · subst v
      have forceTo :
          ∀ l,
            (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p
                var_airplane l = true →
            l = var_loc_to := by
        intro l hat
        by_contra hTo
        by_cases hFrom : l = var_loc_from
        · subst l
          simp [fly_airplane, hTo] at hat
        · have hOldAt : s.dynamic.at_p var_airplane l = true := by
            simpa [fly_airplane, hTo, hFrom] using hat
          have hLocEq :=
            hVehicleUnique var_airplane l var_loc_from
              (Or.inr hAirplaneType) hOldAt hAirplaneAtFrom
          exact hFrom hLocEq
      exact (forceTo l₁ hat₁).trans (forceTo l₂ hat₂).symm
    · apply hVehicleUnique v l₁ l₂ hv
      · change
          (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p
              v l₁ = true at hat₁
        simpa [fly_airplane, hEq] using hat₁
      · change
          (fly_airplane var_airplane var_loc_from var_loc_to s).dynamic.at_p
              v l₂ = true at hat₂
        simpa [fly_airplane, hEq] using hat₂

  · intro o ho hboth
    have hne : o ≠ var_airplane :=
      obj_ne_airplane_of_disjoint hdis ho hAirplaneType
    apply hXor o ho
    rcases hboth with ⟨⟨l, hat⟩, ⟨v, hin⟩⟩
    constructor
    · exact ⟨l, by simpa [fly_airplane, hne] using hat⟩
    · exact ⟨v, hin⟩

  · intro o l₁ l₂ ho hat₁ hat₂
    have hne : o ≠ var_airplane :=
      obj_ne_airplane_of_disjoint hdis ho hAirplaneType
    apply hUniqueAt o l₁ l₂ ho
    · simpa [fly_airplane, hne] using hat₁
    · simpa [fly_airplane, hne] using hat₂

  · intro o v₁ v₂ ho hin₁ hin₂
    apply hUniqueIn o v₁ v₂ ho
    · exact hin₁
    · exact hin₂

  · intro c hc
    rcases hTrucks c hc with ⟨t, l, ht, hl, hil, hat⟩
    have hne : t ≠ var_airplane :=
      truck_ne_airplane_of_disjoint hdis ht hAirplaneType
    exact
      ⟨t, l, ht, hl, hil, by
        simpa [fly_airplane, hne] using hat⟩

  · intro v hv
    by_cases hEq : v = var_airplane
    · subst v
      exact
        ⟨var_loc_to, hToType,
          fly_airplane_at_p_eq1
            var_airplane var_loc_from var_loc_to s⟩
    · rcases hVehicleLoc v hv with ⟨l, hl, hat⟩
      exact
        ⟨l, hl, by
          simpa [fly_airplane, hEq] using hat⟩

  · intro o ho
    have hne : o ≠ var_airplane :=
      obj_ne_airplane_of_disjoint hdis ho hAirplaneType
    rcases hPackageLoc o ho with hAtLoc | hInVehicle
    · left
      rcases hAtLoc with ⟨l, hl, hat⟩
      exact
        ⟨l, hl, by
          simpa [fly_airplane, hne] using hat⟩
    · right
      rcases hInVehicle with ⟨v, hv, hin⟩
      exact ⟨v, hv, hin⟩

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | load_truck var_obj var_truck var_loc =>
      exact load_truck_preserves_wf var_obj var_truck var_loc s hwf hpre
  | load_airplane var_obj var_airplane var_loc =>
      exact load_airplane_preserves_wf var_obj var_airplane var_loc s hwf hpre
  | unload_truck var_obj var_truck var_loc =>
      exact unload_truck_preserves_wf var_obj var_truck var_loc s hwf hpre
  | unload_airplane var_obj var_airplane var_loc =>
      exact unload_airplane_preserves_wf var_obj var_airplane var_loc s hwf hpre
  | drive_truck var_truck var_loc_from var_loc_to var_city =>
      exact drive_truck_preserves_wf var_truck var_loc_from var_loc_to var_city s hwf hpre
  | fly_airplane var_airplane var_loc_from var_loc_to =>
      exact fly_airplane_preserves_wf var_airplane var_loc_from var_loc_to s hwf hpre

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

@[simp] lemma gp_bool_and_eq_true (a b : Bool) :
    ((a && b) = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

@[simp] lemma gp_bool_or_eq_true (a b : Bool) :
    ((a || b) = true) ↔ (a = true ∨ b = true) := by
  cases a <;> cases b <;> simp

lemma gpFind_some_spec
    {xs : List Obj} {p : Obj → Bool} {x : Obj}
    (h : gpFind xs p = some x) :
    x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [gpFind] at h
  | cons y ys ih =>
      by_cases hy : p y = true
      · simp [gpFind, hy] at h
        subst x
        exact ⟨by simp, hy⟩
      · simp [gpFind, hy] at h
        rcases ih h with ⟨hx, hp⟩
        exact ⟨by simp [hx], hp⟩

lemma gpFind_exists_some
    {xs : List Obj} {p : Obj → Bool}
    (h : ∃ x, x ∈ xs ∧ p x = true) :
    ∃ x, gpFind xs p = some x := by
  induction xs with
  | nil =>
      rcases h with ⟨x, hx, _⟩
      simp at hx
  | cons y ys ih =>
      by_cases hy : p y = true
      · exact ⟨y, by simp [gpFind, hy]⟩
      · rcases h with ⟨x, hx, hp⟩
        simp only [List.mem_cons] at hx
        rcases hx with hxy | hx
        · subst x
          exact False.elim (hy hp)
        · rcases ih ⟨x, hx, hp⟩ with ⟨z, hz⟩
          exact ⟨z, by simp [gpFind, hy, hz]⟩

lemma gpChoose_spec
    {xs : List Obj} {p : Obj → Bool}
    (h : ∃ x, x ∈ xs ∧ p x = true) :
    gpChoose xs p ∈ xs ∧ p (gpChoose xs p) = true := by
  rcases gpFind_exists_some h with ⟨x, hx⟩
  have hs := gpFind_some_spec hx
  simpa [gpChoose, hx] using hs

lemma gpAny_eq_true_iff
    {xs : List Obj} {p : Obj → Bool} :
    gpAny xs p = true ↔ ∃ x, x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [gpAny]
  | cons x xs ih =>
      by_cases hx : p x = true
      · simp [gpAny, hx]
      · simp [gpAny, hx, ih]

lemma gpGoalAt_eq_true_iff (g : Goal) (o l : Obj) :
    gpGoalAt g o l = true ↔
      g.dynamic.at_p o l = some true := by
  cases h : g.dynamic.at_p o l with
  | none =>
      simp [gpGoalAt, h]
  | some b =>
      cases b <;> simp [gpGoalAt, h]

lemma wfStatic_validObj'
    {s : StaticState} (h : WellFormedStatic s) :
    ValidObjParam s := by
  exact h.2.1

lemma wfStatic_validTruck'
    {s : StaticState} (h : WellFormedStatic s) :
    ValidTruckParam s := by
  exact h.2.2.1

lemma wfStatic_validLocation'
    {s : StaticState} (h : WellFormedStatic s) :
    ValidLocationParam s := by
  exact h.2.2.2.1

lemma wfStatic_validAirplane'
    {s : StaticState} (h : WellFormedStatic s) :
    ValidAirplaneParam s := by
  exact h.2.2.2.2.1

lemma wfStatic_validCity'
    {s : StaticState} (h : WellFormedStatic s) :
    ValidCityParam s := by
  exact h.2.2.2.2.2.1

lemma wfStatic_cityAirport'
    {s : StaticState} (h : WellFormedStatic s) :
    CityHasExactlyOneAirport s := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, hAirport, _, _, _⟩
  exact hAirport

lemma wfStatic_minObjects'
    {s : StaticState} (h : WellFormedStatic s) :
    MinNumObj s := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hMin⟩
  exact hMin

lemma wf_vehicleUnique'
    {s : State} (h : WellFormed s) :
    VehicleUniqueLoc s.statics s.dynamic := by
  rcases h with ⟨_, _, _, _, hUnique, _, _, _, _, _, _⟩
  exact hUnique

lemma wf_airplanesAtAirports'
    {s : State} (h : WellFormed s) :
    AirplanesOnlyAtAirports s.statics s.dynamic := by
  rcases h with ⟨_, _, _, hAir, _, _, _, _, _, _, _⟩
  exact hAir

lemma wf_vehicleHasLocation'
    {s : State} (h : WellFormed s) :
    VehicleHasLocation s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hVehicle, _⟩
  exact hVehicle

lemma wf_packageHasLocation'
    {s : State} (h : WellFormed s) :
    PackageHasLocationOrVehicle s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, hPackage⟩
  exact hPackage

lemma wf_truckPerCity'
    {s : State} (h : WellFormed s) :
    AtLeastOneTruckPerCity s := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hTruck, _, _⟩
  exact hTruck

def GPGoalSpec (st : StaticState) (g : Goal) : Prop :=
  ValidAtParam st g.dynamic ∧
  (∀ o, st.obj_p o = true →
    ∃! l, st.location_p l = true ∧
      g.dynamic.at_p o l = some true) ∧
  (∀ v l,
    (st.truck_p v = true ∨ st.airplane_p v = true) →
      g.dynamic.at_p v l = none) ∧
  (∀ o l, g.dynamic.at_p o l ≠ some false) ∧
  (∀ o v, g.dynamic.in_p o v = none)

lemma gpGoalSpec_of_wellFormedGoal
    {s : State} {g : Goal}
    (h : WellFormedGoal s g) :
    GPGoalSpec s.statics g := by
  rcases h with
    ⟨_, hAt, _, _, _, _, _, _, hPositive,
      hTarget, hVehicle, hIn⟩
  exact ⟨hAt, hTarget, hVehicle, hPositive, hIn⟩

lemma gpGoalTarget_spec
    (s : State) (g : Goal) (o : Obj)
    (hstatic : WellFormedStatic s.statics)
    (hgoal : GPGoalSpec s.statics g)
    (ho : s.statics.obj_p o = true) :
    gpGoalTarget s g o ∈ s.statics.objects ∧
    s.statics.location_p (gpGoalTarget s g o) = true ∧
    g.dynamic.at_p o (gpGoalTarget s g o) = some true ∧
    ∀ l, g.dynamic.at_p o l = some true →
      l = gpGoalTarget s g o := by
  rcases hgoal with
    ⟨hValidAt, hTargets, _, _, _⟩
  rcases hTargets o ho with
    ⟨target, htarget, hunique⟩
  have htargetMem :
      target ∈ s.statics.objects :=
    wfStatic_validLocation' hstatic target htarget.1
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun l =>
        s.statics.location_p l && gpGoalAt g o l)
      ⟨target, htargetMem, by
        apply (gp_bool_and_eq_true _ _).2
        exact
          ⟨htarget.1,
            (gpGoalAt_eq_true_iff g o target).2 htarget.2⟩⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hp' :=
    (gp_bool_and_eq_true _ _).1 hp
  have hchosenGoal :
      g.dynamic.at_p o
          (gpChoose s.statics.objects
            (fun l =>
              s.statics.location_p l && gpGoalAt g o l)) =
        some true :=
    (gpGoalAt_eq_true_iff g o _).1 hp'.2
  have hchosenTarget :
      gpChoose s.statics.objects
          (fun l =>
            s.statics.location_p l && gpGoalAt g o l) =
        target :=
    hunique _ ⟨hp'.1, hchosenGoal⟩
  change
    gpChoose s.statics.objects
        (fun l =>
          s.statics.location_p l && gpGoalAt g o l)
        ∈ s.statics.objects ∧
    s.statics.location_p
        (gpChoose s.statics.objects
          (fun l =>
            s.statics.location_p l && gpGoalAt g o l)) = true ∧
    g.dynamic.at_p o
        (gpChoose s.statics.objects
          (fun l =>
            s.statics.location_p l && gpGoalAt g o l)) =
        some true ∧
    ∀ l, g.dynamic.at_p o l = some true →
      l =
        gpChoose s.statics.objects
          (fun l =>
            s.statics.location_p l && gpGoalAt g o l)
  refine ⟨hmem, hp'.1, hchosenGoal, ?_⟩
  intro l hl
  have htruth :
      Truthy.isTrue (g.dynamic.at_p o l) := by
    change g.dynamic.at_p o l = some true
    exact hl
  have hloc := (hValidAt o l htruth).2.2.1
  have hlTarget : l = target :=
    hunique l ⟨hloc, hl⟩
  exact hlTarget.trans hchosenTarget.symm

lemma gpCityOfLocation_spec
    (s : State) (l : Obj)
    (hwf : WellFormed s)
    (hl : s.statics.location_p l = true) :
    gpCityOfLocation s l ∈ s.statics.objects ∧
    s.statics.city_p (gpCityOfLocation s l) = true ∧
    s.statics.in_city_p l (gpCityOfLocation s l) = true := by
  have hstatic := hwf.1
  rcases wfStatic_eachLocInOneCity s.statics hstatic l hl with
    ⟨c, hc, _⟩
  have hcmem :=
    wfStatic_validCity' hstatic c hc.2
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun c =>
        s.statics.city_p c && s.statics.in_city_p l c)
      ⟨c, hcmem, by
        apply (gp_bool_and_eq_true _ _).2
        exact ⟨hc.2, hc.1⟩⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hp' := (gp_bool_and_eq_true _ _).1 hp
  exact ⟨hmem, hp'.1, hp'.2⟩

lemma gpAirportInCity_spec
    (s : State) (c : Obj)
    (hwf : WellFormed s)
    (hc : s.statics.city_p c = true) :
    gpAirportInCity s c ∈ s.statics.objects ∧
    s.statics.location_p (gpAirportInCity s c) = true ∧
    s.statics.airport_p (gpAirportInCity s c) = true ∧
    s.statics.in_city_p (gpAirportInCity s c) c = true := by
  have hstatic := hwf.1
  rcases wfStatic_cityAirport' hstatic c hc with
    ⟨a, ha, _⟩
  have hamem :=
    wfStatic_validLocation' hstatic a ha.1
  have hpred :
      (s.statics.location_p a &&
       s.statics.airport_p a &&
       s.statics.in_city_p a c) = true := by
    apply (gp_bool_and_eq_true _ _).2
    constructor
    · apply (gp_bool_and_eq_true _ _).2
      exact ⟨ha.1, ha.2.2⟩
    · exact ha.2.1
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun l =>
        s.statics.location_p l &&
        s.statics.airport_p l &&
        s.statics.in_city_p l c)
      ⟨a, hamem, hpred⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hpOuter := (gp_bool_and_eq_true _ _).1 hp
  have hpInner := (gp_bool_and_eq_true _ _).1 hpOuter.1
  exact ⟨hmem, hpInner.1, hpInner.2, hpOuter.2⟩

lemma gpVehicleLocation_spec
    (s : State) (v : Obj)
    (hwf : WellFormed s)
    (hv :
      s.statics.truck_p v = true ∨
      s.statics.airplane_p v = true) :
    gpVehicleLocation s v ∈ s.statics.objects ∧
    s.statics.location_p (gpVehicleLocation s v) = true ∧
    s.dynamic.at_p v (gpVehicleLocation s v) = true := by
  rcases wf_vehicleHasLocation' hwf v hv with
    ⟨l, hl, hat⟩
  have hlmem :=
    wfStatic_validLocation' hwf.1 l hl
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun l =>
        s.statics.location_p l && s.dynamic.at_p v l)
      ⟨l, hlmem, by
        apply (gp_bool_and_eq_true _ _).2
        exact ⟨hl, hat⟩⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hp' := (gp_bool_and_eq_true _ _).1 hp
  exact ⟨hmem, hp'.1, hp'.2⟩

lemma gpTruckInCity_spec
    (s : State) (c : Obj)
    (hwf : WellFormed s)
    (hc : s.statics.city_p c = true) :
    gpTruckInCity s c ∈ s.statics.objects ∧
    s.statics.truck_p (gpTruckInCity s c) = true ∧
    ∃ l,
      l ∈ s.statics.objects ∧
      s.statics.location_p l = true ∧
      s.statics.in_city_p l c = true ∧
      s.dynamic.at_p (gpTruckInCity s c) l = true := by
  rcases wf_truckPerCity' hwf c hc with
    ⟨t, l, ht, hl, hil, hat⟩
  have htmem :=
    wfStatic_validTruck' hwf.1 t ht
  have hlmem :=
    wfStatic_validLocation' hwf.1 l hl
  have hlpred :
      (s.statics.location_p l &&
       s.statics.in_city_p l c &&
       s.dynamic.at_p t l) = true := by
    apply (gp_bool_and_eq_true _ _).2
    constructor
    · apply (gp_bool_and_eq_true _ _).2
      exact ⟨hl, hil⟩
    · exact hat
  have hany :
      gpAny s.statics.objects
        (fun l =>
          s.statics.location_p l &&
          s.statics.in_city_p l c &&
          s.dynamic.at_p t l) = true :=
    gpAny_eq_true_iff.mpr ⟨l, hlmem, hlpred⟩
  have houter :
      gpTruckHasLocationInCity s t c = true := by
    unfold gpTruckHasLocationInCity
    apply (gp_bool_and_eq_true _ _).2
    exact ⟨ht, hany⟩
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun t => gpTruckHasLocationInCity s t c)
      ⟨t, htmem, houter⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hparts :
      s.statics.truck_p (gpTruckInCity s c) = true ∧
      gpAny s.statics.objects
        (fun l =>
          s.statics.location_p l &&
          s.statics.in_city_p l c &&
          s.dynamic.at_p (gpTruckInCity s c) l) = true := by
    change
      (s.statics.truck_p (gpTruckInCity s c) &&
       gpAny s.statics.objects
         (fun l =>
           s.statics.location_p l &&
           s.statics.in_city_p l c &&
           s.dynamic.at_p (gpTruckInCity s c) l)) = true at hp
    exact (gp_bool_and_eq_true _ _).1 hp
  rcases gpAny_eq_true_iff.mp hparts.2 with
    ⟨l', hlmem', hlp⟩
  have hlpOuter := (gp_bool_and_eq_true _ _).1 hlp
  have hlpInner := (gp_bool_and_eq_true _ _).1 hlpOuter.1
  exact
    ⟨hmem, hparts.1, l', hlmem',
      hlpInner.1, hlpInner.2, hlpOuter.2⟩

lemma gpAirplane_spec
    (s : State)
    (hwf : WellFormed s) :
    gpAirplane s ∈ s.statics.objects ∧
    s.statics.airplane_p (gpAirplane s) = true := by
  rcases wfStatic_minObjects' hwf.1 with
    ⟨_, _, _, _, p, hp⟩
  have hpmem :=
    wfStatic_validAirplane' hwf.1 p hp
  exact
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun p => s.statics.airplane_p p)
      ⟨p, hpmem, hp⟩

lemma gpCarrierOf_spec
    (s : State) (o : Obj)
    (hwf : WellFormed s)
    (hcarrier :
      ∃ v,
        (s.statics.truck_p v = true ∨
         s.statics.airplane_p v = true) ∧
        s.dynamic.in_p o v = true) :
    gpCarrierOf s o ∈ s.statics.objects ∧
    (s.statics.truck_p (gpCarrierOf s o) = true ∨
     s.statics.airplane_p (gpCarrierOf s o) = true) ∧
    s.dynamic.in_p o (gpCarrierOf s o) = true := by
  rcases hcarrier with ⟨v, hvtype, hin⟩
  have hvmem : v ∈ s.statics.objects := by
    rcases hvtype with ht | hp
    · exact wfStatic_validTruck' hwf.1 v ht
    · exact wfStatic_validAirplane' hwf.1 v hp
  have hor :
      (s.statics.truck_p v || s.statics.airplane_p v) = true :=
    (gp_bool_or_eq_true _ _).2 hvtype
  have hpred :
      ((s.statics.truck_p v || s.statics.airplane_p v) &&
       s.dynamic.in_p o v) = true :=
    (gp_bool_and_eq_true _ _).2 ⟨hor, hin⟩
  have hchoose :=
    gpChoose_spec
      (xs := s.statics.objects)
      (p := fun v =>
        (s.statics.truck_p v || s.statics.airplane_p v) &&
        s.dynamic.in_p o v)
      ⟨v, hvmem, hpred⟩
  rcases hchoose with ⟨hmem, hp⟩
  have hp' := (gp_bool_and_eq_true _ _).1 hp
  have htype := (gp_bool_or_eq_true _ _).1 hp'.1
  exact ⟨hmem, htype, hp'.2⟩

def GPMoveResult
    (o dst : Obj) (s : State)
    (r : List PlanAction × State) : Prop :=
  ValidPlan r.1 s ∧
  r.2 = runPlan r.1 s ∧
  WellFormed r.2 ∧
  r.2.statics = s.statics ∧
  r.2.statics.location_p dst = true ∧
  r.2.dynamic.at_p o dst = true ∧
  ∀ x, s.statics.obj_p x = true → x ≠ o →
    ∀ l, r.2.dynamic.at_p x l = s.dynamic.at_p x l

lemma gpMove_empty
    {o dst : Obj} {s : State}
    (hwf : WellFormed s)
    (hloc : s.statics.location_p dst = true)
    (hat : s.dynamic.at_p o dst = true) :
    GPMoveResult o dst s ([], s) := by
  exact
    ⟨by simp [ValidPlan],
      by simp [runPlan],
      hwf, rfl, hloc, hat,
      by intros; rfl⟩

lemma gpMove_compose
    {o mid dst : Obj} {s : State}
    {r₁ r₂ : List PlanAction × State}
    (h₁ : GPMoveResult o mid s r₁)
    (h₂ : GPMoveResult o dst r₁.2 r₂) :
    GPMoveResult o dst s (r₁.1 ++ r₂.1, r₂.2) := by
  rcases h₁ with
    ⟨hv₁, hr₁, _, hs₁, _, _, hpres₁⟩
  rcases h₂ with
    ⟨hv₂, hr₂, hwf₂, hs₂, hloc₂, hat₂, hpres₂⟩
  refine
    ⟨?_, ?_, hwf₂, hs₂.trans hs₁,
      hloc₂, hat₂, ?_⟩
  · exact
      (validPlan_append r₁.1 r₂.1 s).2
        ⟨hv₁, by rw [← hr₁]; exact hv₂⟩
  · rw [runPlan_append, ← hr₁, ← hr₂]
  · intro x hx hxo l
    have hx' : r₁.2.statics.obj_p x = true := by
      rw [hs₁]
      exact hx
    exact
      (hpres₂ x hx' hxo l).trans
        (hpres₁ x hx hxo l)

lemma truck_payload_correct
    (o truck src dst city : Obj) (s : State)
    (hwf : WellFormed s)
    (homem : o ∈ s.statics.objects)
    (htmem : truck ∈ s.statics.objects)
    (hsmem : src ∈ s.statics.objects)
    (hdmem : dst ∈ s.statics.objects)
    (hcmem : city ∈ s.statics.objects)
    (ho : s.statics.obj_p o = true)
    (ht : s.statics.truck_p truck = true)
    (hs : s.statics.location_p src = true)
    (hd : s.statics.location_p dst = true)
    (hc : s.statics.city_p city = true)
    (hsrcCity : s.statics.in_city_p src city = true)
    (hdstCity : s.statics.in_city_p dst city = true)
    (htruckAt : s.dynamic.at_p truck src = true)
    (hoAt : s.dynamic.at_p o src = true) :
    GPMoveResult o dst s
      ([PlanAction.load_truck o truck src,
        PlanAction.drive_truck truck src dst city,
        PlanAction.unload_truck o truck dst],
       runPlan
        [PlanAction.load_truck o truck src,
         PlanAction.drive_truck truck src dst city,
         PlanAction.unload_truck o truck dst] s) := by
  let s₁ := load_truck o truck src s
  let s₂ := drive_truck truck src dst city s₁
  have hdis := wfStatic_disjoint s.statics hwf.1
  have hto : truck ≠ o :=
    (obj_ne_truck_of_disjoint hdis ho ht).symm
  have hpre₁ : load_truckPre o truck src s :=
    ⟨homem, htmem, hsmem, ho, ht, hs, htruckAt, hoAt⟩
  have htruckAt₁ : s₁.dynamic.at_p truck src = true := by
    unfold s₁
    simpa [load_truck, hto] using htruckAt
  have hpre₂ :
      drive_truckPre truck src dst city s₁ :=
    ⟨htmem, hsmem, hdmem, hcmem, ht, hs, hd, hc,
      htruckAt₁, hsrcCity, hdstCity⟩
  have hpre₃ : unload_truckPre o truck dst s₂ := by
    refine
      ⟨homem, htmem, hdmem, ho, ht, hd, ?_, ?_⟩
    · exact drive_truck_at_p_eq1 truck src dst city s₁
    · unfold s₂
      rw [drive_truck_in_p]
      exact load_truck_in_p_eq1 o truck src s
  have hvalid :
      ValidPlan
        [PlanAction.load_truck o truck src,
         PlanAction.drive_truck truck src dst city,
         PlanAction.unload_truck o truck dst] s := by
    simp only [ValidPlan]
    refine ⟨hpre₁, ?_⟩
    change
      drive_truckPre truck src dst city s₁ ∧
      ValidPlan [PlanAction.unload_truck o truck dst] s₂
    refine ⟨hpre₂, ?_⟩
    change unload_truckPre o truck dst s₂ ∧ True
    exact ⟨hpre₃, trivial⟩
  refine
    ⟨hvalid, rfl,
      validPlan_preserves_wf hvalid hwf,
      runPlan_statics _ _,
      ?_, ?_, ?_⟩
  · rw [runPlan_statics]
    exact hd
  · simp only [runPlan]
    change
      (unload_truck o truck dst
        (drive_truck truck src dst city
          (load_truck o truck src s))).dynamic.at_p o dst = true
    exact unload_truck_at_p_eq1 o truck dst _
  · intro x hx hxo l
    have hxt : x ≠ truck :=
      obj_ne_truck_of_disjoint hdis hx ht
    simp only [runPlan]
    change
      (unload_truck o truck dst
        (drive_truck truck src dst city
          (load_truck o truck src s))).dynamic.at_p x l =
        s.dynamic.at_p x l
    rw [unload_truck_at_p_ne o truck dst _ hxo]
    change
      (drive_truck truck src dst city
        (load_truck o truck src s)).dynamic.at_p x l =
        s.dynamic.at_p x l
    simp [drive_truck, hxt]
    exact load_truck_at_p_ne o truck src s hxo

lemma air_payload_correct
    (o airplane src dst : Obj) (s : State)
    (hwf : WellFormed s)
    (homem : o ∈ s.statics.objects)
    (hpmem : airplane ∈ s.statics.objects)
    (hsmem : src ∈ s.statics.objects)
    (hdmem : dst ∈ s.statics.objects)
    (ho : s.statics.obj_p o = true)
    (hp : s.statics.airplane_p airplane = true)
    (hsa : s.statics.airport_p src = true)
    (hda : s.statics.airport_p dst = true)
    (hoAt : s.dynamic.at_p o src = true)
    (hpAt : s.dynamic.at_p airplane src = true) :
    GPMoveResult o dst s
      ([PlanAction.load_airplane o airplane src,
        PlanAction.fly_airplane airplane src dst,
        PlanAction.unload_airplane o airplane dst],
       runPlan
        [PlanAction.load_airplane o airplane src,
         PlanAction.fly_airplane airplane src dst,
         PlanAction.unload_airplane o airplane dst] s) := by
  let s₁ := load_airplane o airplane src s
  let s₂ := fly_airplane airplane src dst s₁
  have hdis := wfStatic_disjoint s.statics hwf.1
  have hpo : airplane ≠ o :=
    (obj_ne_airplane_of_disjoint hdis ho hp).symm
  have hs :
      s.statics.location_p src = true :=
    wfStatic_airportsAreLocs s.statics hwf.1 src hsa
  have hd :
      s.statics.location_p dst = true :=
    wfStatic_airportsAreLocs s.statics hwf.1 dst hda
  have hpre₁ :
      load_airplanePre o airplane src s :=
    ⟨homem, hpmem, hsmem, ho, hp, hs, hoAt, hpAt⟩
  have hpAt₁ :
      s₁.dynamic.at_p airplane src = true := by
    unfold s₁
    simpa [load_airplane, hpo] using hpAt
  have hpre₂ :
      fly_airplanePre airplane src dst s₁ :=
    ⟨hpmem, hsmem, hdmem, hp, hsa, hda, hpAt₁⟩
  have hpre₃ :
      unload_airplanePre o airplane dst s₂ := by
    refine
      ⟨homem, hpmem, hdmem, ho, hp, hd, ?_, ?_⟩
    · unfold s₂
      rw [fly_airplane_in_p]
      exact load_airplane_in_p_eq1 o airplane src s
    · exact fly_airplane_at_p_eq1 airplane src dst s₁
  have hvalid :
      ValidPlan
        [PlanAction.load_airplane o airplane src,
         PlanAction.fly_airplane airplane src dst,
         PlanAction.unload_airplane o airplane dst] s := by
    simp only [ValidPlan]
    refine ⟨hpre₁, ?_⟩
    change
      fly_airplanePre airplane src dst s₁ ∧
      ValidPlan [PlanAction.unload_airplane o airplane dst] s₂
    refine ⟨hpre₂, ?_⟩
    change unload_airplanePre o airplane dst s₂ ∧ True
    exact ⟨hpre₃, trivial⟩
  refine
    ⟨hvalid, rfl,
      validPlan_preserves_wf hvalid hwf,
      runPlan_statics _ _,
      ?_, ?_, ?_⟩
  · rw [runPlan_statics]
    exact hd
  · simp only [runPlan]
    change
      (unload_airplane o airplane dst
        (fly_airplane airplane src dst
          (load_airplane o airplane src s))).dynamic.at_p o dst = true
    exact unload_airplane_at_p_eq1 o airplane dst _
  · intro x hx hxo l
    have hxp : x ≠ airplane :=
      obj_ne_airplane_of_disjoint hdis hx hp
    simp only [runPlan]
    change
      (unload_airplane o airplane dst
        (fly_airplane airplane src dst
          (load_airplane o airplane src s))).dynamic.at_p x l =
        s.dynamic.at_p x l
    rw [unload_airplane_at_p_ne o airplane dst _ hxo]
    change
      (fly_airplane airplane src dst
        (load_airplane o airplane src s)).dynamic.at_p x l =
        s.dynamic.at_p x l
    simp [fly_airplane, hxp]
    exact load_airplane_at_p_ne o airplane src s hxo

lemma truck_position_correct
    (o truck packageLoc frm dstLoc city : Obj) (s : State)
    (hwf : WellFormed s)
    (ho : s.statics.obj_p o = true)
    (hpackageLoc : s.statics.location_p packageLoc = true)
    (ht : s.statics.truck_p truck = true)
    (htmem : truck ∈ s.statics.objects)
    (hfmem : frm ∈ s.statics.objects)
    (hdmem : dstLoc ∈ s.statics.objects)
    (hcmem : city ∈ s.statics.objects)
    (hf : s.statics.location_p frm = true)
    (hd : s.statics.location_p dstLoc = true)
    (hc : s.statics.city_p city = true)
    (hfc : s.statics.in_city_p frm city = true)
    (hdc : s.statics.in_city_p dstLoc city = true)
    (htruckAt : s.dynamic.at_p truck frm = true)
    (hoAt : s.dynamic.at_p o packageLoc = true) :
    let plan :=
      if frm = dstLoc then []
      else [PlanAction.drive_truck truck frm dstLoc city]
    GPMoveResult o packageLoc s (plan, runPlan plan s) ∧
    (runPlan plan s).dynamic.at_p truck dstLoc = true := by
  by_cases hEq : frm = dstLoc
  · subst dstLoc
    simp only [if_pos rfl]
    constructor
    · exact gpMove_empty hwf hpackageLoc hoAt
    · simpa [runPlan] using htruckAt
  · have hpre :
      drive_truckPre truck frm dstLoc city s :=
      ⟨htmem, hfmem, hdmem, hcmem, ht, hf, hd, hc,
        htruckAt, hfc, hdc⟩
    have hvalid :
        ValidPlan
          [PlanAction.drive_truck truck frm dstLoc city] s := by
      change
        drive_truckPre truck frm dstLoc city s ∧ True
      exact ⟨hpre, trivial⟩
    have hdis := wfStatic_disjoint s.statics hwf.1
    have hot : o ≠ truck :=
      obj_ne_truck_of_disjoint hdis ho ht
    simp only [if_neg hEq]
    constructor
    · refine
        ⟨hvalid, rfl,
          validPlan_preserves_wf hvalid hwf,
          runPlan_statics _ _,
          ?_, ?_, ?_⟩
      · rw [runPlan_statics]
        exact hpackageLoc
      · simp only [runPlan]
        change
          (drive_truck truck frm dstLoc city s).dynamic.at_p
            o packageLoc = true
        simpa [drive_truck, hot] using hoAt
      · intro x hx hxo l
        have hxt :=
          obj_ne_truck_of_disjoint hdis hx ht
        simp only [runPlan]
        change
          (drive_truck truck frm dstLoc city s).dynamic.at_p x l =
            s.dynamic.at_p x l
        simp [drive_truck, hxt]
    · simp only [runPlan]
      exact drive_truck_at_p_eq1 truck frm dstLoc city s

lemma airplane_position_correct
    (o airplane packageLoc frm dstLoc : Obj) (s : State)
    (hwf : WellFormed s)
    (ho : s.statics.obj_p o = true)
    (hpackageLoc : s.statics.location_p packageLoc = true)
    (hp : s.statics.airplane_p airplane = true)
    (hpmem : airplane ∈ s.statics.objects)
    (hfmem : frm ∈ s.statics.objects)
    (hdmem : dstLoc ∈ s.statics.objects)
    (hfa : s.statics.airport_p frm = true)
    (hda : s.statics.airport_p dstLoc = true)
    (hpAt : s.dynamic.at_p airplane frm = true)
    (hoAt : s.dynamic.at_p o packageLoc = true) :
    let plan :=
      if frm = dstLoc then []
      else [PlanAction.fly_airplane airplane frm dstLoc]
    GPMoveResult o packageLoc s (plan, runPlan plan s) ∧
    (runPlan plan s).dynamic.at_p airplane dstLoc = true := by
  by_cases hEq : frm = dstLoc
  · subst dstLoc
    simp only [if_pos rfl]
    constructor
    · exact gpMove_empty hwf hpackageLoc hoAt
    · simpa [runPlan] using hpAt
  · have hpre :
      fly_airplanePre airplane frm dstLoc s :=
      ⟨hpmem, hfmem, hdmem, hp, hfa, hda, hpAt⟩
    have hvalid :
        ValidPlan
          [PlanAction.fly_airplane airplane frm dstLoc] s := by
      change
        fly_airplanePre airplane frm dstLoc s ∧ True
      exact ⟨hpre, trivial⟩
    have hdis := wfStatic_disjoint s.statics hwf.1
    have hop : o ≠ airplane :=
      obj_ne_airplane_of_disjoint hdis ho hp
    simp only [if_neg hEq]
    constructor
    · refine
        ⟨hvalid, rfl,
          validPlan_preserves_wf hvalid hwf,
          runPlan_statics _ _,
          ?_, ?_, ?_⟩
      · rw [runPlan_statics]
        exact hpackageLoc
      · simp only [runPlan]
        change
          (fly_airplane airplane frm dstLoc s).dynamic.at_p
            o packageLoc = true
        simpa [fly_airplane, hop] using hoAt
      · intro x hx hxo l
        have hxp :=
          obj_ne_airplane_of_disjoint hdis hx hp
        simp only [runPlan]
        change
          (fly_airplane airplane frm dstLoc s).dynamic.at_p x l =
            s.dynamic.at_p x l
        simp [fly_airplane, hxp]
    · simp only [runPlan]
      exact fly_airplane_at_p_eq1 airplane frm dstLoc s

lemma unload_truck_move_correct
    (o truck l : Obj) (s : State)
    (hwf : WellFormed s)
    (homem : o ∈ s.statics.objects)
    (htmem : truck ∈ s.statics.objects)
    (hlmem : l ∈ s.statics.objects)
    (ho : s.statics.obj_p o = true)
    (ht : s.statics.truck_p truck = true)
    (hl : s.statics.location_p l = true)
    (htruckAt : s.dynamic.at_p truck l = true)
    (hin : s.dynamic.in_p o truck = true) :
    GPMoveResult o l s
      ([PlanAction.unload_truck o truck l],
       runPlan [PlanAction.unload_truck o truck l] s) := by
  have hpre :
      unload_truckPre o truck l s :=
    ⟨homem, htmem, hlmem, ho, ht, hl, htruckAt, hin⟩
  have hvalid :
      ValidPlan [PlanAction.unload_truck o truck l] s := by
    change unload_truckPre o truck l s ∧ True
    exact ⟨hpre, trivial⟩
  refine
    ⟨hvalid, rfl,
      validPlan_preserves_wf hvalid hwf,
      runPlan_statics _ _,
      ?_, ?_, ?_⟩
  · rw [runPlan_statics]
    exact hl
  · simp only [runPlan]
    change
      (unload_truck o truck l s).dynamic.at_p o l = true
    exact unload_truck_at_p_eq1 o truck l s
  · intro x hx hxo l'
    simp only [runPlan]
    change
      (unload_truck o truck l s).dynamic.at_p x l' =
        s.dynamic.at_p x l'
    exact unload_truck_at_p_ne o truck l s hxo

lemma unload_airplane_move_correct
    (o airplane l : Obj) (s : State)
    (hwf : WellFormed s)
    (homem : o ∈ s.statics.objects)
    (hpmem : airplane ∈ s.statics.objects)
    (hlmem : l ∈ s.statics.objects)
    (ho : s.statics.obj_p o = true)
    (hp : s.statics.airplane_p airplane = true)
    (hl : s.statics.location_p l = true)
    (hin : s.dynamic.in_p o airplane = true)
    (hpAt : s.dynamic.at_p airplane l = true) :
    GPMoveResult o l s
      ([PlanAction.unload_airplane o airplane l],
       runPlan [PlanAction.unload_airplane o airplane l] s) := by
  have hpre :
      unload_airplanePre o airplane l s :=
    ⟨homem, hpmem, hlmem, ho, hp, hl, hin, hpAt⟩
  have hvalid :
      ValidPlan [PlanAction.unload_airplane o airplane l] s := by
    change unload_airplanePre o airplane l s ∧ True
    exact ⟨hpre, trivial⟩
  refine
    ⟨hvalid, rfl,
      validPlan_preserves_wf hvalid hwf,
      runPlan_statics _ _,
      ?_, ?_, ?_⟩
  · rw [runPlan_statics]
    exact hl
  · simp only [runPlan]
    change
      (unload_airplane o airplane l s).dynamic.at_p o l = true
    exact unload_airplane_at_p_eq1 o airplane l s
  · intro x hx hxo l'
    simp only [runPlan]
    change
      (unload_airplane o airplane l s).dynamic.at_p x l' =
        s.dynamic.at_p x l'
    exact unload_airplane_at_p_ne o airplane l s hxo

lemma gpLocatePackage_correct
    (o : Obj) (s : State)
    (hwf : WellFormed s)
    (ho : s.statics.obj_p o = true) :
    let q := gpLocatePackage o s
    GPMoveResult o q.loc s (q.actions, q.state) := by
  unfold gpLocatePackage
  split
  case h_1 l hfind =>
    have hspec := gpFind_some_spec hfind
    rcases hspec with ⟨_, hp⟩
    have hp' := (gp_bool_and_eq_true _ _).1 hp
    exact gpMove_empty hwf hp'.1 hp'.2
  case h_2 hfind =>
    have hpackage :=
      wf_packageHasLocation' hwf o ho
    have hcarrier :
        ∃ v,
          (s.statics.truck_p v = true ∨
           s.statics.airplane_p v = true) ∧
          s.dynamic.in_p o v = true := by
      rcases hpackage with hat | hin
      · rcases hat with ⟨l, hl, hat⟩
        have hlmem :=
          wfStatic_validLocation' hwf.1 l hl
        have hpred :
            (s.statics.location_p l &&
             s.dynamic.at_p o l) = true :=
          (gp_bool_and_eq_true _ _).2 ⟨hl, hat⟩
        rcases gpFind_exists_some
          (xs := s.statics.objects)
          (p := fun l =>
            s.statics.location_p l &&
            s.dynamic.at_p o l)
          ⟨l, hlmem, hpred⟩ with
          ⟨x, hx⟩
        rw [hfind] at hx
        cases hx
      · exact hin
    let v := gpCarrierOf s o
    have hv := gpCarrierOf_spec s o hwf hcarrier
    let l := gpVehicleLocation s v
    have hl :=
      gpVehicleLocation_spec s v hwf hv.2.1
    by_cases ht : s.statics.truck_p v = true
    · have hmove :=
        unload_truck_move_correct o v l s hwf
          (wfStatic_validObj' hwf.1 o ho)
          hv.1 hl.1 ho ht hl.2.1 hl.2.2 hv.2.2
      simpa [v, l, ht] using hmove
    · have hp : s.statics.airplane_p v = true := by
        rcases hv.2.1 with ht' | hp
        · exact False.elim (ht ht')
        · exact hp
      have htfalse :
          s.statics.truck_p v = false := by
        cases htv : s.statics.truck_p v <;> simp_all
      have hmove :=
        unload_airplane_move_correct o v l s hwf
          (wfStatic_validObj' hwf.1 o ho)
          hv.1 hl.1 ho hp hl.2.1 hv.2.2 hl.2.2
      simpa [v, l, htfalse] using hmove

lemma gpTruckTransfer_correct
    (o src dst city : Obj) (s : State)
    (hwf : WellFormed s)
    (ho : s.statics.obj_p o = true)
    (hsrc : s.statics.location_p src = true)
    (hdst : s.statics.location_p dst = true)
    (hcity : s.statics.city_p city = true)
    (hsrcCity : s.statics.in_city_p src city = true)
    (hdstCity : s.statics.in_city_p dst city = true)
    (hoAt : s.dynamic.at_p o src = true) :
    GPMoveResult o dst s
      (gpTruckTransfer o src dst city s) := by
  by_cases hsd : src = dst
  · subst dst
    simpa [gpTruckTransfer] using
      gpMove_empty hwf hsrc hoAt
  · let truck := gpTruckInCity s city
    have htruckSpec :=
      gpTruckInCity_spec s city hwf hcity
    rcases htruckSpec with
      ⟨htmem, ht, l₀, _, _, hl₀city, htAt₀⟩
    let truckLoc := gpVehicleLocation s truck
    have htruckLocSpec :=
      gpVehicleLocation_spec s truck hwf (Or.inl ht)
    rcases htruckLocSpec with
      ⟨htlmem, htl, htAt⟩
    have hlocEq : truckLoc = l₀ :=
      wf_vehicleUnique' hwf truck truckLoc l₀
        (Or.inl ht) htAt htAt₀
    have htruckLocCity :
        s.statics.in_city_p truckLoc city = true := by
      rw [hlocEq]
      exact hl₀city
    let position :=
      if truckLoc = src then []
      else [PlanAction.drive_truck truck truckLoc src city]
    have hposition :=
      truck_position_correct
        o truck src truckLoc src city s
        hwf ho hsrc ht htmem htlmem
        (wfStatic_validLocation' hwf.1 src hsrc)
        (wfStatic_validCity' hwf.1 city hcity)
        htl hsrc hcity htruckLocCity hsrcCity
        htAt hoAt
    have hposMove :
        GPMoveResult o src s
          (position, runPlan position s) := by
      simpa [position] using hposition.1
    have htruckAtSrc :
        (runPlan position s).dynamic.at_p truck src = true := by
      simpa [position] using hposition.2
    have hposData := hposMove
    rcases hposData with
      ⟨_, _, hposWF, hposStatic, _, hposAt, _⟩
    have hpayload :=
      truck_payload_correct
        o truck src dst city (runPlan position s)
        hposWF
        (by
          rw [hposStatic]
          exact wfStatic_validObj' hwf.1 o ho)
        (by rw [hposStatic]; exact htmem)
        (by
          rw [hposStatic]
          exact wfStatic_validLocation' hwf.1 src hsrc)
        (by
          rw [hposStatic]
          exact wfStatic_validLocation' hwf.1 dst hdst)
        (by
          rw [hposStatic]
          exact wfStatic_validCity' hwf.1 city hcity)
        (by rw [hposStatic]; exact ho)
        (by rw [hposStatic]; exact ht)
        (by rw [hposStatic]; exact hsrc)
        (by rw [hposStatic]; exact hdst)
        (by rw [hposStatic]; exact hcity)
        (by rw [hposStatic]; exact hsrcCity)
        (by rw [hposStatic]; exact hdstCity)
        htruckAtSrc hposAt
    have hcomposed :=
      gpMove_compose hposMove hpayload
    simpa [gpTruckTransfer, hsd, truck, truckLoc,
      position, runPlan_append] using hcomposed

lemma gpAirTransfer_correct
    (o src dst : Obj) (s : State)
    (hwf : WellFormed s)
    (ho : s.statics.obj_p o = true)
    (hsrcAirport : s.statics.airport_p src = true)
    (hdstAirport : s.statics.airport_p dst = true)
    (hoAt : s.dynamic.at_p o src = true) :
    GPMoveResult o dst s
      (gpAirTransfer o src dst s) := by
  by_cases hsd : src = dst
  · subst dst
    have hsrcLoc :=
      wfStatic_airportsAreLocs s.statics hwf.1 src
        hsrcAirport
    simpa [gpAirTransfer] using
      gpMove_empty hwf hsrcLoc hoAt
  · let airplane := gpAirplane s
    have hairplaneSpec := gpAirplane_spec s hwf
    rcases hairplaneSpec with ⟨hpmem, hp⟩
    let airplaneLoc := gpVehicleLocation s airplane
    have hairplaneLocSpec :=
      gpVehicleLocation_spec s airplane hwf (Or.inr hp)
    rcases hairplaneLocSpec with
      ⟨hplmem, _, hpAt⟩
    have hplAirport :
        s.statics.airport_p airplaneLoc = true :=
      wf_airplanesAtAirports' hwf
        airplane airplaneLoc hp hpAt
    let position :=
      if airplaneLoc = src then []
      else [PlanAction.fly_airplane airplane airplaneLoc src]
    have hposition :=
      airplane_position_correct
        o airplane src airplaneLoc src s
        hwf ho
        (wfStatic_airportsAreLocs s.statics hwf.1
          src hsrcAirport)
        hp hpmem hplmem
        (wfStatic_validLocation' hwf.1 src
          (wfStatic_airportsAreLocs s.statics hwf.1
            src hsrcAirport))
        hplAirport hsrcAirport hpAt hoAt
    have hposMove :
        GPMoveResult o src s
          (position, runPlan position s) := by
      simpa [position] using hposition.1
    have hpAtSrc :
        (runPlan position s).dynamic.at_p airplane src = true := by
      simpa [position] using hposition.2
    have hposData := hposMove
    rcases hposData with
      ⟨_, _, hposWF, hposStatic, _, hposAt, _⟩
    have hpayload :=
      air_payload_correct
        o airplane src dst (runPlan position s)
        hposWF
        (by
          rw [hposStatic]
          exact wfStatic_validObj' hwf.1 o ho)
        (by rw [hposStatic]; exact hpmem)
        (by
          rw [hposStatic]
          exact wfStatic_validLocation' hwf.1 src
            (wfStatic_airportsAreLocs s.statics hwf.1
              src hsrcAirport))
        (by
          rw [hposStatic]
          exact wfStatic_validLocation' hwf.1 dst
            (wfStatic_airportsAreLocs s.statics hwf.1
              dst hdstAirport))
        (by rw [hposStatic]; exact ho)
        (by rw [hposStatic]; exact hp)
        (by rw [hposStatic]; exact hsrcAirport)
        (by rw [hposStatic]; exact hdstAirport)
        hposAt hpAtSrc
    have hcomposed :=
      gpMove_compose hposMove hpayload
    simpa [gpAirTransfer, hsd, airplane, airplaneLoc,
      position, runPlan_append] using hcomposed

lemma gpDeliverPackage_correct
    (o : Obj) (s : State) (g : Goal)
    (hwf : WellFormed s)
    (hgoal : GPGoalSpec s.statics g)
    (ho : s.statics.obj_p o = true) :
    GPMoveResult o (gpGoalTarget s g o) s
      (gpDeliverPackage o s g) := by
  let q := gpLocatePackage o s
  have hloc :
      GPMoveResult o q.loc s (q.actions, q.state) := by
    simpa [q] using gpLocatePackage_correct o s hwf ho
  have hlocData := hloc
  rcases hlocData with
    ⟨_, _, hqWF, hqStatic, hqLoc, hqAt, _⟩
  have hgoalq : GPGoalSpec q.state.statics g := by
    rw [hqStatic]
    exact hgoal
  let dst := gpGoalTarget q.state g o
  have hdstSpec :=
    gpGoalTarget_spec q.state g o hqWF.1 hgoalq
      (by rw [hqStatic]; exact ho)
  have hdstEq :
      dst = gpGoalTarget s g o := by
    unfold dst gpGoalTarget
    rw [hqStatic]
  by_cases hsrcDst : q.loc = dst
  · have hc :
        GPMoveResult o dst s
          (gpDeliverPackage o s g) := by
      simpa [gpDeliverPackage, q, dst, hsrcDst] using hloc
    rw [hdstEq] at hc
    exact hc
  · let srcCity := gpCityOfLocation q.state q.loc
    let dstCity := gpCityOfLocation q.state dst
    have hsrcCitySpec :=
      gpCityOfLocation_spec q.state q.loc hqWF hqLoc
    have hdstCitySpec :=
      gpCityOfLocation_spec q.state dst hqWF hdstSpec.2.1
    by_cases hsameCity : srcCity = dstCity
    · have htransfer :=
        gpTruckTransfer_correct
          o q.loc dst srcCity q.state
          hqWF
          (by rw [hqStatic]; exact ho)
          hqLoc hdstSpec.2.1
          hsrcCitySpec.2.1
          hsrcCitySpec.2.2
          (by
            rw [hsameCity]
            exact hdstCitySpec.2.2)
          hqAt
      have hcombined :=
        gpMove_compose hloc htransfer
      have hc :
          GPMoveResult o dst s
            (gpDeliverPackage o s g) := by
        simpa [gpDeliverPackage, q, dst,
          srcCity, dstCity, hsrcDst, hsameCity,
          runPlan_append, List.append_assoc] using hcombined
      rw [hdstEq] at hc
      exact hc
    · let srcAirport :=
        gpAirportInCity q.state srcCity
      let dstAirport :=
        gpAirportInCity q.state dstCity
      have hsrcAirportSpec :=
        gpAirportInCity_spec q.state srcCity hqWF
          hsrcCitySpec.2.1
      have hdstAirportSpec :=
        gpAirportInCity_spec q.state dstCity hqWF
          hdstCitySpec.2.1
      let originPair : List PlanAction × State :=
        if q.loc = srcAirport then
          ([], q.state)
        else
          gpTruckTransfer
            o q.loc srcAirport srcCity q.state
      have hOrigin :
          GPMoveResult o srcAirport q.state originPair := by
        by_cases hEq : q.loc = srcAirport
        · have hempty :
              GPMoveResult o srcAirport q.state
                ([], q.state) :=
            gpMove_empty hqWF
              (by rw [← hEq]; exact hqLoc)
              (by rw [← hEq]; exact hqAt)
          simpa [originPair, hEq] using hempty
        · have hm :=
            gpTruckTransfer_correct
              o q.loc srcAirport srcCity q.state
              hqWF
              (by rw [hqStatic]; exact ho)
              hqLoc hsrcAirportSpec.2.1
              hsrcCitySpec.2.1
              hsrcCitySpec.2.2
              hsrcAirportSpec.2.2.2
              hqAt
          simpa [originPair, hEq] using hm
      let airPair :=
        gpAirTransfer o srcAirport dstAirport originPair.2
      have hOriginData := hOrigin
      rcases hOriginData with
        ⟨_, _, hOriginWF, hOriginStatic,
          _, hOriginAt, _⟩
      have hAir :
          GPMoveResult o dstAirport originPair.2 airPair := by
        unfold airPair
        apply gpAirTransfer_correct
        · exact hOriginWF
        · rw [hOriginStatic, hqStatic]
          exact ho
        · rw [hOriginStatic]
          exact hsrcAirportSpec.2.2.1
        · rw [hOriginStatic]
          exact hdstAirportSpec.2.2.1
        · exact hOriginAt
      let destinationPair : List PlanAction × State :=
        if dst = dstAirport then
          ([], airPair.2)
        else
          gpTruckTransfer
            o dstAirport dst dstCity airPair.2
      have hAirData := hAir
      rcases hAirData with
        ⟨_, _, hAirWF, hAirStatic, _, hAirAt, _⟩
      have hDestination :
          GPMoveResult o dst airPair.2 destinationPair := by
        by_cases hEq : dst = dstAirport
        · have hempty :
              GPMoveResult o dst airPair.2
                ([], airPair.2) :=
            gpMove_empty hAirWF
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstSpec.2.1)
              (by
                rw [hEq]
                exact hAirAt)
          simpa [destinationPair, hEq] using hempty
        · have hm :=
            gpTruckTransfer_correct
              o dstAirport dst dstCity airPair.2
              hAirWF
              (by
                rw [hAirStatic, hOriginStatic, hqStatic]
                exact ho)
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstAirportSpec.2.1)
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstSpec.2.1)
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstCitySpec.2.1)
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstAirportSpec.2.2.2)
              (by
                rw [hAirStatic, hOriginStatic]
                exact hdstCitySpec.2.2)
              hAirAt
          simpa [destinationPair, hEq] using hm
      have h₁ := gpMove_compose hloc hOrigin
      have h₂ := gpMove_compose h₁ hAir
      have h₃ := gpMove_compose h₂ hDestination
      have hc :
          GPMoveResult o dst s
            (gpDeliverPackage o s g) := by
        simpa [gpDeliverPackage, q, dst,
          srcCity, dstCity, srcAirport, dstAirport,
          originPair, airPair, destinationPair,
          hsrcDst, hsameCity, runPlan_append,
          List.append_assoc] using h₃
      rw [hdstEq] at hc
      exact hc

def PackageGoalSatisfied
    (s : State) (g : Goal) (o : Obj) : Prop :=
  ∀ l, g.dynamic.at_p o l = some true →
    s.dynamic.at_p o l = true

lemma gpDeliverPackage_goal
    (o : Obj) (s : State) (g : Goal)
    (hwf : WellFormed s)
    (hgoal : GPGoalSpec s.statics g)
    (ho : s.statics.obj_p o = true) :
    let r := gpDeliverPackage o s g
    ValidPlan r.1 s ∧
    r.2 = runPlan r.1 s ∧
    WellFormed r.2 ∧
    r.2.statics = s.statics ∧
    PackageGoalSatisfied r.2 g o ∧
    ∀ x, s.statics.obj_p x = true → x ≠ o →
      ∀ l, r.2.dynamic.at_p x l =
        s.dynamic.at_p x l := by
  let r := gpDeliverPackage o s g
  have hmove :=
    gpDeliverPackage_correct o s g hwf hgoal ho
  rcases hmove with
    ⟨hvalid, hr, hwf', hstatic,
      _, hat, hpres⟩
  have htarget :=
    gpGoalTarget_spec s g o hwf.1 hgoal ho
  refine
    ⟨hvalid, hr, hwf', hstatic, ?_, hpres⟩
  intro l hl
  have heq := htarget.2.2.2 l hl
  subst l
  exact hat

lemma gpSolveObjects_correct
    (xs : List Obj) (s : State) (g : Goal)
    (hwf : WellFormed s)
    (hgoal : GPGoalSpec s.statics g)
    (hnodup : xs.Nodup) :
    let plan := gpSolveObjects xs s g
    ValidPlan plan s ∧
    WellFormed (runPlan plan s) ∧
    (runPlan plan s).statics = s.statics ∧
    (∀ o, s.statics.obj_p o = true → o ∈ xs →
      PackageGoalSatisfied (runPlan plan s) g o) ∧
    (∀ o, s.statics.obj_p o = true → o ∉ xs →
      ∀ l,
        (runPlan plan s).dynamic.at_p o l =
          s.dynamic.at_p o l) := by
  induction xs generalizing s with
  | nil =>
      simp [gpSolveObjects, ValidPlan, runPlan,
        PackageGoalSatisfied, hwf]
  | cons o rest ih =>
      have hnodupParts := List.nodup_cons.mp hnodup
      have hoNotMem : o ∉ rest := hnodupParts.1
      have hrestNodup : rest.Nodup := hnodupParts.2
      by_cases ho : s.statics.obj_p o = true
      · let r := gpDeliverPackage o s g
        have hdeliver :=
          gpDeliverPackage_goal o s g hwf hgoal ho
        rcases hdeliver with
          ⟨hvalidD, hr, hwfD, hstaticD,
            hgoalO, hpresD⟩
        have hgoalD :
            GPGoalSpec r.2.statics g := by
          rw [hstaticD]
          exact hgoal
        have hrec :=
          ih r.2 hwfD hgoalD hrestNodup
        rcases hrec with
          ⟨hvalidR, hwfR, hstaticR,
            hgoalsR, hpresR⟩
        have hplan :
            gpSolveObjects (o :: rest) s g =
              r.1 ++ gpSolveObjects rest r.2 g := by
          simp [gpSolveObjects, ho, r]
        rw [hplan]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · exact
            (validPlan_append
              r.1 (gpSolveObjects rest r.2 g) s).2
              ⟨hvalidD, by
                rw [← hr]
                exact hvalidR⟩
        · rw [runPlan_append, ← hr]
          exact hwfR
        · rw [runPlan_append, ← hr]
          exact hstaticR.trans hstaticD
        · intro x hx hxmem
          have hx' :
              r.2.statics.obj_p x = true := by
            rw [hstaticD]
            exact hx
          rcases List.mem_cons.mp hxmem with hxo | hxrest
          · subst x
            intro l hl
            rw [runPlan_append, ← hr]
            have hpresHead :=
              hpresR o hx' hoNotMem l
            rw [hpresHead]
            exact hgoalO l hl
          · rw [runPlan_append, ← hr]
            exact hgoalsR x hx' hxrest
        · intro x hx hxnot l
          have hxne : x ≠ o := by
            intro hEq
            subst x
            exact hxnot (by simp)
          have hxnotRest : x ∉ rest := by
            intro hxmem
            exact hxnot (by simp [hxmem])
          have hx' :
              r.2.statics.obj_p x = true := by
            rw [hstaticD]
            exact hx
          rw [runPlan_append, ← hr]
          exact
            (hpresR x hx' hxnotRest l).trans
              (hpresD x hx hxne l)
      · have hrec :=
          ih s hwf hgoal hrestNodup
        rcases hrec with
          ⟨hvalidR, hwfR, hstaticR,
            hgoalsR, hpresR⟩
        simp only [gpSolveObjects, ho, if_false]
        refine
          ⟨hvalidR, hwfR, hstaticR, ?_, ?_⟩
        · intro x hx hxmem
          rcases List.mem_cons.mp hxmem with hEq | hxrest
          · subst x
            exact False.elim (ho hx)
          · exact hgoalsR x hx hxrest
        · intro x hx hxnot
          apply hpresR x hx
          intro hxrest
          exact hxnot (by simp [hxrest])

lemma satisfiesGoal_of_packageGoals
    (s : State) (g : Goal)
    (hgoal : GPGoalSpec s.statics g)
    (hpackages :
      ∀ o, s.statics.obj_p o = true →
        PackageGoalSatisfied s g o) :
    SatisfiesGoal s g := by
  rcases hgoal with
    ⟨hValidAt, _, hIgnoreVehicle,
      hPositive, hIgnoreIn⟩
  constructor
  · intro o l
    cases hopt : g.dynamic.at_p o l with
    | none =>
        simp [hopt]
    | some b =>
        cases b with
        | false =>
            exact False.elim (hPositive o l hopt)
        | true =>
            simp only [hopt]
            have htruth :
                Truthy.isTrue (g.dynamic.at_p o l) := by
              change g.dynamic.at_p o l = some true
              exact hopt
            rcases hValidAt o l htruth with
              ⟨_, _, _, htype⟩
            rcases htype with ht | hp | ho
            · have hnone :=
                hIgnoreVehicle o l (Or.inl ht)
              rw [hopt] at hnone
              cases hnone
            · have hnone :=
                hIgnoreVehicle o l (Or.inr hp)
              rw [hopt] at hnone
              cases hnone
            · exact hpackages o ho l hopt
  · intro o v
    have hnone := hIgnoreIn o v
    simp [hnone]

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
  have hgoalSpec :
      GPGoalSpec s.statics g :=
    gpGoalSpec_of_wellFormedGoal hgoal
  have hnodup : s.statics.objects.Nodup :=
    hstatic.1
  have hsolve :=
    gpSolveObjects_correct
      s.statics.objects s g hwf hgoalSpec hnodup
  rcases hsolve with
    ⟨hvalid, _, hstaticFinal,
      hpackages, _⟩
  constructor
  · simpa [solve] using hvalid
  · have hstaticFinal' :
        (runPlan (solve s g) s).statics =
          s.statics := by
      simpa [solve] using hstaticFinal
    have hgoalFinal :
        GPGoalSpec (runPlan (solve s g) s).statics g := by
      rw [hstaticFinal']
      exact hgoalSpec
    apply satisfiesGoal_of_packageGoals
      (runPlan (solve s g) s) g hgoalFinal
    intro o hoFinal
    have ho : s.statics.obj_p o = true := by
      rw [hstaticFinal'] at hoFinal
      exact hoFinal
    have homem :
        o ∈ s.statics.objects :=
      wfStatic_validObj' hstatic o ho
    simpa [solve] using hpackages o ho homem

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

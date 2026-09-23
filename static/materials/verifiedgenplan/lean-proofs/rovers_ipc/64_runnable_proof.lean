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
  at_lander_p : Obj → Obj → Bool
  can_traverse_p : Obj → Obj → Obj → Bool
  equipped_for_soil_analysis_p : Obj → Bool
  equipped_for_rock_analysis_p : Obj → Bool
  equipped_for_imaging_p : Obj → Bool
  supports_p : Obj → Obj → Bool
  visible_p : Obj → Obj → Bool
  visible_from_p : Obj → Obj → Bool
  store_of_p : Obj → Obj → Bool
  calibration_target_p : Obj → Obj → Bool
  on_board_p : Obj → Obj → Bool
  rover_t : Obj → Bool
  waypoint_t : Obj → Bool
  store_t : Obj → Bool
  camera_t : Obj → Bool
  mode_t : Obj → Bool
  lander_t : Obj → Bool
  objective_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_p : Obj → Obj → α
  empty_p : Obj → α
  have_rock_analysis_p : Obj → Obj → α
  have_soil_analysis_p : Obj → Obj → α
  full_p : Obj → α
  calibrated_p : Obj → Obj → α
  have_image_p : Obj → Obj → Obj → α
  communicated_soil_data_p : Obj → α
  communicated_rock_data_p : Obj → α
  communicated_image_data_p : Obj → Obj → α
  at_soil_sample_p : Obj → α
  at_rock_sample_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidAtLanderParam (s : StaticState) : Prop :=
  ∀ var_x var_y, s.at_lander_p var_x var_y = true → s.lander_t var_x = true ∧ s.waypoint_t var_y = true

def ValidCanTraverseParam (s : StaticState) : Prop :=
  ∀ var_r var_x var_y, s.can_traverse_p var_r var_x var_y = true → s.rover_t var_r = true ∧ s.waypoint_t var_x = true ∧ s.waypoint_t var_y = true

def ValidEquippedForSoilAnalysisParam (s : StaticState) : Prop :=
  ∀ var_r, s.equipped_for_soil_analysis_p var_r = true → s.rover_t var_r = true

def ValidEquippedForRockAnalysisParam (s : StaticState) : Prop :=
  ∀ var_r, s.equipped_for_rock_analysis_p var_r = true → s.rover_t var_r = true

def ValidEquippedForImagingParam (s : StaticState) : Prop :=
  ∀ var_r, s.equipped_for_imaging_p var_r = true → s.rover_t var_r = true

def ValidSupportsParam (s : StaticState) : Prop :=
  ∀ var_c var_m, s.supports_p var_c var_m = true → s.camera_t var_c = true ∧ s.mode_t var_m = true

def ValidVisibleParam (s : StaticState) : Prop :=
  ∀ var_w var_p, s.visible_p var_w var_p = true → s.waypoint_t var_w = true ∧ s.waypoint_t var_p = true

def ValidVisibleFromParam (s : StaticState) : Prop :=
  ∀ var_o var_w, s.visible_from_p var_o var_w = true → s.objective_t var_o = true ∧ s.waypoint_t var_w = true

def ValidStoreOfParam (s : StaticState) : Prop :=
  ∀ var_s var_r, s.store_of_p var_s var_r = true → s.store_t var_s = true ∧ s.rover_t var_r = true

def ValidCalibrationTargetParam (s : StaticState) : Prop :=
  ∀ var_i var_o, s.calibration_target_p var_i var_o = true → s.camera_t var_i = true ∧ s.objective_t var_o = true

def ValidOnBoardParam (s : StaticState) : Prop :=
  ∀ var_i var_r, s.on_board_p var_i var_r = true → s.camera_t var_i = true ∧ s.rover_t var_r = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.rover_t x = true → x ∈ s.objects) ∧
  (∀ x, s.waypoint_t x = true → x ∈ s.objects) ∧
  (∀ x, s.store_t x = true → x ∈ s.objects) ∧
  (∀ x, s.camera_t x = true → x ∈ s.objects) ∧
  (∀ x, s.mode_t x = true → x ∈ s.objects) ∧
  (∀ x, s.lander_t x = true → x ∈ s.objects) ∧
  (∀ x, s.objective_t x = true → x ∈ s.objects) ∧
  (∀ x, s.rover_t x = true → s.waypoint_t x = false) ∧
  (∀ x, s.rover_t x = true → s.store_t x = false) ∧
  (∀ x, s.rover_t x = true → s.camera_t x = false) ∧
  (∀ x, s.rover_t x = true → s.mode_t x = false) ∧
  (∀ x, s.rover_t x = true → s.lander_t x = false) ∧
  (∀ x, s.rover_t x = true → s.objective_t x = false) ∧
  (∀ x, s.waypoint_t x = true → s.store_t x = false) ∧
  (∀ x, s.waypoint_t x = true → s.camera_t x = false) ∧
  (∀ x, s.waypoint_t x = true → s.mode_t x = false) ∧
  (∀ x, s.waypoint_t x = true → s.lander_t x = false) ∧
  (∀ x, s.waypoint_t x = true → s.objective_t x = false) ∧
  (∀ x, s.store_t x = true → s.camera_t x = false) ∧
  (∀ x, s.store_t x = true → s.mode_t x = false) ∧
  (∀ x, s.store_t x = true → s.lander_t x = false) ∧
  (∀ x, s.store_t x = true → s.objective_t x = false) ∧
  (∀ x, s.camera_t x = true → s.mode_t x = false) ∧
  (∀ x, s.camera_t x = true → s.lander_t x = false) ∧
  (∀ x, s.camera_t x = true → s.objective_t x = false) ∧
  (∀ x, s.mode_t x = true → s.lander_t x = false) ∧
  (∀ x, s.mode_t x = true → s.objective_t x = false) ∧
  (∀ x, s.lander_t x = true → s.objective_t x = false)

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects →
    (s.rover_t x = true ∨ s.waypoint_t x = true ∨ s.store_t x = true ∨ s.camera_t x = true ∨
     s.mode_t x = true ∨ s.lander_t x = true ∨ s.objective_t x = true)

def MinObj (s : StaticState) : Prop :=
  (∃ r, s.rover_t r = true) ∧
  (∃ w1 w2, s.waypoint_t w1 = true ∧ s.waypoint_t w2 = true ∧ w1 ≠ w2) ∧
  (∃ c, s.camera_t c = true) ∧
  (∃ o, s.objective_t o = true) ∧
  (∃ m, s.mode_t m = true)

def UniqueLander (s : StaticState) : Prop :=
  ∃! l, s.lander_t l = true

def StoreOfFunctional (s : StaticState) : Prop :=
  ∀ st r1 r2, s.store_of_p st r1 = true → s.store_of_p st r2 = true → r1 = r2

def StoreOfInjective (s : StaticState) : Prop :=
  ∀ st1 st2 r, s.store_of_p st1 r = true → s.store_of_p st2 r = true → st1 = st2

def RoverHasStore (s : StaticState) : Prop :=
  ∀ r, s.rover_t r = true → ∃ st, s.store_of_p st r = true

def StoreHasRover (s : StaticState) : Prop :=
  ∀ st, s.store_t st = true → ∃ r, s.store_of_p st r = true

def AtLanderFunctional (s : StaticState) : Prop :=
  ∀ l w1 w2, s.at_lander_p l w1 = true → s.at_lander_p l w2 = true → w1 = w2

def LanderHasLocation (s : StaticState) : Prop :=
  ∀ l, s.lander_t l = true → ∃ w, s.at_lander_p l w = true

def CameraHasCalibrationTarget (s : StaticState) : Prop :=
  ∀ c, s.camera_t c = true → ∃ o, s.calibration_target_p c o = true

def CameraOnBoardImagingRover (s : StaticState) : Prop :=
  ∀ c, s.camera_t c = true → ∃ r, s.on_board_p c r = true ∧ s.equipped_for_imaging_p r = true

def CalibrationTargetFunctional (s : StaticState) : Prop :=
  ∀ c o1 o2, s.calibration_target_p c o1 = true → s.calibration_target_p c o2 = true → o1 = o2

def OnBoardFunctional (s : StaticState) : Prop :=
  ∀ c r1 r2, s.on_board_p c r1 = true → s.on_board_p c r2 = true → r1 = r2

def CameraSupportsSomeMode (s : StaticState) : Prop :=
  ∀ c, s.camera_t c = true → ∃ m, s.supports_p c m = true

def ModeSupportedBySomeCamera (s : StaticState) : Prop :=
  ∀ m, s.mode_t m = true → ∃ c, s.supports_p c m = true

def VisibleSymmetric (s : StaticState) : Prop :=
  ∀ w1 w2, s.visible_p w1 w2 = true → s.visible_p w2 w1 = true

def CanTraverseSymmetric (s : StaticState) : Prop :=
  ∀ r w1 w2, s.can_traverse_p r w1 w2 = true → s.can_traverse_p r w2 w1 = true

def VisibleConnected (s : StaticState) : Prop :=
  ∀ w1 w2, s.waypoint_t w1 = true → s.waypoint_t w2 = true →
    Relation.ReflTransGen (fun a b => s.visible_p a b = true) w1 w2

def CanTraverseConnected (s : StaticState) : Prop :=
  ∀ r, s.rover_t r = true → ∀ w1 w2, s.waypoint_t w1 = true → s.waypoint_t w2 = true →
    Relation.ReflTransGen (fun a b => s.can_traverse_p r a b = true) w1 w2

def ObjectiveVisibleFromSomewhere (s : StaticState) : Prop :=
  ∀ o, s.objective_t o = true → ∃ w, s.visible_from_p o w = true

def NavigableConnected (s : StaticState) : Prop :=
  ∀ r, s.rover_t r = true → ∀ w1 w2, s.waypoint_t w1 = true → s.waypoint_t w2 = true →
    Relation.ReflTransGen (fun a b => s.can_traverse_p r a b = true ∧ s.visible_p a b = true) w1 w2

def WellFormedStatic (s : StaticState) : Prop :=
  ObjectsUnique s ∧
  ValidAtLanderParam s ∧
  ValidCanTraverseParam s ∧
  ValidEquippedForSoilAnalysisParam s ∧
  ValidEquippedForRockAnalysisParam s ∧
  ValidEquippedForImagingParam s ∧
  ValidSupportsParam s ∧
  ValidVisibleParam s ∧
  ValidVisibleFromParam s ∧
  ValidStoreOfParam s ∧
  ValidCalibrationTargetParam s ∧
  ValidOnBoardParam s ∧
  ValidTypeHierarchy s ∧
  TypeCoverage s ∧
  MinObj s ∧
  UniqueLander s ∧
  StoreOfFunctional s ∧
  StoreOfInjective s ∧
  RoverHasStore s ∧
  StoreHasRover s ∧
  AtLanderFunctional s ∧
  LanderHasLocation s ∧
  CameraHasCalibrationTarget s ∧
  CameraOnBoardImagingRover s ∧
  CalibrationTargetFunctional s ∧
  OnBoardFunctional s ∧
  CameraSupportsSomeMode s ∧
  ModeSupportedBySomeCamera s ∧
  VisibleSymmetric s ∧
  CanTraverseSymmetric s ∧
  VisibleConnected s ∧
  CanTraverseConnected s ∧
  ObjectiveVisibleFromSomewhere s ∧
  NavigableConnected s

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_x var_y, Truthy.isTrue (d.at_p var_x var_y) → s.rover_t var_x = true ∧ s.waypoint_t var_y = true

def ValidEmptyParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_s, Truthy.isTrue (d.empty_p var_s) → s.store_t var_s = true

def ValidHaveRockAnalysisParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_w, Truthy.isTrue (d.have_rock_analysis_p var_r var_w) → s.rover_t var_r = true ∧ s.waypoint_t var_w = true

def ValidHaveSoilAnalysisParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_w, Truthy.isTrue (d.have_soil_analysis_p var_r var_w) → s.rover_t var_r = true ∧ s.waypoint_t var_w = true

def ValidFullParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_s, Truthy.isTrue (d.full_p var_s) → s.store_t var_s = true

def ValidCalibratedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_c var_r, Truthy.isTrue (d.calibrated_p var_c var_r) → s.camera_t var_c = true ∧ s.rover_t var_r = true

def ValidHaveImageParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_r var_o var_m, Truthy.isTrue (d.have_image_p var_r var_o var_m) → s.rover_t var_r = true ∧ s.objective_t var_o = true ∧ s.mode_t var_m = true

def ValidCommunicatedSoilDataParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_w, Truthy.isTrue (d.communicated_soil_data_p var_w) → s.waypoint_t var_w = true

def ValidCommunicatedRockDataParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_w, Truthy.isTrue (d.communicated_rock_data_p var_w) → s.waypoint_t var_w = true

def ValidCommunicatedImageDataParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_o var_m, Truthy.isTrue (d.communicated_image_data_p var_o var_m) → s.objective_t var_o = true ∧ s.mode_t var_m = true

def ValidAtSoilSampleParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_w, Truthy.isTrue (d.at_soil_sample_p var_w) → s.waypoint_t var_w = true

def ValidAtRockSampleParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_w, Truthy.isTrue (d.at_rock_sample_p var_w) → s.waypoint_t var_w = true

def AtMostOneLocation {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r w1 w2, Truthy.isTrue (d.at_p r w1) → Truthy.isTrue (d.at_p r w2) → w1 = w2

def EmptyFullExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ st, ¬ (Truthy.isTrue (d.empty_p st) ∧ Truthy.isTrue (d.full_p st))

def HaveSoilAnalysisImpliesNotAtSoilSample {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r p, Truthy.isTrue (d.have_soil_analysis_p r p) → ¬ Truthy.isTrue (d.at_soil_sample_p p)

def HaveRockAnalysisImpliesNotAtRockSample {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r p, Truthy.isTrue (d.have_rock_analysis_p r p) → ¬ Truthy.isTrue (d.at_rock_sample_p p)

def CalibratedImpliesOnBoardAndEquipped {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ c r, Truthy.isTrue (d.calibrated_p c r) → s.on_board_p c r = true ∧ s.equipped_for_imaging_p r = true

def HaveImageImpliesEquippedForImaging {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r o m, Truthy.isTrue (d.have_image_p r o m) → s.equipped_for_imaging_p r = true

def HaveSoilAnalysisImpliesEquipped {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r p, Truthy.isTrue (d.have_soil_analysis_p r p) → s.equipped_for_soil_analysis_p r = true

def HaveRockAnalysisImpliesEquipped {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ r p, Truthy.isTrue (d.have_rock_analysis_p r p) → s.equipped_for_rock_analysis_p r = true

def RoverHasLocation (s : State) : Prop :=
  ∀ r, s.statics.rover_t r = true → ∃ w, s.dynamic.at_p r w = true

def StoreEmptyOrFull (s : State) : Prop :=
  ∀ st, s.statics.store_t st = true → s.dynamic.empty_p st = true ∨ s.dynamic.full_p st = true

def CommunicatedSoilImpliesHaveSoilAnalysis (s : State) : Prop :=
  ∀ p, Truthy.isTrue (s.dynamic.communicated_soil_data_p p) → ∃ r, Truthy.isTrue (s.dynamic.have_soil_analysis_p r p)

def CommunicatedRockImpliesHaveRockAnalysis (s : State) : Prop :=
  ∀ p, Truthy.isTrue (s.dynamic.communicated_rock_data_p p) → ∃ r, Truthy.isTrue (s.dynamic.have_rock_analysis_p r p)

def CommunicatedImageImpliesHaveImage (s : State) : Prop :=
  ∀ o m, Truthy.isTrue (s.dynamic.communicated_image_data_p o m) → ∃ r, Truthy.isTrue (s.dynamic.have_image_p r o m)

def WellFormed (s : State) : Prop :=
  WellFormedStatic s.statics ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidEmptyParam s.statics s.dynamic ∧
  ValidHaveRockAnalysisParam s.statics s.dynamic ∧
  ValidHaveSoilAnalysisParam s.statics s.dynamic ∧
  ValidFullParam s.statics s.dynamic ∧
  ValidCalibratedParam s.statics s.dynamic ∧
  ValidHaveImageParam s.statics s.dynamic ∧
  ValidCommunicatedSoilDataParam s.statics s.dynamic ∧
  ValidCommunicatedRockDataParam s.statics s.dynamic ∧
  ValidCommunicatedImageDataParam s.statics s.dynamic ∧
  ValidAtSoilSampleParam s.statics s.dynamic ∧
  ValidAtRockSampleParam s.statics s.dynamic ∧
  AtMostOneLocation s.statics s.dynamic ∧
  EmptyFullExclusive s.statics s.dynamic ∧
  HaveSoilAnalysisImpliesNotAtSoilSample s.statics s.dynamic ∧
  HaveRockAnalysisImpliesNotAtRockSample s.statics s.dynamic ∧
  CalibratedImpliesOnBoardAndEquipped s.statics s.dynamic ∧
  HaveImageImpliesEquippedForImaging s.statics s.dynamic ∧
  HaveSoilAnalysisImpliesEquipped s.statics s.dynamic ∧
  HaveRockAnalysisImpliesEquipped s.statics s.dynamic ∧
  RoverHasLocation s ∧
  StoreEmptyOrFull s ∧
  CommunicatedSoilImpliesHaveSoilAnalysis s ∧
  CommunicatedRockImpliesHaveRockAnalysis s ∧
  CommunicatedImageImpliesHaveImage s

def InitAllStoresEmpty (s : State) : Prop :=
  ∀ st, s.statics.store_t st = true → s.dynamic.empty_p st = true

def InitNothingCommunicated (s : State) : Prop :=
  (∀ w, s.dynamic.communicated_soil_data_p w = false) ∧
  (∀ w, s.dynamic.communicated_rock_data_p w = false) ∧
  (∀ o m, s.dynamic.communicated_image_data_p o m = false)

def InitNoHaveSoilAnalysis (s : State) : Prop :=
  ∀ r p, s.dynamic.have_soil_analysis_p r p = false

def InitNoHaveRockAnalysis (s : State) : Prop :=
  ∀ r p, s.dynamic.have_rock_analysis_p r p = false

def InitNoCalibrated (s : State) : Prop :=
  ∀ c r, s.dynamic.calibrated_p c r = false

def InitNoHaveImage (s : State) : Prop :=
  ∀ r o m, s.dynamic.have_image_p r o m = false

def WellFormedInit (s : State) : Prop :=
  WellFormed s ∧
  InitAllStoresEmpty s ∧
  InitNothingCommunicated s ∧
  InitNoHaveSoilAnalysis s ∧
  InitNoHaveRockAnalysis s ∧
  InitNoCalibrated s ∧
  InitNoHaveImage s

def GoalIgnoreAt (initial : State) (g : Goal) : Prop :=
  ∀ r w, g.dynamic.at_p r w = none

def GoalIgnoreEmpty (initial : State) (g : Goal) : Prop :=
  ∀ st, g.dynamic.empty_p st = none

def GoalIgnoreFull (initial : State) (g : Goal) : Prop :=
  ∀ st, g.dynamic.full_p st = none

def GoalIgnoreHaveRockAnalysis (initial : State) (g : Goal) : Prop :=
  ∀ r w, g.dynamic.have_rock_analysis_p r w = none

def GoalIgnoreHaveSoilAnalysis (initial : State) (g : Goal) : Prop :=
  ∀ r w, g.dynamic.have_soil_analysis_p r w = none

def GoalIgnoreCalibrated (initial : State) (g : Goal) : Prop :=
  ∀ c r, g.dynamic.calibrated_p c r = none

def GoalIgnoreHaveImage (initial : State) (g : Goal) : Prop :=
  ∀ r o m, g.dynamic.have_image_p r o m = none

def GoalIgnoreAtSoilSample (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.at_soil_sample_p w = none

def GoalIgnoreAtRockSample (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.at_rock_sample_p w = none

def GoalCommunicatedSoilOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.communicated_soil_data_p w ≠ some false

def GoalCommunicatedRockOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.communicated_rock_data_p w ≠ some false

def GoalCommunicatedImageOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ o m, g.dynamic.communicated_image_data_p o m ≠ some false

def GoalCommunicatedSoilOnlySolvable (initial : State) (g : Goal) : Prop :=
  (∃ w, g.dynamic.communicated_soil_data_p w = some true) → ∃ r, initial.statics.equipped_for_soil_analysis_p r = true

def GoalCommunicatedRockOnlySolvable (initial : State) (g : Goal) : Prop :=
  (∃ w, g.dynamic.communicated_rock_data_p w = some true) → ∃ r, initial.statics.equipped_for_rock_analysis_p r = true

def GoalCommunicatedImageOnlySolvable (initial : State) (g : Goal) : Prop :=
  (∃ o m, g.dynamic.communicated_image_data_p o m = some true) → ∃ r, initial.statics.equipped_for_imaging_p r = true

def GoalCommunicatedSoilImpliesSampleAtWaypoint (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.communicated_soil_data_p w = some true → initial.dynamic.at_soil_sample_p w = true

def GoalCommunicatedRockImpliesSampleAtWaypoint (initial : State) (g : Goal) : Prop :=
  ∀ w, g.dynamic.communicated_rock_data_p w = some true → initial.dynamic.at_rock_sample_p w = true

def WellFormedGoal (initial : State) (g : Goal) : Prop :=
  WellFormedStatic initial.statics ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidEmptyParam initial.statics g.dynamic ∧
  ValidHaveRockAnalysisParam initial.statics g.dynamic ∧
  ValidHaveSoilAnalysisParam initial.statics g.dynamic ∧
  ValidFullParam initial.statics g.dynamic ∧
  ValidCalibratedParam initial.statics g.dynamic ∧
  ValidHaveImageParam initial.statics g.dynamic ∧
  ValidCommunicatedSoilDataParam initial.statics g.dynamic ∧
  ValidCommunicatedRockDataParam initial.statics g.dynamic ∧
  ValidCommunicatedImageDataParam initial.statics g.dynamic ∧
  ValidAtSoilSampleParam initial.statics g.dynamic ∧
  ValidAtRockSampleParam initial.statics g.dynamic ∧
  AtMostOneLocation initial.statics g.dynamic ∧
  EmptyFullExclusive initial.statics g.dynamic ∧
  HaveSoilAnalysisImpliesNotAtSoilSample initial.statics g.dynamic ∧
  HaveRockAnalysisImpliesNotAtRockSample initial.statics g.dynamic ∧
  CalibratedImpliesOnBoardAndEquipped initial.statics g.dynamic ∧
  HaveImageImpliesEquippedForImaging initial.statics g.dynamic ∧
  HaveSoilAnalysisImpliesEquipped initial.statics g.dynamic ∧
  HaveRockAnalysisImpliesEquipped initial.statics g.dynamic ∧
  GoalIgnoreAt initial g ∧
  GoalIgnoreEmpty initial g ∧
  GoalIgnoreFull initial g ∧
  GoalIgnoreHaveRockAnalysis initial g ∧
  GoalIgnoreHaveSoilAnalysis initial g ∧
  GoalIgnoreCalibrated initial g ∧
  GoalIgnoreHaveImage initial g ∧
  GoalIgnoreAtSoilSample initial g ∧
  GoalIgnoreAtRockSample initial g ∧
  GoalCommunicatedSoilOnlyPositive initial g ∧
  GoalCommunicatedRockOnlyPositive initial g ∧
  GoalCommunicatedImageOnlyPositive initial g ∧
  GoalCommunicatedSoilOnlySolvable initial g ∧
  GoalCommunicatedRockOnlySolvable initial g ∧
  GoalCommunicatedImageOnlySolvable initial g ∧
  GoalCommunicatedSoilImpliesSampleAtWaypoint initial g ∧
  GoalCommunicatedRockImpliesSampleAtWaypoint initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_x var_y,
    match g.dynamic.at_p var_x var_y with
    | none => True
    | some b => s.dynamic.at_p var_x var_y = b) ∧
  (∀ var_s,
    match g.dynamic.empty_p var_s with
    | none => True
    | some b => s.dynamic.empty_p var_s = b) ∧
  (∀ var_r var_w,
    match g.dynamic.have_rock_analysis_p var_r var_w with
    | none => True
    | some b => s.dynamic.have_rock_analysis_p var_r var_w = b) ∧
  (∀ var_r var_w,
    match g.dynamic.have_soil_analysis_p var_r var_w with
    | none => True
    | some b => s.dynamic.have_soil_analysis_p var_r var_w = b) ∧
  (∀ var_s,
    match g.dynamic.full_p var_s with
    | none => True
    | some b => s.dynamic.full_p var_s = b) ∧
  (∀ var_c var_r,
    match g.dynamic.calibrated_p var_c var_r with
    | none => True
    | some b => s.dynamic.calibrated_p var_c var_r = b) ∧
  (∀ var_r var_o var_m,
    match g.dynamic.have_image_p var_r var_o var_m with
    | none => True
    | some b => s.dynamic.have_image_p var_r var_o var_m = b) ∧
  (∀ var_w,
    match g.dynamic.communicated_soil_data_p var_w with
    | none => True
    | some b => s.dynamic.communicated_soil_data_p var_w = b) ∧
  (∀ var_w,
    match g.dynamic.communicated_rock_data_p var_w with
    | none => True
    | some b => s.dynamic.communicated_rock_data_p var_w = b) ∧
  (∀ var_o var_m,
    match g.dynamic.communicated_image_data_p var_o var_m with
    | none => True
    | some b => s.dynamic.communicated_image_data_p var_o var_m = b) ∧
  (∀ var_w,
    match g.dynamic.at_soil_sample_p var_w with
    | none => True
    | some b => s.dynamic.at_soil_sample_p var_w = b) ∧
  (∀ var_w,
    match g.dynamic.at_rock_sample_p var_w with
    | none => True
    | some b => s.dynamic.at_rock_sample_p var_w = b)

def navigatePre (var_x : Obj) (var_y : Obj) (var_z : Obj) (s : State) : Prop :=
  s.statics.rover_t var_x = true ∧
  s.statics.waypoint_t var_y = true ∧
  s.statics.waypoint_t var_z = true ∧
  s.statics.can_traverse_p var_x var_y var_z = true ∧
  s.dynamic.at_p var_x var_y = true ∧
  s.statics.visible_p var_y var_z = true

def sample_soilPre (var_x : Obj) (var_s : Obj) (var_p : Obj) (s : State) : Prop :=
  s.statics.rover_t var_x = true ∧
  s.statics.store_t var_s = true ∧
  s.statics.waypoint_t var_p = true ∧
  s.dynamic.at_p var_x var_p = true ∧
  s.dynamic.at_soil_sample_p var_p = true ∧
  s.statics.equipped_for_soil_analysis_p var_x = true ∧
  s.statics.store_of_p var_s var_x = true ∧
  s.dynamic.empty_p var_s = true

def sample_rockPre (var_x : Obj) (var_s : Obj) (var_p : Obj) (s : State) : Prop :=
  s.statics.rover_t var_x = true ∧
  s.statics.store_t var_s = true ∧
  s.statics.waypoint_t var_p = true ∧
  s.dynamic.at_p var_x var_p = true ∧
  s.dynamic.at_rock_sample_p var_p = true ∧
  s.statics.equipped_for_rock_analysis_p var_x = true ∧
  s.statics.store_of_p var_s var_x = true ∧
  s.dynamic.empty_p var_s = true

def dropPre (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.rover_t var_x = true ∧
  s.statics.store_t var_y = true ∧
  s.statics.store_of_p var_y var_x = true ∧
  s.dynamic.full_p var_y = true

def calibratePre (var_r : Obj) (var_i : Obj) (var_t : Obj) (var_w : Obj) (s : State) : Prop :=
  s.statics.rover_t var_r = true ∧
  s.statics.camera_t var_i = true ∧
  s.statics.objective_t var_t = true ∧
  s.statics.waypoint_t var_w = true ∧
  s.statics.equipped_for_imaging_p var_r = true ∧
  s.statics.calibration_target_p var_i var_t = true ∧
  s.dynamic.at_p var_r var_w = true ∧
  s.statics.visible_from_p var_t var_w = true ∧
  s.statics.on_board_p var_i var_r = true

def take_imagePre (var_r : Obj) (var_p : Obj) (var_o : Obj) (var_i : Obj) (var_m : Obj) (s : State) : Prop :=
  s.statics.rover_t var_r = true ∧
  s.statics.waypoint_t var_p = true ∧
  s.statics.objective_t var_o = true ∧
  s.statics.camera_t var_i = true ∧
  s.statics.mode_t var_m = true ∧
  s.dynamic.calibrated_p var_i var_r = true ∧
  s.statics.on_board_p var_i var_r = true ∧
  s.statics.equipped_for_imaging_p var_r = true ∧
  s.statics.supports_p var_i var_m = true ∧
  s.statics.visible_from_p var_o var_p = true ∧
  s.dynamic.at_p var_r var_p = true

def communicate_soil_dataPre (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.rover_t var_r = true ∧
  s.statics.lander_t var_l = true ∧
  s.statics.waypoint_t var_p = true ∧
  s.statics.waypoint_t var_x = true ∧
  s.statics.waypoint_t var_y = true ∧
  s.dynamic.at_p var_r var_x = true ∧
  s.statics.at_lander_p var_l var_y = true ∧
  s.dynamic.have_soil_analysis_p var_r var_p = true ∧
  s.statics.visible_p var_x var_y = true

def communicate_rock_dataPre (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.rover_t var_r = true ∧
  s.statics.lander_t var_l = true ∧
  s.statics.waypoint_t var_p = true ∧
  s.statics.waypoint_t var_x = true ∧
  s.statics.waypoint_t var_y = true ∧
  s.dynamic.at_p var_r var_x = true ∧
  s.statics.at_lander_p var_l var_y = true ∧
  s.dynamic.have_rock_analysis_p var_r var_p = true ∧
  s.statics.visible_p var_x var_y = true

def communicate_image_dataPre (var_r : Obj) (var_l : Obj) (var_o : Obj) (var_m : Obj) (var_x : Obj) (var_y : Obj) (s : State) : Prop :=
  s.statics.rover_t var_r = true ∧
  s.statics.lander_t var_l = true ∧
  s.statics.objective_t var_o = true ∧
  s.statics.mode_t var_m = true ∧
  s.statics.waypoint_t var_x = true ∧
  s.statics.waypoint_t var_y = true ∧
  s.dynamic.at_p var_r var_x = true ∧
  s.statics.at_lander_p var_l var_y = true ∧
  s.dynamic.have_image_p var_r var_o var_m = true ∧
  s.statics.visible_p var_x var_y = true

def navigate (var_x : Obj) (var_y : Obj) (var_z : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_x' var_z' =>
        if var_x' = var_x ∧ var_z' = var_z then
          true
        else if var_x' = var_x ∧ var_z' = var_y then
          false
        else
          s.dynamic.at_p var_x' var_z'
  }
}

def sample_soil (var_x : Obj) (var_s : Obj) (var_p : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    empty_p :=
      fun var_s' =>
        if var_s' = var_s then
          false
        else
          s.dynamic.empty_p var_s',
    have_soil_analysis_p :=
      fun var_x' var_p' =>
        if var_x' = var_x ∧ var_p' = var_p then
          true
        else
          s.dynamic.have_soil_analysis_p var_x' var_p',
    full_p :=
      fun var_s' =>
        if var_s' = var_s then
          true
        else
          s.dynamic.full_p var_s',
    at_soil_sample_p :=
      fun var_p' =>
        if var_p' = var_p then
          false
        else
          s.dynamic.at_soil_sample_p var_p'
  }
}

def sample_rock (var_x : Obj) (var_s : Obj) (var_p : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    empty_p :=
      fun var_s' =>
        if var_s' = var_s then
          false
        else
          s.dynamic.empty_p var_s',
    have_rock_analysis_p :=
      fun var_x' var_p' =>
        if var_x' = var_x ∧ var_p' = var_p then
          true
        else
          s.dynamic.have_rock_analysis_p var_x' var_p',
    full_p :=
      fun var_s' =>
        if var_s' = var_s then
          true
        else
          s.dynamic.full_p var_s',
    at_rock_sample_p :=
      fun var_p' =>
        if var_p' = var_p then
          false
        else
          s.dynamic.at_rock_sample_p var_p'
  }
}

def drop (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    empty_p :=
      fun var_y' =>
        if var_y' = var_y then
          true
        else
          s.dynamic.empty_p var_y',
    full_p :=
      fun var_y' =>
        if var_y' = var_y then
          false
        else
          s.dynamic.full_p var_y'
  }
}

def calibrate (var_r : Obj) (var_i : Obj) (var_t : Obj) (var_w : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    calibrated_p :=
      fun var_i' var_r' =>
        if var_i' = var_i ∧ var_r' = var_r then
          true
        else
          s.dynamic.calibrated_p var_i' var_r'
  }
}

def take_image (var_r : Obj) (var_p : Obj) (var_o : Obj) (var_i : Obj) (var_m : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    calibrated_p :=
      fun var_i' var_r' =>
        if var_i' = var_i ∧ var_r' = var_r then
          false
        else
          s.dynamic.calibrated_p var_i' var_r',
    have_image_p :=
      fun var_r' var_o' var_m' =>
        if var_r' = var_r ∧ var_o' = var_o ∧ var_m' = var_m then
          true
        else
          s.dynamic.have_image_p var_r' var_o' var_m'
  }
}

def communicate_soil_data (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    communicated_soil_data_p :=
      fun var_p' =>
        if var_p' = var_p then
          true
        else
          s.dynamic.communicated_soil_data_p var_p'
  }
}

def communicate_rock_data (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    communicated_rock_data_p :=
      fun var_p' =>
        if var_p' = var_p then
          true
        else
          s.dynamic.communicated_rock_data_p var_p'
  }
}

def communicate_image_data (var_r : Obj) (var_l : Obj) (var_o : Obj) (var_m : Obj) (var_x : Obj) (var_y : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    communicated_image_data_p :=
      fun var_o' var_m' =>
        if var_o' = var_o ∧ var_m' = var_m then
          true
        else
          s.dynamic.communicated_image_data_p var_o' var_m'
  }
}

inductive PlanAction where
  | navigate               (var_x : Obj) (var_y : Obj) (var_z : Obj)
  | sample_soil            (var_x : Obj) (var_s : Obj) (var_p : Obj)
  | sample_rock            (var_x : Obj) (var_s : Obj) (var_p : Obj)
  | drop                   (var_x : Obj) (var_y : Obj)
  | calibrate              (var_r : Obj) (var_i : Obj) (var_t : Obj) (var_w : Obj)
  | take_image             (var_r : Obj) (var_p : Obj) (var_o : Obj) (var_i : Obj) (var_m : Obj)
  | communicate_soil_data  (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj)
  | communicate_rock_data  (var_r : Obj) (var_l : Obj) (var_p : Obj) (var_x : Obj) (var_y : Obj)
  | communicate_image_data (var_r : Obj) (var_l : Obj) (var_o : Obj) (var_m : Obj) (var_x : Obj) (var_y : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .navigate               var_x var_y var_z                  , s => navigatePre var_x var_y var_z s
  | .sample_soil            var_x var_s var_p                  , s => sample_soilPre var_x var_s var_p s
  | .sample_rock            var_x var_s var_p                  , s => sample_rockPre var_x var_s var_p s
  | .drop                   var_x var_y                        , s => dropPre var_x var_y s
  | .calibrate              var_r var_i var_t var_w            , s => calibratePre var_r var_i var_t var_w s
  | .take_image             var_r var_p var_o var_i var_m      , s => take_imagePre var_r var_p var_o var_i var_m s
  | .communicate_soil_data  var_r var_l var_p var_x var_y      , s => communicate_soil_dataPre var_r var_l var_p var_x var_y s
  | .communicate_rock_data  var_r var_l var_p var_x var_y      , s => communicate_rock_dataPre var_r var_l var_p var_x var_y s
  | .communicate_image_data var_r var_l var_o var_m var_x var_y, s => communicate_image_dataPre var_r var_l var_o var_m var_x var_y s

def actionApply : PlanAction → State → State
  | .navigate               var_x var_y var_z                  , s => navigate var_x var_y var_z s
  | .sample_soil            var_x var_s var_p                  , s => sample_soil var_x var_s var_p s
  | .sample_rock            var_x var_s var_p                  , s => sample_rock var_x var_s var_p s
  | .drop                   var_x var_y                        , s => drop var_x var_y s
  | .calibrate              var_r var_i var_t var_w            , s => calibrate var_r var_i var_t var_w s
  | .take_image             var_r var_p var_o var_i var_m      , s => take_image var_r var_p var_o var_i var_m s
  | .communicate_soil_data  var_r var_l var_p var_x var_y      , s => communicate_soil_data var_r var_l var_p var_x var_y s
  | .communicate_rock_data  var_r var_l var_p var_x var_y      , s => communicate_rock_data var_r var_l var_p var_x var_y s
  | .communicate_image_data var_r var_l var_o var_m var_x var_y, s => communicate_image_data var_r var_l var_o var_m var_x var_y s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def gpFindObj? (xs : List Obj) (p : Obj → Bool) : Option Obj :=
  match xs with
  | [] => none
  | x :: rest =>
      if p x then
        some x
      else
        gpFindObj? rest p

def gpChooseObj (xs : List Obj) (p : Obj → Bool) : Obj :=
  match gpFindObj? xs p with
  | some x => x
  | none => 0

def gpFirstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x :: rest =>
      match f x with
      | some y => some y
      | none => gpFirstSome f rest

def gpIsSomeTrue : Option Bool → Bool
  | some true => true
  | _ => false

def gpNavDfs
    (ss : StaticState) (rover target : Obj) :
    Nat → List Obj → Obj → Option (List Obj)
  | 0, _, current =>
      if current = target then some [current] else none
  | fuel + 1, visited, current =>
      if current = target then
        some [current]
      else
        let nextWaypoints :=
          ss.objects.filter (fun next =>
            ss.waypoint_t next &&
            ss.can_traverse_p rover current next &&
            ss.visible_p current next &&
            decide (next ∉ visited))
        gpFirstSome
          (fun next =>
            match gpNavDfs ss rover target fuel (next :: visited) next with
            | some path => some (current :: path)
            | none => none)
          nextWaypoints

def gpNavigationActionsFrom
    (rover current : Obj) : List Obj → List PlanAction
  | [] => []
  | next :: rest =>
      PlanAction.navigate rover current next ::
        gpNavigationActionsFrom rover next rest

def gpPathToNavigationActions
    (rover : Obj) (path : List Obj) : List PlanAction :=
  match path with
  | [] => []
  | start :: rest => gpNavigationActionsFrom rover start rest

def gpRoverLocation (s : State) (rover : Obj) : Obj :=
  gpChooseObj s.statics.objects (fun waypoint =>
    s.dynamic.at_p rover waypoint)

def gpNavigationPlan (s : State) (rover target : Obj) : List PlanAction :=
  let start := gpRoverLocation s rover
  match
      gpNavDfs
        s.statics
        rover
        target
        (s.statics.objects.length + 1)
        [start]
        start
  with
  | some path => gpPathToNavigationActions rover path
  | none => []

def gpRequestedSoilWaypoints (s : State) (g : Goal) : List Obj :=
  s.statics.objects.filter (fun waypoint =>
    gpIsSomeTrue (g.dynamic.communicated_soil_data_p waypoint))

def gpRequestedRockWaypoints (s : State) (g : Goal) : List Obj :=
  s.statics.objects.filter (fun waypoint =>
    gpIsSomeTrue (g.dynamic.communicated_rock_data_p waypoint))

def gpRequestedImages
    (s : State) (g : Goal) : List (Obj × Obj) :=
  s.statics.objects.flatMap (fun objective =>
    s.statics.objects.filterMap (fun mode =>
      if gpIsSomeTrue
          (g.dynamic.communicated_image_data_p objective mode)
      then
        some (objective, mode)
      else
        none))

def gpSoilTask
    (mailbox lander landerWaypoint rover store sampleWaypoint : Obj)
    (acc : List PlanAction × State) : List PlanAction × State :=
  let state0 := acc.2

  let navToSample :=
    gpNavigationPlan state0 rover sampleWaypoint
  let state1 :=
    runPlan navToSample state0

  let sampleAct : PlanAction :=
    .sample_soil rover store sampleWaypoint
  let state2 :=
    actionApply sampleAct state1

  let dropAct : PlanAction :=
    .drop rover store
  let state3 :=
    actionApply dropAct state2

  let navToMailbox :=
    gpNavigationPlan state3 rover mailbox
  let state4 :=
    runPlan navToMailbox state3

  let communicateAct : PlanAction :=
    .communicate_soil_data
      rover lander sampleWaypoint mailbox landerWaypoint
  let state5 :=
    actionApply communicateAct state4

  ( acc.1 ++
      navToSample ++
      [sampleAct, dropAct] ++
      navToMailbox ++
      [communicateAct],
    state5 )

def gpRockTask
    (mailbox lander landerWaypoint rover store sampleWaypoint : Obj)
    (acc : List PlanAction × State) : List PlanAction × State :=
  let state0 := acc.2

  let navToSample :=
    gpNavigationPlan state0 rover sampleWaypoint
  let state1 :=
    runPlan navToSample state0

  let sampleAct : PlanAction :=
    .sample_rock rover store sampleWaypoint
  let state2 :=
    actionApply sampleAct state1

  let dropAct : PlanAction :=
    .drop rover store
  let state3 :=
    actionApply dropAct state2

  let navToMailbox :=
    gpNavigationPlan state3 rover mailbox
  let state4 :=
    runPlan navToMailbox state3

  let communicateAct : PlanAction :=
    .communicate_rock_data
      rover lander sampleWaypoint mailbox landerWaypoint
  let state5 :=
    actionApply communicateAct state4

  ( acc.1 ++
      navToSample ++
      [sampleAct, dropAct] ++
      navToMailbox ++
      [communicateAct],
    state5 )

def gpImageTask
    (mailbox lander landerWaypoint : Obj)
    (request : Obj × Obj)
    (acc : List PlanAction × State) : List PlanAction × State :=
  let state0 := acc.2
  let ss := state0.statics
  let objective := request.1
  let mode := request.2

  let camera :=
    gpChooseObj ss.objects (fun candidate =>
      ss.supports_p candidate mode)

  let rover :=
    gpChooseObj ss.objects (fun candidate =>
      ss.on_board_p camera candidate)

  let calibrationTarget :=
    gpChooseObj ss.objects (fun candidate =>
      ss.calibration_target_p camera candidate)

  let calibrationWaypoint :=
    gpChooseObj ss.objects (fun waypoint =>
      ss.visible_from_p calibrationTarget waypoint)

  let shootingWaypoint :=
    gpChooseObj ss.objects (fun waypoint =>
      ss.visible_from_p objective waypoint)

  let navToCalibration :=
    gpNavigationPlan state0 rover calibrationWaypoint
  let state1 :=
    runPlan navToCalibration state0

  let calibrateAct : PlanAction :=
    .calibrate
      rover camera calibrationTarget calibrationWaypoint
  let state2 :=
    actionApply calibrateAct state1

  let navToShooting :=
    gpNavigationPlan state2 rover shootingWaypoint
  let state3 :=
    runPlan navToShooting state2

  let takeImageAct : PlanAction :=
    .take_image
      rover shootingWaypoint objective camera mode
  let state4 :=
    actionApply takeImageAct state3

  let navToMailbox :=
    gpNavigationPlan state4 rover mailbox
  let state5 :=
    runPlan navToMailbox state4

  let communicateAct : PlanAction :=
    .communicate_image_data
      rover lander objective mode mailbox landerWaypoint
  let state6 :=
    actionApply communicateAct state5

  ( acc.1 ++
      navToCalibration ++
      [calibrateAct] ++
      navToShooting ++
      [takeImageAct] ++
      navToMailbox ++
      [communicateAct],
    state6 )

def solve (s : State) (g : Goal) : List PlanAction :=
  let objects := s.statics.objects

  let lander :=
    gpChooseObj objects (fun candidate =>
      s.statics.lander_t candidate)

  let landerWaypoint :=
    gpChooseObj objects (fun waypoint =>
      s.statics.at_lander_p lander waypoint)

  let mailbox :=
    gpChooseObj objects (fun waypoint =>
      s.statics.visible_p waypoint landerWaypoint)

  let soilGoals :=
    gpRequestedSoilWaypoints s g

  let rockGoals :=
    gpRequestedRockWaypoints s g

  let imageGoals :=
    gpRequestedImages s g

  let soilRover :=
    gpChooseObj objects (fun rover =>
      s.statics.equipped_for_soil_analysis_p rover)

  let soilStore :=
    gpChooseObj objects (fun store =>
      s.statics.store_of_p store soilRover)

  let rockRover :=
    gpChooseObj objects (fun rover =>
      s.statics.equipped_for_rock_analysis_p rover)

  let rockStore :=
    gpChooseObj objects (fun store =>
      s.statics.store_of_p store rockRover)

  let initialAccumulator : List PlanAction × State :=
    ([], s)

  let afterSoil :=
    soilGoals.foldl
      (fun acc waypoint =>
        gpSoilTask
          mailbox lander landerWaypoint
          soilRover soilStore waypoint
          acc)
      initialAccumulator

  let afterRock :=
    rockGoals.foldl
      (fun acc waypoint =>
        gpRockTask
          mailbox lander landerWaypoint
          rockRover rockStore waypoint
          acc)
      afterSoil

  let afterImages :=
    imageGoals.foldl
      (fun acc request =>
        gpImageTask
          mailbox lander landerWaypoint
          request acc)
      afterRock

  afterImages.1

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

lemma navigate_statics (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).statics = s.statics := rfl

lemma sample_soil_statics (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).statics = s.statics := rfl

lemma sample_rock_statics (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).statics = s.statics := rfl

lemma drop_statics (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).statics = s.statics := rfl

lemma calibrate_statics (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).statics = s.statics := rfl

lemma take_image_statics (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).statics = s.statics := rfl

lemma communicate_soil_data_statics (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).statics = s.statics := rfl

lemma communicate_rock_data_statics (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).statics = s.statics := rfl

lemma communicate_image_data_statics (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | navigate var_x var_y var_z                                 => exact navigate_statics var_x var_y var_z s
      | sample_soil var_x var_s var_p                              => exact sample_soil_statics var_x var_s var_p s
      | sample_rock var_x var_s var_p                              => exact sample_rock_statics var_x var_s var_p s
      | drop var_x var_y                                           => exact drop_statics var_x var_y s
      | calibrate var_r var_i var_t var_w                          => exact calibrate_statics var_r var_i var_t var_w s
      | take_image var_r var_p var_o var_i var_m                   => exact take_image_statics var_r var_p var_o var_i var_m s
      | communicate_soil_data var_r var_l var_p var_x var_y        => exact communicate_soil_data_statics var_r var_l var_p var_x var_y s
      | communicate_rock_data var_r var_l var_p var_x var_y        => exact communicate_rock_data_statics var_r var_l var_p var_x var_y s
      | communicate_image_data var_r var_l var_o var_m var_x var_y => exact communicate_image_data_statics var_r var_l var_o var_m var_x var_y s

-- navigate only touches at_p
lemma navigate_at_p_ne_var_y (var_x var_y var_z : Obj) (s : State) {var_z' : Obj} (h1 : var_z' ≠ var_z) (h2 : var_z' ≠ var_y) :
    (navigate var_x var_y var_z s).dynamic.at_p var_x var_z' = s.dynamic.at_p var_x var_z' := by
  unfold navigate
  simp [h1, h2]

-- navigate never touches empty_p
lemma navigate_empty_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- navigate never touches have_rock_analysis_p
lemma navigate_have_rock_analysis_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- navigate never touches have_soil_analysis_p
lemma navigate_have_soil_analysis_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- navigate never touches full_p
lemma navigate_full_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.full_p = s.dynamic.full_p := rfl

-- navigate never touches calibrated_p
lemma navigate_calibrated_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- navigate never touches have_image_p
lemma navigate_have_image_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- navigate never touches communicated_soil_data_p
lemma navigate_communicated_soil_data_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- navigate never touches communicated_rock_data_p
lemma navigate_communicated_rock_data_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- navigate never touches communicated_image_data_p
lemma navigate_communicated_image_data_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- navigate never touches at_soil_sample_p
lemma navigate_at_soil_sample_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- navigate never touches at_rock_sample_p
lemma navigate_at_rock_sample_p (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- sample_soil only touches full_p, have_soil_analysis_p, empty_p, at_soil_sample_p
lemma sample_soil_empty_p_ne (var_x var_s var_p : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (sample_soil var_x var_s var_p s).dynamic.empty_p var_s' = s.dynamic.empty_p var_s' := by
  unfold sample_soil
  simp [h1]

lemma sample_soil_have_soil_analysis_p_ne (var_x var_s var_p : Obj) (s : State) {var_x' var_p' : Obj} (h1 : var_x' ≠ var_x) :
    (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p var_x' var_p' = s.dynamic.have_soil_analysis_p var_x' var_p' := by
  unfold sample_soil
  simp [h1]

lemma sample_soil_have_soil_analysis_p_ne_var_w (var_x var_s var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p var_x var_p' = s.dynamic.have_soil_analysis_p var_x var_p' := by
  unfold sample_soil
  simp [h1]

lemma sample_soil_full_p_ne (var_x var_s var_p : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (sample_soil var_x var_s var_p s).dynamic.full_p var_s' = s.dynamic.full_p var_s' := by
  unfold sample_soil
  simp [h1]

lemma sample_soil_at_soil_sample_p_ne (var_x var_s var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (sample_soil var_x var_s var_p s).dynamic.at_soil_sample_p var_p' = s.dynamic.at_soil_sample_p var_p' := by
  unfold sample_soil
  simp [h1]

-- sample_soil never touches at_p
lemma sample_soil_at_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.at_p = s.dynamic.at_p := rfl

-- sample_soil never touches have_rock_analysis_p
lemma sample_soil_have_rock_analysis_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- sample_soil never touches calibrated_p
lemma sample_soil_calibrated_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- sample_soil never touches have_image_p
lemma sample_soil_have_image_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- sample_soil never touches communicated_soil_data_p
lemma sample_soil_communicated_soil_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- sample_soil never touches communicated_rock_data_p
lemma sample_soil_communicated_rock_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- sample_soil never touches communicated_image_data_p
lemma sample_soil_communicated_image_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- sample_soil never touches at_rock_sample_p
lemma sample_soil_at_rock_sample_p (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- sample_rock only touches full_p, have_rock_analysis_p, empty_p, at_rock_sample_p
lemma sample_rock_empty_p_ne (var_x var_s var_p : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (sample_rock var_x var_s var_p s).dynamic.empty_p var_s' = s.dynamic.empty_p var_s' := by
  unfold sample_rock
  simp [h1]

lemma sample_rock_have_rock_analysis_p_ne (var_x var_s var_p : Obj) (s : State) {var_x' var_p' : Obj} (h1 : var_x' ≠ var_x) :
    (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p var_x' var_p' = s.dynamic.have_rock_analysis_p var_x' var_p' := by
  unfold sample_rock
  simp [h1]

lemma sample_rock_have_rock_analysis_p_ne_var_w (var_x var_s var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p var_x var_p' = s.dynamic.have_rock_analysis_p var_x var_p' := by
  unfold sample_rock
  simp [h1]

lemma sample_rock_full_p_ne (var_x var_s var_p : Obj) (s : State) {var_s' : Obj} (h1 : var_s' ≠ var_s) :
    (sample_rock var_x var_s var_p s).dynamic.full_p var_s' = s.dynamic.full_p var_s' := by
  unfold sample_rock
  simp [h1]

lemma sample_rock_at_rock_sample_p_ne (var_x var_s var_p : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (sample_rock var_x var_s var_p s).dynamic.at_rock_sample_p var_p' = s.dynamic.at_rock_sample_p var_p' := by
  unfold sample_rock
  simp [h1]

-- sample_rock never touches at_p
lemma sample_rock_at_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.at_p = s.dynamic.at_p := rfl

-- sample_rock never touches have_soil_analysis_p
lemma sample_rock_have_soil_analysis_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- sample_rock never touches calibrated_p
lemma sample_rock_calibrated_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- sample_rock never touches have_image_p
lemma sample_rock_have_image_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- sample_rock never touches communicated_soil_data_p
lemma sample_rock_communicated_soil_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- sample_rock never touches communicated_rock_data_p
lemma sample_rock_communicated_rock_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- sample_rock never touches communicated_image_data_p
lemma sample_rock_communicated_image_data_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- sample_rock never touches at_soil_sample_p
lemma sample_rock_at_soil_sample_p (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- drop only touches empty_p, full_p
lemma drop_empty_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (drop var_x var_y s).dynamic.empty_p var_y' = s.dynamic.empty_p var_y' := by
  unfold drop
  simp [h1]

lemma drop_full_p_ne (var_x var_y : Obj) (s : State) {var_y' : Obj} (h1 : var_y' ≠ var_y) :
    (drop var_x var_y s).dynamic.full_p var_y' = s.dynamic.full_p var_y' := by
  unfold drop
  simp [h1]

-- drop never touches at_p
lemma drop_at_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.at_p = s.dynamic.at_p := rfl

-- drop never touches have_rock_analysis_p
lemma drop_have_rock_analysis_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- drop never touches have_soil_analysis_p
lemma drop_have_soil_analysis_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- drop never touches calibrated_p
lemma drop_calibrated_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- drop never touches have_image_p
lemma drop_have_image_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- drop never touches communicated_soil_data_p
lemma drop_communicated_soil_data_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- drop never touches communicated_rock_data_p
lemma drop_communicated_rock_data_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- drop never touches communicated_image_data_p
lemma drop_communicated_image_data_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- drop never touches at_soil_sample_p
lemma drop_at_soil_sample_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- drop never touches at_rock_sample_p
lemma drop_at_rock_sample_p (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- calibrate only touches calibrated_p
lemma calibrate_calibrated_p_ne (var_r var_i var_t var_w : Obj) (s : State) {var_i' var_r' : Obj} (h1 : var_i' ≠ var_i) :
    (calibrate var_r var_i var_t var_w s).dynamic.calibrated_p var_i' var_r' = s.dynamic.calibrated_p var_i' var_r' := by
  unfold calibrate
  simp [h1]

lemma calibrate_calibrated_p_ne_var_r (var_r var_i var_t var_w : Obj) (s : State) {var_r' : Obj} (h1 : var_r' ≠ var_r) :
    (calibrate var_r var_i var_t var_w s).dynamic.calibrated_p var_i var_r' = s.dynamic.calibrated_p var_i var_r' := by
  unfold calibrate
  simp [h1]

-- calibrate never touches at_p
lemma calibrate_at_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.at_p = s.dynamic.at_p := rfl

-- calibrate never touches empty_p
lemma calibrate_empty_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- calibrate never touches have_rock_analysis_p
lemma calibrate_have_rock_analysis_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- calibrate never touches have_soil_analysis_p
lemma calibrate_have_soil_analysis_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- calibrate never touches full_p
lemma calibrate_full_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.full_p = s.dynamic.full_p := rfl

-- calibrate never touches have_image_p
lemma calibrate_have_image_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- calibrate never touches communicated_soil_data_p
lemma calibrate_communicated_soil_data_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- calibrate never touches communicated_rock_data_p
lemma calibrate_communicated_rock_data_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- calibrate never touches communicated_image_data_p
lemma calibrate_communicated_image_data_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- calibrate never touches at_soil_sample_p
lemma calibrate_at_soil_sample_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- calibrate never touches at_rock_sample_p
lemma calibrate_at_rock_sample_p (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- take_image only touches have_image_p, calibrated_p
lemma take_image_calibrated_p_ne (var_r var_p var_o var_i var_m : Obj) (s : State) {var_i' var_r' : Obj} (h1 : var_i' ≠ var_i) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.calibrated_p var_i' var_r' = s.dynamic.calibrated_p var_i' var_r' := by
  unfold take_image
  simp [h1]

lemma take_image_calibrated_p_ne_var_r (var_r var_p var_o var_i var_m : Obj) (s : State) {var_r' : Obj} (h1 : var_r' ≠ var_r) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.calibrated_p var_i var_r' = s.dynamic.calibrated_p var_i var_r' := by
  unfold take_image
  simp [h1]

lemma take_image_have_image_p_ne (var_r var_p var_o var_i var_m : Obj) (s : State) {var_r' var_o' var_m' : Obj} (h1 : var_r' ≠ var_r) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p var_r' var_o' var_m' = s.dynamic.have_image_p var_r' var_o' var_m' := by
  unfold take_image
  simp [h1]

lemma take_image_have_image_p_ne_var_o (var_r var_p var_o var_i var_m : Obj) (s : State) {var_o' var_m' : Obj} (h1 : var_o' ≠ var_o) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p var_r var_o' var_m' = s.dynamic.have_image_p var_r var_o' var_m' := by
  unfold take_image
  simp [h1]

lemma take_image_have_image_p_ne_var_m (var_r var_p var_o var_i var_m : Obj) (s : State) {var_m' : Obj} (h1 : var_m' ≠ var_m) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p var_r var_o var_m' = s.dynamic.have_image_p var_r var_o var_m' := by
  unfold take_image
  simp [h1]

-- take_image never touches at_p
lemma take_image_at_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.at_p = s.dynamic.at_p := rfl

-- take_image never touches empty_p
lemma take_image_empty_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- take_image never touches have_rock_analysis_p
lemma take_image_have_rock_analysis_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- take_image never touches have_soil_analysis_p
lemma take_image_have_soil_analysis_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- take_image never touches full_p
lemma take_image_full_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.full_p = s.dynamic.full_p := rfl

-- take_image never touches communicated_soil_data_p
lemma take_image_communicated_soil_data_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- take_image never touches communicated_rock_data_p
lemma take_image_communicated_rock_data_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- take_image never touches communicated_image_data_p
lemma take_image_communicated_image_data_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- take_image never touches at_soil_sample_p
lemma take_image_at_soil_sample_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- take_image never touches at_rock_sample_p
lemma take_image_at_rock_sample_p (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- communicate_soil_data only touches communicated_soil_data_p
lemma communicate_soil_data_communicated_soil_data_p_ne (var_r var_l var_p var_x var_y : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_soil_data_p var_p' = s.dynamic.communicated_soil_data_p var_p' := by
  unfold communicate_soil_data
  simp [h1]

-- communicate_soil_data never touches at_p
lemma communicate_soil_data_at_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.at_p = s.dynamic.at_p := rfl

-- communicate_soil_data never touches empty_p
lemma communicate_soil_data_empty_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- communicate_soil_data never touches have_rock_analysis_p
lemma communicate_soil_data_have_rock_analysis_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- communicate_soil_data never touches have_soil_analysis_p
lemma communicate_soil_data_have_soil_analysis_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- communicate_soil_data never touches full_p
lemma communicate_soil_data_full_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.full_p = s.dynamic.full_p := rfl

-- communicate_soil_data never touches calibrated_p
lemma communicate_soil_data_calibrated_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- communicate_soil_data never touches have_image_p
lemma communicate_soil_data_have_image_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- communicate_soil_data never touches communicated_rock_data_p
lemma communicate_soil_data_communicated_rock_data_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- communicate_soil_data never touches communicated_image_data_p
lemma communicate_soil_data_communicated_image_data_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- communicate_soil_data never touches at_soil_sample_p
lemma communicate_soil_data_at_soil_sample_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- communicate_soil_data never touches at_rock_sample_p
lemma communicate_soil_data_at_rock_sample_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- communicate_rock_data only touches communicated_rock_data_p
lemma communicate_rock_data_communicated_rock_data_p_ne (var_r var_l var_p var_x var_y : Obj) (s : State) {var_p' : Obj} (h1 : var_p' ≠ var_p) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_rock_data_p var_p' = s.dynamic.communicated_rock_data_p var_p' := by
  unfold communicate_rock_data
  simp [h1]

-- communicate_rock_data never touches at_p
lemma communicate_rock_data_at_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.at_p = s.dynamic.at_p := rfl

-- communicate_rock_data never touches empty_p
lemma communicate_rock_data_empty_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- communicate_rock_data never touches have_rock_analysis_p
lemma communicate_rock_data_have_rock_analysis_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- communicate_rock_data never touches have_soil_analysis_p
lemma communicate_rock_data_have_soil_analysis_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- communicate_rock_data never touches full_p
lemma communicate_rock_data_full_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.full_p = s.dynamic.full_p := rfl

-- communicate_rock_data never touches calibrated_p
lemma communicate_rock_data_calibrated_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- communicate_rock_data never touches have_image_p
lemma communicate_rock_data_have_image_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- communicate_rock_data never touches communicated_soil_data_p
lemma communicate_rock_data_communicated_soil_data_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- communicate_rock_data never touches communicated_image_data_p
lemma communicate_rock_data_communicated_image_data_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_image_data_p = s.dynamic.communicated_image_data_p := rfl

-- communicate_rock_data never touches at_soil_sample_p
lemma communicate_rock_data_at_soil_sample_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- communicate_rock_data never touches at_rock_sample_p
lemma communicate_rock_data_at_rock_sample_p (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

-- communicate_image_data only touches communicated_image_data_p
lemma communicate_image_data_communicated_image_data_p_ne (var_r var_l var_o var_m var_x var_y : Obj) (s : State) {var_o' var_m' : Obj} (h1 : var_o' ≠ var_o) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_image_data_p var_o' var_m' = s.dynamic.communicated_image_data_p var_o' var_m' := by
  unfold communicate_image_data
  simp [h1]

lemma communicate_image_data_communicated_image_data_p_ne_var_m (var_r var_l var_o var_m var_x var_y : Obj) (s : State) {var_m' : Obj} (h1 : var_m' ≠ var_m) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_image_data_p var_o var_m' = s.dynamic.communicated_image_data_p var_o var_m' := by
  unfold communicate_image_data
  simp [h1]

-- communicate_image_data never touches at_p
lemma communicate_image_data_at_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.at_p = s.dynamic.at_p := rfl

-- communicate_image_data never touches empty_p
lemma communicate_image_data_empty_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.empty_p = s.dynamic.empty_p := rfl

-- communicate_image_data never touches have_rock_analysis_p
lemma communicate_image_data_have_rock_analysis_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.have_rock_analysis_p = s.dynamic.have_rock_analysis_p := rfl

-- communicate_image_data never touches have_soil_analysis_p
lemma communicate_image_data_have_soil_analysis_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.have_soil_analysis_p = s.dynamic.have_soil_analysis_p := rfl

-- communicate_image_data never touches full_p
lemma communicate_image_data_full_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.full_p = s.dynamic.full_p := rfl

-- communicate_image_data never touches calibrated_p
lemma communicate_image_data_calibrated_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.calibrated_p = s.dynamic.calibrated_p := rfl

-- communicate_image_data never touches have_image_p
lemma communicate_image_data_have_image_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.have_image_p = s.dynamic.have_image_p := rfl

-- communicate_image_data never touches communicated_soil_data_p
lemma communicate_image_data_communicated_soil_data_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_soil_data_p = s.dynamic.communicated_soil_data_p := rfl

-- communicate_image_data never touches communicated_rock_data_p
lemma communicate_image_data_communicated_rock_data_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_rock_data_p = s.dynamic.communicated_rock_data_p := rfl

-- communicate_image_data never touches at_soil_sample_p
lemma communicate_image_data_at_soil_sample_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.at_soil_sample_p = s.dynamic.at_soil_sample_p := rfl

-- communicate_image_data never touches at_rock_sample_p
lemma communicate_image_data_at_rock_sample_p (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.at_rock_sample_p = s.dynamic.at_rock_sample_p := rfl

lemma navigate_at_p_eq1 (var_x var_y var_z : Obj) (s : State) :
    (navigate var_x var_y var_z s).dynamic.at_p var_x var_z = true := by
  unfold navigate
  simp

lemma navigate_at_p_eq2 (var_x var_y var_z : Obj) (s : State) (h1 : var_y ≠ var_z) :
    (navigate var_x var_y var_z s).dynamic.at_p var_x var_y = false := by
  unfold navigate
  simp [h1]

lemma sample_soil_empty_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.empty_p var_s = false := by
  unfold sample_soil
  simp

lemma sample_soil_have_soil_analysis_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p var_x var_p = true := by
  unfold sample_soil
  simp

lemma sample_soil_full_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.full_p var_s = true := by
  unfold sample_soil
  simp

lemma sample_soil_at_soil_sample_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_soil var_x var_s var_p s).dynamic.at_soil_sample_p var_p = false := by
  unfold sample_soil
  simp

lemma sample_rock_empty_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.empty_p var_s = false := by
  unfold sample_rock
  simp

lemma sample_rock_have_rock_analysis_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p var_x var_p = true := by
  unfold sample_rock
  simp

lemma sample_rock_full_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.full_p var_s = true := by
  unfold sample_rock
  simp

lemma sample_rock_at_rock_sample_p_eq1 (var_x var_s var_p : Obj) (s : State) :
    (sample_rock var_x var_s var_p s).dynamic.at_rock_sample_p var_p = false := by
  unfold sample_rock
  simp

lemma drop_empty_p_eq1 (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.empty_p var_y = true := by
  unfold drop
  simp

lemma drop_full_p_eq1 (var_x var_y : Obj) (s : State) :
    (drop var_x var_y s).dynamic.full_p var_y = false := by
  unfold drop
  simp

lemma calibrate_calibrated_p_eq1 (var_r var_i var_t var_w : Obj) (s : State) :
    (calibrate var_r var_i var_t var_w s).dynamic.calibrated_p var_i var_r = true := by
  unfold calibrate
  simp

lemma take_image_calibrated_p_eq1 (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.calibrated_p var_i var_r = false := by
  unfold take_image
  simp

lemma take_image_have_image_p_eq1 (var_r var_p var_o var_i var_m : Obj) (s : State) :
    (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p var_r var_o var_m = true := by
  unfold take_image
  simp

lemma communicate_soil_data_communicated_soil_data_p_eq1 (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_soil_data_p var_p = true := by
  unfold communicate_soil_data
  simp

lemma communicate_rock_data_communicated_rock_data_p_eq1 (var_r var_l var_p var_x var_y : Obj) (s : State) :
    (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_rock_data_p var_p = true := by
  unfold communicate_rock_data
  simp

lemma communicate_image_data_communicated_image_data_p_eq1 (var_r var_l var_o var_m var_x var_y : Obj) (s : State) :
    (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_image_data_p var_o var_m = true := by
  unfold communicate_image_data
  simp

lemma navigate_preserves_wf
    (var_x var_y var_z)
    (s : State)
    (hwf : WellFormed s)
    (hpre : navigatePre var_x var_y var_z s) :
    WellFormed (navigate var_x var_y var_z s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with ⟨hxT, hyT, hzT, hTraverse, hAtXY, hVisible⟩
  refine
    ⟨hWS, ?_, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, ?_, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     ?_, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  · unfold ValidAtParam
    intro r w h
    change (navigate var_x var_y var_z s).dynamic.at_p r w = true at h
    by_cases hr : r = var_x
    · subst r
      by_cases hwz : w = var_z
      · subst w
        exact ⟨hxT, hzT⟩
      · by_cases hwy : w = var_y
        · subst w
          simp [navigate, hwz] at h
        · have hOld : s.dynamic.at_p var_x w = true := by
            simpa [navigate, hwz, hwy] using h
          exact hVAt var_x w hOld
    · have hOld : s.dynamic.at_p r w = true := by
        simpa [navigate, hr] using h
      exact hVAt r w hOld
  · unfold AtMostOneLocation
    intro r w1 w2 h1 h2
    change (navigate var_x var_y var_z s).dynamic.at_p r w1 = true at h1
    change (navigate var_x var_y var_z s).dynamic.at_p r w2 = true at h2
    by_cases hr : r = var_x
    · subst r
      have hloc :
          ∀ w,
            (navigate var_x var_y var_z s).dynamic.at_p var_x w = true →
            w = var_z := by
        intro w hw
        by_cases hwz : w = var_z
        · exact hwz
        · by_cases hwy : w = var_y
          · subst w
            simp [navigate, hwz] at hw
          · have hOld : s.dynamic.at_p var_x w = true := by
              simpa [navigate, hwz, hwy] using hw
            have hEq : w = var_y :=
              hOneLoc var_x w var_y hOld hAtXY
            exact (hwy hEq).elim
      exact (hloc w1 h1).trans (hloc w2 h2).symm
    · have hOld1 : s.dynamic.at_p r w1 = true := by
        simpa [navigate, hr] using h1
      have hOld2 : s.dynamic.at_p r w2 = true := by
        simpa [navigate, hr] using h2
      exact hOneLoc r w1 w2 hOld1 hOld2
  · unfold RoverHasLocation
    intro r hrT
    by_cases hr : r = var_x
    · subst r
      exact ⟨var_z, navigate_at_p_eq1 var_x var_y var_z s⟩
    · obtain ⟨w, hw⟩ := hRoverLoc r hrT
      refine ⟨w, ?_⟩
      simpa [navigate, hr] using hw

lemma sample_soil_preserves_wf
    (var_x var_s var_p)
    (s : State)
    (hwf : WellFormed s)
    (hpre : sample_soilPre var_x var_s var_p s) :
    WellFormed (sample_soil var_x var_s var_p s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hxT, hsT, hpT, hAt, hSample, hEquipped, hStoreOf, hEmpty⟩
  refine
    ⟨hWS, hVAt, ?_, hVRock, ?_, ?_, hVCal, hVImage,
     hVCS, hVCR, hVCI, ?_, hVAtRock, hOneLoc, ?_,
     ?_, hRockNo, hCalInv, hImageEquip, ?_, hRockEquip,
     hRoverLoc, ?_, ?_, hCRHave, hCIHave⟩
  · unfold ValidEmptyParam
    intro st h
    change (sample_soil var_x var_s var_p s).dynamic.empty_p st = true at h
    by_cases hst : st = var_s
    · subst st
      simp [sample_soil] at h
    · have hOld : s.dynamic.empty_p st = true := by
        simpa [sample_soil, hst] using h
      exact hVEmpty st hOld
  · unfold ValidHaveSoilAnalysisParam
    intro r w h
    change
      (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p r w =
        true at h
    by_cases hm : r = var_x ∧ w = var_p
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨hxT, hpT⟩
    · have hOld : s.dynamic.have_soil_analysis_p r w = true := by
        simpa [sample_soil, hm] using h
      exact hVSoil r w hOld
  · unfold ValidFullParam
    intro st h
    change (sample_soil var_x var_s var_p s).dynamic.full_p st = true at h
    by_cases hst : st = var_s
    · subst st
      exact hsT
    · have hOld : s.dynamic.full_p st = true := by
        simpa [sample_soil, hst] using h
      exact hVFull st hOld
  · unfold ValidAtSoilSampleParam
    intro w h
    change
      (sample_soil var_x var_s var_p s).dynamic.at_soil_sample_p w =
        true at h
    by_cases hw : w = var_p
    · subst w
      simp [sample_soil] at h
    · have hOld : s.dynamic.at_soil_sample_p w = true := by
        simpa [sample_soil, hw] using h
      exact hVAtSoil w hOld
  · unfold EmptyFullExclusive
    intro st hbad
    rcases hbad with ⟨he, hf⟩
    change (sample_soil var_x var_s var_p s).dynamic.empty_p st = true at he
    change (sample_soil var_x var_s var_p s).dynamic.full_p st = true at hf
    by_cases hst : st = var_s
    · subst st
      simp [sample_soil] at he
    · have heOld : s.dynamic.empty_p st = true := by
        simpa [sample_soil, hst] using he
      have hfOld : s.dynamic.full_p st = true := by
        simpa [sample_soil, hst] using hf
      exact hExclusive st ⟨heOld, hfOld⟩
  · unfold HaveSoilAnalysisImpliesNotAtSoilSample
    intro r p hh hs
    change
      (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p r p =
        true at hh
    change
      (sample_soil var_x var_s var_p s).dynamic.at_soil_sample_p p =
        true at hs
    by_cases hp : p = var_p
    · subst p
      simp [sample_soil] at hs
    · have hhOld : s.dynamic.have_soil_analysis_p r p = true := by
        simpa [sample_soil, hp] using hh
      have hsOld : s.dynamic.at_soil_sample_p p = true := by
        simpa [sample_soil, hp] using hs
      exact hSoilNo r p hhOld hsOld
  · unfold HaveSoilAnalysisImpliesEquipped
    intro r p hh
    change
      (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p r p =
        true at hh
    by_cases hm : r = var_x ∧ p = var_p
    · rcases hm with ⟨rfl, rfl⟩
      exact hEquipped
    · have hhOld : s.dynamic.have_soil_analysis_p r p = true := by
        simpa [sample_soil, hm] using hh
      exact hSoilEquip r p hhOld
  · unfold StoreEmptyOrFull
    intro st hstT
    by_cases hst : st = var_s
    · subst st
      exact Or.inr (sample_soil_full_p_eq1 var_x var_s var_p s)
    · rcases hStoreTotal st hstT with he | hf
      · exact Or.inl (by simpa [sample_soil, hst] using he)
      · exact Or.inr (by simpa [sample_soil, hst] using hf)
  · unfold CommunicatedSoilImpliesHaveSoilAnalysis
    intro p hc
    obtain ⟨r, hr⟩ := hCSHave p hc
    refine ⟨r, ?_⟩
    change
      (sample_soil var_x var_s var_p s).dynamic.have_soil_analysis_p r p =
        true
    change s.dynamic.have_soil_analysis_p r p = true at hr
    by_cases hm : r = var_x ∧ p = var_p
    · simp [sample_soil, hm]
    · simpa [sample_soil, hm] using hr

lemma sample_rock_preserves_wf
    (var_x var_s var_p)
    (s : State)
    (hwf : WellFormed s)
    (hpre : sample_rockPre var_x var_s var_p s) :
    WellFormed (sample_rock var_x var_s var_p s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hxT, hsT, hpT, hAt, hSample, hEquipped, hStoreOf, hEmpty⟩
  refine
    ⟨hWS, hVAt, ?_, ?_, hVSoil, ?_, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, ?_, hOneLoc, ?_,
     hSoilNo, ?_, hCalInv, hImageEquip, hSoilEquip, ?_,
     hRoverLoc, ?_, hCSHave, ?_, hCIHave⟩
  · unfold ValidEmptyParam
    intro st h
    change (sample_rock var_x var_s var_p s).dynamic.empty_p st = true at h
    by_cases hst : st = var_s
    · subst st
      simp [sample_rock] at h
    · have hOld : s.dynamic.empty_p st = true := by
        simpa [sample_rock, hst] using h
      exact hVEmpty st hOld
  · unfold ValidHaveRockAnalysisParam
    intro r w h
    change
      (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p r w =
        true at h
    by_cases hm : r = var_x ∧ w = var_p
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨hxT, hpT⟩
    · have hOld : s.dynamic.have_rock_analysis_p r w = true := by
        simpa [sample_rock, hm] using h
      exact hVRock r w hOld
  · unfold ValidFullParam
    intro st h
    change (sample_rock var_x var_s var_p s).dynamic.full_p st = true at h
    by_cases hst : st = var_s
    · subst st
      exact hsT
    · have hOld : s.dynamic.full_p st = true := by
        simpa [sample_rock, hst] using h
      exact hVFull st hOld
  · unfold ValidAtRockSampleParam
    intro w h
    change
      (sample_rock var_x var_s var_p s).dynamic.at_rock_sample_p w =
        true at h
    by_cases hw : w = var_p
    · subst w
      simp [sample_rock] at h
    · have hOld : s.dynamic.at_rock_sample_p w = true := by
        simpa [sample_rock, hw] using h
      exact hVAtRock w hOld
  · unfold EmptyFullExclusive
    intro st hbad
    rcases hbad with ⟨he, hf⟩
    change (sample_rock var_x var_s var_p s).dynamic.empty_p st = true at he
    change (sample_rock var_x var_s var_p s).dynamic.full_p st = true at hf
    by_cases hst : st = var_s
    · subst st
      simp [sample_rock] at he
    · have heOld : s.dynamic.empty_p st = true := by
        simpa [sample_rock, hst] using he
      have hfOld : s.dynamic.full_p st = true := by
        simpa [sample_rock, hst] using hf
      exact hExclusive st ⟨heOld, hfOld⟩
  · unfold HaveRockAnalysisImpliesNotAtRockSample
    intro r p hh hs
    change
      (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p r p =
        true at hh
    change
      (sample_rock var_x var_s var_p s).dynamic.at_rock_sample_p p =
        true at hs
    by_cases hp : p = var_p
    · subst p
      simp [sample_rock] at hs
    · have hhOld : s.dynamic.have_rock_analysis_p r p = true := by
        simpa [sample_rock, hp] using hh
      have hsOld : s.dynamic.at_rock_sample_p p = true := by
        simpa [sample_rock, hp] using hs
      exact hRockNo r p hhOld hsOld
  · unfold HaveRockAnalysisImpliesEquipped
    intro r p hh
    change
      (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p r p =
        true at hh
    by_cases hm : r = var_x ∧ p = var_p
    · rcases hm with ⟨rfl, rfl⟩
      exact hEquipped
    · have hhOld : s.dynamic.have_rock_analysis_p r p = true := by
        simpa [sample_rock, hm] using hh
      exact hRockEquip r p hhOld
  · unfold StoreEmptyOrFull
    intro st hstT
    by_cases hst : st = var_s
    · subst st
      exact Or.inr (sample_rock_full_p_eq1 var_x var_s var_p s)
    · rcases hStoreTotal st hstT with he | hf
      · exact Or.inl (by simpa [sample_rock, hst] using he)
      · exact Or.inr (by simpa [sample_rock, hst] using hf)
  · unfold CommunicatedRockImpliesHaveRockAnalysis
    intro p hc
    obtain ⟨r, hr⟩ := hCRHave p hc
    refine ⟨r, ?_⟩
    change
      (sample_rock var_x var_s var_p s).dynamic.have_rock_analysis_p r p =
        true
    change s.dynamic.have_rock_analysis_p r p = true at hr
    by_cases hm : r = var_x ∧ p = var_p
    · simp [sample_rock, hm]
    · simpa [sample_rock, hm] using hr

lemma drop_preserves_wf
    (var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre : dropPre var_x var_y s) :
    WellFormed (drop var_x var_y s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with ⟨hxT, hyT, hStoreOf, hFull⟩
  refine
    ⟨hWS, hVAt, ?_, hVRock, hVSoil, ?_, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, ?_,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, ?_, hCSHave, hCRHave, hCIHave⟩
  · unfold ValidEmptyParam
    intro st h
    change (drop var_x var_y s).dynamic.empty_p st = true at h
    by_cases hst : st = var_y
    · subst st
      exact hyT
    · have hOld : s.dynamic.empty_p st = true := by
        simpa [drop, hst] using h
      exact hVEmpty st hOld
  · unfold ValidFullParam
    intro st h
    change (drop var_x var_y s).dynamic.full_p st = true at h
    by_cases hst : st = var_y
    · subst st
      simp [drop] at h
    · have hOld : s.dynamic.full_p st = true := by
        simpa [drop, hst] using h
      exact hVFull st hOld
  · unfold EmptyFullExclusive
    intro st hbad
    rcases hbad with ⟨he, hf⟩
    change (drop var_x var_y s).dynamic.empty_p st = true at he
    change (drop var_x var_y s).dynamic.full_p st = true at hf
    by_cases hst : st = var_y
    · subst st
      simp [drop] at hf
    · have heOld : s.dynamic.empty_p st = true := by
        simpa [drop, hst] using he
      have hfOld : s.dynamic.full_p st = true := by
        simpa [drop, hst] using hf
      exact hExclusive st ⟨heOld, hfOld⟩
  · unfold StoreEmptyOrFull
    intro st hstT
    by_cases hst : st = var_y
    · subst st
      exact Or.inl (drop_empty_p_eq1 var_x var_y s)
    · rcases hStoreTotal st hstT with he | hf
      · exact Or.inl (by simpa [drop, hst] using he)
      · exact Or.inr (by simpa [drop, hst] using hf)

lemma calibrate_preserves_wf
    (var_r var_i var_t var_w)
    (s : State)
    (hwf : WellFormed s)
    (hpre : calibratePre var_r var_i var_t var_w s) :
    WellFormed (calibrate var_r var_i var_t var_w s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hrT, hiT, htT, hwT, hEquipped, hTarget, hAt, hVisible, hOnBoard⟩
  refine
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, ?_, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, ?_, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  · unfold ValidCalibratedParam
    intro c r h
    change
      (calibrate var_r var_i var_t var_w s).dynamic.calibrated_p c r =
        true at h
    by_cases hm : c = var_i ∧ r = var_r
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨hiT, hrT⟩
    · have hOld : s.dynamic.calibrated_p c r = true := by
        simpa [calibrate, hm] using h
      exact hVCal c r hOld
  · unfold CalibratedImpliesOnBoardAndEquipped
    intro c r h
    change
      (calibrate var_r var_i var_t var_w s).dynamic.calibrated_p c r =
        true at h
    by_cases hm : c = var_i ∧ r = var_r
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨hOnBoard, hEquipped⟩
    · have hOld : s.dynamic.calibrated_p c r = true := by
        simpa [calibrate, hm] using h
      exact hCalInv c r hOld

lemma take_image_preserves_wf
    (var_r var_p var_o var_i var_m)
    (s : State)
    (hwf : WellFormed s)
    (hpre : take_imagePre var_r var_p var_o var_i var_m s) :
    WellFormed (take_image var_r var_p var_o var_i var_m s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hrT, hpT, hoT, hiT, hmT, hCalibrated, hOnBoard, hEquipped,
     hSupports, hVisible, hAt⟩
  refine
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, ?_, ?_,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, ?_, ?_, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, ?_⟩
  · unfold ValidCalibratedParam
    intro c r h
    change
      (take_image var_r var_p var_o var_i var_m s).dynamic.calibrated_p
          c r =
        true at h
    by_cases hm : c = var_i ∧ r = var_r
    · rcases hm with ⟨rfl, rfl⟩
      simp [take_image] at h
    · have hh :
          (¬c = var_i ∨ ¬r = var_r) ∧
            s.dynamic.calibrated_p c r = true := by
        simpa [take_image] using h
      exact hVCal c r hh.2
  · unfold ValidHaveImageParam
    intro r o m h
    change
      (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p
          r o m =
        true at h
    by_cases hmatch : r = var_r ∧ o = var_o ∧ m = var_m
    · rcases hmatch with ⟨rfl, rfl, rfl⟩
      exact ⟨hrT, hoT, hmT⟩
    · have hOld : s.dynamic.have_image_p r o m = true := by
        simpa [take_image, hmatch] using h
      exact hVImage r o m hOld
  · unfold CalibratedImpliesOnBoardAndEquipped
    intro c r h
    change
      (take_image var_r var_p var_o var_i var_m s).dynamic.calibrated_p
          c r =
        true at h
    by_cases hm : c = var_i ∧ r = var_r
    · rcases hm with ⟨rfl, rfl⟩
      simp [take_image] at h
    · have hh :
          (¬c = var_i ∨ ¬r = var_r) ∧
            s.dynamic.calibrated_p c r = true := by
        simpa [take_image] using h
      exact hCalInv c r hh.2
  · unfold HaveImageImpliesEquippedForImaging
    intro r o m h
    change
      (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p
          r o m =
        true at h
    by_cases hmatch : r = var_r ∧ o = var_o ∧ m = var_m
    · rcases hmatch with ⟨rfl, rfl, rfl⟩
      exact hEquipped
    · have hOld : s.dynamic.have_image_p r o m = true := by
        simpa [take_image, hmatch] using h
      exact hImageEquip r o m hOld
  · unfold CommunicatedImageImpliesHaveImage
    intro o m hc
    obtain ⟨r, hr⟩ := hCIHave o m hc
    refine ⟨r, ?_⟩
    change
      (take_image var_r var_p var_o var_i var_m s).dynamic.have_image_p
          r o m =
        true
    change s.dynamic.have_image_p r o m = true at hr
    by_cases hmatch : r = var_r ∧ o = var_o ∧ m = var_m
    · simp [take_image, hmatch]
    · simpa [take_image, hmatch] using hr

lemma communicate_soil_data_preserves_wf
    (var_r var_l var_p var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre :
      communicate_soil_dataPre var_r var_l var_p var_x var_y s) :
    WellFormed
      (communicate_soil_data var_r var_l var_p var_x var_y s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hrT, hlT, hpT, hxT, hyT, hAt, hLanderAt, hHave, hVisible⟩
  refine
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     ?_, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, ?_, hCRHave, hCIHave⟩
  · unfold ValidCommunicatedSoilDataParam
    intro p h
    change
      (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_soil_data_p p =
        true at h
    by_cases hp : p = var_p
    · subst p
      exact hpT
    · have hOld : s.dynamic.communicated_soil_data_p p = true := by
        simpa [communicate_soil_data, hp] using h
      exact hVCS p hOld
  · unfold CommunicatedSoilImpliesHaveSoilAnalysis
    intro p h
    change
      (communicate_soil_data var_r var_l var_p var_x var_y s).dynamic.communicated_soil_data_p p =
        true at h
    by_cases hp : p = var_p
    · subst p
      exact ⟨var_r, hHave⟩
    · have hOld : s.dynamic.communicated_soil_data_p p = true := by
        simpa [communicate_soil_data, hp] using h
      exact hCSHave p hOld

lemma communicate_rock_data_preserves_wf
    (var_r var_l var_p var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre :
      communicate_rock_dataPre var_r var_l var_p var_x var_y s) :
    WellFormed
      (communicate_rock_data var_r var_l var_p var_x var_y s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hrT, hlT, hpT, hxT, hyT, hAt, hLanderAt, hHave, hVisible⟩
  refine
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, ?_, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, ?_, hCIHave⟩
  · unfold ValidCommunicatedRockDataParam
    intro p h
    change
      (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_rock_data_p p =
        true at h
    by_cases hp : p = var_p
    · subst p
      exact hpT
    · have hOld : s.dynamic.communicated_rock_data_p p = true := by
        simpa [communicate_rock_data, hp] using h
      exact hVCR p hOld
  · unfold CommunicatedRockImpliesHaveRockAnalysis
    intro p h
    change
      (communicate_rock_data var_r var_l var_p var_x var_y s).dynamic.communicated_rock_data_p p =
        true at h
    by_cases hp : p = var_p
    · subst p
      exact ⟨var_r, hHave⟩
    · have hOld : s.dynamic.communicated_rock_data_p p = true := by
        simpa [communicate_rock_data, hp] using h
      exact hCRHave p hOld

lemma communicate_image_data_preserves_wf
    (var_r var_l var_o var_m var_x var_y)
    (s : State)
    (hwf : WellFormed s)
    (hpre :
      communicate_image_dataPre
        var_r var_l var_o var_m var_x var_y s) :
    WellFormed
      (communicate_image_data
        var_r var_l var_o var_m var_x var_y s) := by
  rcases hwf with
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, hVCI, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, hCIHave⟩
  rcases hpre with
    ⟨hrT, hlT, hoT, hmT, hxT, hyT, hAt, hLanderAt, hHave, hVisible⟩
  refine
    ⟨hWS, hVAt, hVEmpty, hVRock, hVSoil, hVFull, hVCal, hVImage,
     hVCS, hVCR, ?_, hVAtSoil, hVAtRock, hOneLoc, hExclusive,
     hSoilNo, hRockNo, hCalInv, hImageEquip, hSoilEquip, hRockEquip,
     hRoverLoc, hStoreTotal, hCSHave, hCRHave, ?_⟩
  · unfold ValidCommunicatedImageDataParam
    intro o m h
    change
      (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_image_data_p o m =
        true at h
    by_cases hm : o = var_o ∧ m = var_m
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨hoT, hmT⟩
    · have hOld : s.dynamic.communicated_image_data_p o m = true := by
        simpa [communicate_image_data, hm] using h
      exact hVCI o m hOld
  · unfold CommunicatedImageImpliesHaveImage
    intro o m h
    change
      (communicate_image_data var_r var_l var_o var_m var_x var_y s).dynamic.communicated_image_data_p o m =
        true at h
    by_cases hm : o = var_o ∧ m = var_m
    · rcases hm with ⟨rfl, rfl⟩
      exact ⟨var_r, hHave⟩
    · have hOld : s.dynamic.communicated_image_data_p o m = true := by
        simpa [communicate_image_data, hm] using h
      exact hCIHave o m hOld

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | navigate var_x var_y var_z =>
      exact navigate_preserves_wf var_x var_y var_z s hwf hpre
  | sample_soil var_x var_s var_p =>
      exact sample_soil_preserves_wf var_x var_s var_p s hwf hpre
  | sample_rock var_x var_s var_p =>
      exact sample_rock_preserves_wf var_x var_s var_p s hwf hpre
  | drop var_x var_y =>
      exact drop_preserves_wf var_x var_y s hwf hpre
  | calibrate var_r var_i var_t var_w =>
      exact calibrate_preserves_wf var_r var_i var_t var_w s hwf hpre
  | take_image var_r var_p var_o var_i var_m =>
      exact take_image_preserves_wf var_r var_p var_o var_i var_m s hwf hpre
  | communicate_soil_data var_r var_l var_p var_x var_y =>
      exact communicate_soil_data_preserves_wf var_r var_l var_p var_x var_y s hwf hpre
  | communicate_rock_data var_r var_l var_p var_x var_y =>
      exact communicate_rock_data_preserves_wf var_r var_l var_p var_x var_y s hwf hpre
  | communicate_image_data var_r var_l var_o var_m var_x var_y =>
      exact communicate_image_data_preserves_wf var_r var_l var_o var_m var_x var_y s hwf hpre

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
  Auxiliary predicates used to state the generalized-plan invariants.
-/

/--
`GPAccInv base acc` says that the plan stored in an accumulator is valid
from `base`, that the state stored in the accumulator is exactly the result
of executing that plan, and that the stored state is well formed.
-/
def GPAccInv
    (base : State)
    (acc : List PlanAction × State) : Prop :=
  ValidPlan acc.1 base ∧
  acc.2 = runPlan acc.1 base ∧
  WellFormed acc.2

/--
The fixed lander/mailbox choices made by `solve` are suitable for all
communication actions.
-/
def GPCommunicationSite
    (ss : StaticState)
    (mailbox lander landerWaypoint : Obj) : Prop :=
  ss.lander_t lander = true ∧
  ss.waypoint_t landerWaypoint = true ∧
  ss.waypoint_t mailbox = true ∧
  ss.at_lander_p lander landerWaypoint = true ∧
  ss.visible_p mailbox landerWaypoint = true

/--
The rover and store selected for soil tasks have all required static
properties.
-/
def GPSoilResource
    (ss : StaticState)
    (rover store : Obj) : Prop :=
  ss.rover_t rover = true ∧
  ss.store_t store = true ∧
  ss.equipped_for_soil_analysis_p rover = true ∧
  ss.store_of_p store rover = true

/--
The rover and store selected for rock tasks have all required static
properties.
-/
def GPRockResource
    (ss : StaticState)
    (rover store : Obj) : Prop :=
  ss.rover_t rover = true ∧
  ss.store_t store = true ∧
  ss.equipped_for_rock_analysis_p rover = true ∧
  ss.store_of_p store rover = true

/--
Every soil waypoint in `goals` has been communicated in `st`.
-/
def GPSoilDone
    (goals : List Obj)
    (st : State) : Prop :=
  ∀ w, w ∈ goals →
    st.dynamic.communicated_soil_data_p w = true

/--
Every rock waypoint in `goals` has been communicated in `st`.
-/
def GPRockDone
    (goals : List Obj)
    (st : State) : Prop :=
  ∀ w, w ∈ goals →
    st.dynamic.communicated_rock_data_p w = true

/--
Every requested objective/mode pair in `goals` has been communicated.
-/
def GPImageDone
    (goals : List (Obj × Obj))
    (st : State) : Prop :=
  ∀ q, q ∈ goals →
    st.dynamic.communicated_image_data_p q.1 q.2 = true

/--
The three communicated-data components of `st` cover every positive
communication literal occurring in `g`.
-/
def GPCoversGoalCommunications
    (st : State)
    (g : Goal) : Prop :=
  (∀ w,
    g.dynamic.communicated_soil_data_p w = some true →
    st.dynamic.communicated_soil_data_p w = true) ∧
  (∀ w,
    g.dynamic.communicated_rock_data_p w = some true →
    st.dynamic.communicated_rock_data_p w = true) ∧
  (∀ o m,
    g.dynamic.communicated_image_data_p o m = some true →
    st.dynamic.communicated_image_data_p o m = true)

/--
Navigation changes only `at_p`. This frame predicate records equality of
all other state components.
-/
def GPSameExceptAt
    (before after : State) : Prop :=
  after.statics = before.statics ∧
  after.dynamic.empty_p = before.dynamic.empty_p ∧
  after.dynamic.have_rock_analysis_p =
    before.dynamic.have_rock_analysis_p ∧
  after.dynamic.have_soil_analysis_p =
    before.dynamic.have_soil_analysis_p ∧
  after.dynamic.full_p = before.dynamic.full_p ∧
  after.dynamic.calibrated_p = before.dynamic.calibrated_p ∧
  after.dynamic.have_image_p = before.dynamic.have_image_p ∧
  after.dynamic.communicated_soil_data_p =
    before.dynamic.communicated_soil_data_p ∧
  after.dynamic.communicated_rock_data_p =
    before.dynamic.communicated_rock_data_p ∧
  after.dynamic.communicated_image_data_p =
    before.dynamic.communicated_image_data_p ∧
  after.dynamic.at_soil_sample_p =
    before.dynamic.at_soil_sample_p ∧
  after.dynamic.at_rock_sample_p =
    before.dynamic.at_rock_sample_p

/-!
  Part 1: generic object-selection lemmas.
-/

/--
If `gpFindObj? xs p` returns `x`, then `x` belongs to `xs` and satisfies
the Boolean predicate.
-/
lemma gpFindObj?_sound
    (xs : List Obj)
    (p : Obj → Bool)
    (x : Obj)
    (hfind : gpFindObj? xs p = some x) :
    x ∈ xs ∧ p x = true := by
  induction xs with
  | nil =>
      simp [gpFindObj?] at hfind
  | cons a rest ih =>
      cases hpa : p a with
      | false =>
          have hrest : gpFindObj? rest p = some x := by
            simpa [gpFindObj?, hpa] using hfind
          obtain ⟨hxmem, hpx⟩ := ih hrest
          exact ⟨by simp [hxmem], hpx⟩
      | true =>
          have hax : a = x := by
            simpa [gpFindObj?, hpa] using hfind
          subst x
          exact ⟨by simp, hpa⟩

/--
If some object in `xs` satisfies `p`, then `gpFindObj? xs p` succeeds.
-/
lemma gpFindObj?_complete
    (xs : List Obj)
    (p : Obj → Bool)
    (hex : ∃ x, x ∈ xs ∧ p x = true) :
    ∃ x, gpFindObj? xs p = some x := by
  induction xs with
  | nil =>
      rcases hex with ⟨x, hx, _⟩
      simp at hx
  | cons a rest ih =>
      cases hpa : p a with
      | true =>
          exact ⟨a, by simp [gpFindObj?, hpa]⟩
      | false =>
          rcases hex with ⟨x, hx, hpx⟩
          have hxrest : x ∈ rest := by
            have hxcases : x = a ∨ x ∈ rest := by
              simpa using hx
            rcases hxcases with hxa | hxr
            · subst x
              simp [hpa] at hpx
            · exact hxr
          obtain ⟨y, hy⟩ := ih ⟨x, hxrest, hpx⟩
          exact ⟨y, by simpa [gpFindObj?, hpa] using hy⟩

/--
When a satisfying object exists, `gpChooseObj` returns an object in the
input list which satisfies the predicate. Thus its default value `0` is
irrelevant under this hypothesis.
-/
lemma gpChooseObj_spec
    (xs : List Obj)
    (p : Obj → Bool)
    (hex : ∃ x, x ∈ xs ∧ p x = true) :
    gpChooseObj xs p ∈ xs ∧
    p (gpChooseObj xs p) = true := by
  obtain ⟨x, hfind⟩ := gpFindObj?_complete xs p hex
  have hsound : x ∈ xs ∧ p x = true :=
    gpFindObj?_sound xs p x hfind
  simpa [gpChooseObj, hfind] using hsound

/--
Soundness of `gpFirstSome`: a returned value was returned by `f` for some
element of the input list.
-/
lemma gpFirstSome_sound
    {α β : Type}
    (f : α → Option β)
    (xs : List α)
    (y : β)
    (h : gpFirstSome f xs = some y) :
    ∃ x, x ∈ xs ∧ f x = some y := by
  induction xs with
  | nil =>
      simp [gpFirstSome] at h
  | cons a rest ih =>
      cases hfa : f a with
      | none =>
          have hrest : gpFirstSome f rest = some y := by
            simpa [gpFirstSome, hfa] using h
          obtain ⟨x, hxmem, hfx⟩ := ih hrest
          exact ⟨x, by simp [hxmem], hfx⟩
      | some b =>
          have hby : b = y := by
            simpa [gpFirstSome, hfa] using h
          refine ⟨a, by simp, ?_⟩
          exact hfa.trans (congrArg some hby)

/--
Completeness of `gpFirstSome`: if `f` succeeds on an input-list member,
then `gpFirstSome f xs` also succeeds.
-/
lemma gpFirstSome_complete
    {α β : Type}
    (f : α → Option β)
    (xs : List α)
    (x : α)
    (y : β)
    (hx : x ∈ xs)
    (hf : f x = some y) :
    ∃ y', gpFirstSome f xs = some y' := by
  induction xs with
  | nil =>
      simp at hx
  | cons a rest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hxrest
      · exact ⟨y, by simp [gpFirstSome, hf]⟩
      · cases hfa : f a with
        | none =>
            obtain ⟨y', hy'⟩ := ih hxrest
            exact ⟨y', by simpa [gpFirstSome, hfa] using hy'⟩
        | some b =>
            exact ⟨b, by simp [gpFirstSome, hfa]⟩

/-!
  Part 2: correctness of the fixed choices and request lists.
-/

/--
A nontrivial reflexive-transitive path has a final edge into its target.
-/
lemma reflTransGen_has_last_of_ne
    {α : Type}
    {r : α → α → Prop}
    {a b : α}
    (hpath : Relation.ReflTransGen r a b)
    (hne : a ≠ b) :
    ∃ x, r x b := by
  cases hpath with
  | refl =>
      exact (hne rfl).elim
  | tail hprefix hedge =>
      exact ⟨_, hedge⟩

/--
The lander, lander waypoint and mailbox selected exactly as in `solve`
form a valid communication site.

The main static argument here is:
* the unique lander exists and belongs to `objects`;
* it has a location;
* since there are at least two waypoints and the visible graph is
  connected, some waypoint is directly visible to the lander waypoint.
-/
lemma gpCommunicationSite_spec
    (s : State)
    (hstatic : WellFormedStatic s.statics) :
    let objects := s.statics.objects
    let lander :=
      gpChooseObj objects (fun candidate =>
        s.statics.lander_t candidate)
    let landerWaypoint :=
      gpChooseObj objects (fun waypoint =>
        s.statics.at_lander_p lander waypoint)
    let mailbox :=
      gpChooseObj objects (fun waypoint =>
        s.statics.visible_p waypoint landerWaypoint)
    GPCommunicationSite
      s.statics mailbox lander landerWaypoint := by
  let objects := s.statics.objects
  let lander :=
    gpChooseObj objects (fun candidate =>
      s.statics.lander_t candidate)
  let landerWaypoint :=
    gpChooseObj objects (fun waypoint =>
      s.statics.at_lander_p lander waypoint)
  let mailbox :=
    gpChooseObj objects (fun waypoint =>
      s.statics.visible_p waypoint landerWaypoint)

  change
    GPCommunicationSite
      s.statics mailbox lander landerWaypoint

  rcases hstatic with
    ⟨_, hAtLanderValid, _, _, _, _, _, hVisibleValid, _, _, _, _,
     hTypes, _, hMin, hUnique, _, _, _, _, _, hLanderLoc, _, _, _, _,
     _, _, _, _, hVisibleConn, _, _, _⟩

  have hWaypointMem :
      ∀ x, s.statics.waypoint_t x = true → x ∈ objects := by
    intro x hx
    simpa [objects] using hTypes.2.1 x hx

  have hLanderMem :
      ∀ x, s.statics.lander_t x = true → x ∈ objects := by
    intro x hx
    simpa [objects] using hTypes.2.2.2.2.2.1 x hx

  obtain ⟨someLander, hSomeLanderT, _⟩ := hUnique

  have hLanderExists :
      ∃ l, l ∈ objects ∧ s.statics.lander_t l = true := by
    exact
      ⟨someLander,
       hLanderMem someLander hSomeLanderT,
       hSomeLanderT⟩

  have hLanderChoice :=
    gpChooseObj_spec
      objects
      (fun candidate => s.statics.lander_t candidate)
      hLanderExists

  have hLanderT :
      s.statics.lander_t lander = true := by
    simpa [lander] using hLanderChoice.2

  obtain ⟨someLanderWaypoint, hSomeLanderAt⟩ :=
    hLanderLoc lander hLanderT

  have hSomeLanderWaypointT :
      s.statics.waypoint_t someLanderWaypoint = true :=
    (hAtLanderValid
      lander someLanderWaypoint hSomeLanderAt).2

  have hLanderWaypointExists :
      ∃ w,
        w ∈ objects ∧
        s.statics.at_lander_p lander w = true := by
    exact
      ⟨someLanderWaypoint,
       hWaypointMem someLanderWaypoint hSomeLanderWaypointT,
       hSomeLanderAt⟩

  have hLanderWaypointChoice :=
    gpChooseObj_spec
      objects
      (fun waypoint =>
        s.statics.at_lander_p lander waypoint)
      hLanderWaypointExists

  have hAtLander :
      s.statics.at_lander_p lander landerWaypoint = true := by
    simpa [landerWaypoint] using hLanderWaypointChoice.2

  have hLanderWaypointT :
      s.statics.waypoint_t landerWaypoint = true :=
    (hAtLanderValid lander landerWaypoint hAtLander).2

  obtain ⟨w₁, w₂, hw₁T, hw₂T, hw₁₂⟩ := hMin.2.1

  have hOtherWaypoint :
      ∃ w,
        s.statics.waypoint_t w = true ∧
        w ≠ landerWaypoint := by
    by_cases hw₁ : w₁ = landerWaypoint
    · refine ⟨w₂, hw₂T, ?_⟩
      intro hw₂
      apply hw₁₂
      exact hw₁.trans hw₂.symm
    · exact ⟨w₁, hw₁T, hw₁⟩

  obtain ⟨otherWaypoint, hOtherWaypointT, hOtherNe⟩ :=
    hOtherWaypoint

  have hVisiblePath :
      Relation.ReflTransGen
        (fun a b => s.statics.visible_p a b = true)
        otherWaypoint landerWaypoint :=
    hVisibleConn
      otherWaypoint landerWaypoint
      hOtherWaypointT hLanderWaypointT

  obtain ⟨someMailbox, hSomeMailboxVisible⟩ :=
    reflTransGen_has_last_of_ne hVisiblePath hOtherNe

  have hSomeMailboxT :
      s.statics.waypoint_t someMailbox = true :=
    (hVisibleValid
      someMailbox landerWaypoint hSomeMailboxVisible).1

  have hMailboxExists :
      ∃ w,
        w ∈ objects ∧
        s.statics.visible_p w landerWaypoint = true := by
    exact
      ⟨someMailbox,
       hWaypointMem someMailbox hSomeMailboxT,
       hSomeMailboxVisible⟩

  have hMailboxChoice :=
    gpChooseObj_spec
      objects
      (fun waypoint =>
        s.statics.visible_p waypoint landerWaypoint)
      hMailboxExists

  have hMailboxVisible :
      s.statics.visible_p mailbox landerWaypoint = true := by
    simpa [mailbox] using hMailboxChoice.2

  have hMailboxT :
      s.statics.waypoint_t mailbox = true :=
    (hVisibleValid
      mailbox landerWaypoint hMailboxVisible).1

  unfold GPCommunicationSite
  exact
    ⟨hLanderT,
     hLanderWaypointT,
     hMailboxT,
     hAtLander,
     hMailboxVisible⟩

/--
If an equipped soil rover exists, the rover/store choices made by `solve`
form a valid soil resource.
-/
lemma gpSoilResource_spec
    (s : State)
    (hstatic : WellFormedStatic s.statics)
    (hex :
      ∃ r, s.statics.equipped_for_soil_analysis_p r = true) :
    let objects := s.statics.objects
    let rover :=
      gpChooseObj objects (fun r =>
        s.statics.equipped_for_soil_analysis_p r)
    let store :=
      gpChooseObj objects (fun st =>
        s.statics.store_of_p st rover)
    GPSoilResource s.statics rover store := by
  let objects := s.statics.objects
  let rover :=
    gpChooseObj objects (fun r =>
      s.statics.equipped_for_soil_analysis_p r)
  let store :=
    gpChooseObj objects (fun st =>
      s.statics.store_of_p st rover)

  change GPSoilResource s.statics rover store

  rcases hstatic with
    ⟨_, _, _, hEquipValid, _, _, _, _, _, hStoreValid, _, _, hTypes,
     _, _, _, _, _, hRoverHasStore, _, _, _, _, _, _, _, _, _, _, _,
     _, _, _, _⟩

  obtain ⟨someRover, hSomeRoverEquipped⟩ := hex

  have hSomeRoverT :
      s.statics.rover_t someRover = true :=
    hEquipValid someRover hSomeRoverEquipped

  have hSomeRoverMem :
      someRover ∈ objects := by
    simpa [objects] using hTypes.1 someRover hSomeRoverT

  have hRoverExists :
      ∃ r,
        r ∈ objects ∧
        s.statics.equipped_for_soil_analysis_p r = true :=
    ⟨someRover, hSomeRoverMem, hSomeRoverEquipped⟩

  have hRoverChoice :=
    gpChooseObj_spec
      objects
      (fun r => s.statics.equipped_for_soil_analysis_p r)
      hRoverExists

  have hRoverEquipped :
      s.statics.equipped_for_soil_analysis_p rover = true := by
    simpa [rover] using hRoverChoice.2

  have hRoverT :
      s.statics.rover_t rover = true :=
    hEquipValid rover hRoverEquipped

  obtain ⟨someStore, hSomeStoreOf⟩ :=
    hRoverHasStore rover hRoverT

  have hSomeStoreT :
      s.statics.store_t someStore = true :=
    (hStoreValid someStore rover hSomeStoreOf).1

  have hSomeStoreMem :
      someStore ∈ objects := by
    simpa [objects] using hTypes.2.2.1 someStore hSomeStoreT

  have hStoreExists :
      ∃ st,
        st ∈ objects ∧
        s.statics.store_of_p st rover = true :=
    ⟨someStore, hSomeStoreMem, hSomeStoreOf⟩

  have hStoreChoice :=
    gpChooseObj_spec
      objects
      (fun st => s.statics.store_of_p st rover)
      hStoreExists

  have hStoreOf :
      s.statics.store_of_p store rover = true := by
    simpa [store] using hStoreChoice.2

  have hStoreT :
      s.statics.store_t store = true :=
    (hStoreValid store rover hStoreOf).1

  unfold GPSoilResource
  exact ⟨hRoverT, hStoreT, hRoverEquipped, hStoreOf⟩

/--
If an equipped rock rover exists, the rover/store choices made by `solve`
form a valid rock resource.
-/
lemma gpRockResource_spec
    (s : State)
    (hstatic : WellFormedStatic s.statics)
    (hex :
      ∃ r, s.statics.equipped_for_rock_analysis_p r = true) :
    let objects := s.statics.objects
    let rover :=
      gpChooseObj objects (fun r =>
        s.statics.equipped_for_rock_analysis_p r)
    let store :=
      gpChooseObj objects (fun st =>
        s.statics.store_of_p st rover)
    GPRockResource s.statics rover store := by
  let objects := s.statics.objects
  let rover :=
    gpChooseObj objects (fun r =>
      s.statics.equipped_for_rock_analysis_p r)
  let store :=
    gpChooseObj objects (fun st =>
      s.statics.store_of_p st rover)

  change GPRockResource s.statics rover store

  rcases hstatic with
    ⟨_, _, _, _, hEquipValid, _, _, _, _, hStoreValid, _, _, hTypes,
     _, _, _, _, _, hRoverHasStore, _, _, _, _, _, _, _, _, _, _, _,
     _, _, _, _⟩

  obtain ⟨someRover, hSomeRoverEquipped⟩ := hex

  have hSomeRoverT :
      s.statics.rover_t someRover = true :=
    hEquipValid someRover hSomeRoverEquipped

  have hSomeRoverMem :
      someRover ∈ objects := by
    simpa [objects] using hTypes.1 someRover hSomeRoverT

  have hRoverExists :
      ∃ r,
        r ∈ objects ∧
        s.statics.equipped_for_rock_analysis_p r = true :=
    ⟨someRover, hSomeRoverMem, hSomeRoverEquipped⟩

  have hRoverChoice :=
    gpChooseObj_spec
      objects
      (fun r => s.statics.equipped_for_rock_analysis_p r)
      hRoverExists

  have hRoverEquipped :
      s.statics.equipped_for_rock_analysis_p rover = true := by
    simpa [rover] using hRoverChoice.2

  have hRoverT :
      s.statics.rover_t rover = true :=
    hEquipValid rover hRoverEquipped

  obtain ⟨someStore, hSomeStoreOf⟩ :=
    hRoverHasStore rover hRoverT

  have hSomeStoreT :
      s.statics.store_t someStore = true :=
    (hStoreValid someStore rover hSomeStoreOf).1

  have hSomeStoreMem :
      someStore ∈ objects := by
    simpa [objects] using hTypes.2.2.1 someStore hSomeStoreT

  have hStoreExists :
      ∃ st,
        st ∈ objects ∧
        s.statics.store_of_p st rover = true :=
    ⟨someStore, hSomeStoreMem, hSomeStoreOf⟩

  have hStoreChoice :=
    gpChooseObj_spec
      objects
      (fun st => s.statics.store_of_p st rover)
      hStoreExists

  have hStoreOf :
      s.statics.store_of_p store rover = true := by
    simpa [store] using hStoreChoice.2

  have hStoreT :
      s.statics.store_t store = true :=
    (hStoreValid store rover hStoreOf).1

  unfold GPRockResource
  exact ⟨hRoverT, hStoreT, hRoverEquipped, hStoreOf⟩

/--
Soundness of soil request enumeration.
-/
lemma gpRequestedSoilWaypoints_sound
    (s : State)
    (g : Goal)
    (w : Obj)
    (hw : w ∈ gpRequestedSoilWaypoints s g) :
    g.dynamic.communicated_soil_data_p w = some true := by
  have hmem :
      w ∈ s.statics.objects.filter (fun waypoint =>
        gpIsSomeTrue
          (g.dynamic.communicated_soil_data_p waypoint)) := by
    simpa only [gpRequestedSoilWaypoints] using hw

  have htrue :
      gpIsSomeTrue
        (g.dynamic.communicated_soil_data_p w) = true :=
    (List.mem_filter.mp hmem).2

  cases hopt : g.dynamic.communicated_soil_data_p w with
  | none =>
      simp [gpIsSomeTrue, hopt] at htrue
  | some b =>
      cases b with
      | false =>
          simp [gpIsSomeTrue, hopt] at htrue
      | true =>
          rfl

lemma gpRequestedSoilWaypoints_complete
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (w : Obj)
    (hw :
      g.dynamic.communicated_soil_data_p w = some true) :
    w ∈ gpRequestedSoilWaypoints s g := by
  rcases hgoal with
    ⟨hstatic, _, _, _, _, _, _, _, hVCS, _⟩
  rcases hstatic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hTypes, _⟩

  have hwT : s.statics.waypoint_t w = true := by
    apply hVCS w
    exact hw

  have hwMem : w ∈ s.statics.objects :=
    hTypes.2.1 w hwT

  unfold gpRequestedSoilWaypoints
  exact List.mem_filter.mpr
    ⟨hwMem, by simp [gpIsSomeTrue, hw]⟩

/--
The soil request list contains no duplicates.
-/
lemma gpRequestedSoilWaypoints_nodup
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics) :
    (gpRequestedSoilWaypoints s g).Nodup := by
  have hobjects : s.statics.objects.Nodup := by
    exact hstatic.1
  unfold gpRequestedSoilWaypoints
  exact hobjects.filter _

/--
Soundness of rock request enumeration.
-/
lemma gpRequestedRockWaypoints_sound
    (s : State)
    (g : Goal)
    (w : Obj)
    (hw : w ∈ gpRequestedRockWaypoints s g) :
    g.dynamic.communicated_rock_data_p w = some true := by
  have hmem :
      w ∈ s.statics.objects.filter (fun waypoint =>
        gpIsSomeTrue
          (g.dynamic.communicated_rock_data_p waypoint)) := by
    simpa only [gpRequestedRockWaypoints] using hw

  have htrue :
      gpIsSomeTrue
        (g.dynamic.communicated_rock_data_p w) = true :=
    (List.mem_filter.mp hmem).2

  cases hopt : g.dynamic.communicated_rock_data_p w with
  | none =>
      simp [gpIsSomeTrue, hopt] at htrue
  | some b =>
      cases b with
      | false =>
          simp [gpIsSomeTrue, hopt] at htrue
      | true =>
          rfl

/--
Completeness of rock request enumeration.
-/
lemma gpRequestedRockWaypoints_complete
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (w : Obj)
    (hw :
      g.dynamic.communicated_rock_data_p w = some true) :
    w ∈ gpRequestedRockWaypoints s g := by
  rcases hgoal with
    ⟨hstatic, _, _, _, _, _, _, _, _, hVCR, _⟩
  rcases hstatic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hTypes, _⟩

  have hwT : s.statics.waypoint_t w = true := by
    apply hVCR w
    exact hw

  have hwMem : w ∈ s.statics.objects :=
    hTypes.2.1 w hwT

  unfold gpRequestedRockWaypoints
  exact List.mem_filter.mpr
    ⟨hwMem, by simp [gpIsSomeTrue, hw]⟩

/--
The rock request list contains no duplicates.
-/
lemma gpRequestedRockWaypoints_nodup
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics) :
    (gpRequestedRockWaypoints s g).Nodup := by
  have hobjects : s.statics.objects.Nodup := by
    exact hstatic.1
  unfold gpRequestedRockWaypoints
  exact hobjects.filter _

/--
Soundness of image request enumeration, including the static types needed
by `gpImageTask`.
-/
lemma gpRequestedImages_sound
    (s : State)
    (g : Goal)
    (o m : Obj)
    (hmem : (o, m) ∈ gpRequestedImages s g)
    (hgoal : WellFormedGoal s g) :
    g.dynamic.communicated_image_data_p o m = some true ∧
    s.statics.objective_t o = true ∧
    s.statics.mode_t m = true := by
  unfold gpRequestedImages at hmem
  simp only [List.mem_flatMap] at hmem
  obtain ⟨o', ho'mem, hpairmem⟩ := hmem

  simp only [List.mem_filterMap] at hpairmem
  obtain ⟨m', hm'mem, hfilter⟩ := hpairmem

  cases hrequested :
      gpIsSomeTrue
        (g.dynamic.communicated_image_data_p o' m') with
  | false =>
      simp [hrequested] at hfilter
  | true =>
      have hpairs : (o', m') = (o, m) := by
        simpa [hrequested] using hfilter

      have ho : o' = o :=
        congrArg Prod.fst hpairs
      have hm : m' = m :=
        congrArg Prod.snd hpairs
      subst o'
      subst m'

      have hrequest :
          g.dynamic.communicated_image_data_p o m = some true := by
        cases hopt :
            g.dynamic.communicated_image_data_p o m with
        | none =>
            simp [gpIsSomeTrue, hopt] at hrequested
        | some b =>
            cases b with
            | false =>
                simp [gpIsSomeTrue, hopt] at hrequested
            | true =>
                rfl

      rcases hgoal with
        ⟨_, _, _, _, _, _, _, _, _, _, hValidImageCommunication, _⟩

      have htypes :
          s.statics.objective_t o = true ∧
          s.statics.mode_t m = true :=
        hValidImageCommunication o m hrequest

      exact ⟨hrequest, htypes.1, htypes.2⟩

/--
Completeness of image request enumeration.
-/
lemma gpRequestedImages_complete
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (o m : Obj)
    (hreq :
      g.dynamic.communicated_image_data_p o m = some true) :
    (o, m) ∈ gpRequestedImages s g := by
  rcases hgoal with
    ⟨hstatic, _, _, _, _, _, _, _, _, _, hValidImageCommunication, _⟩

  have htypes :
      s.statics.objective_t o = true ∧
      s.statics.mode_t m = true :=
    hValidImageCommunication o m hreq

  rcases hstatic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hTypeHierarchy, _⟩

  have hoMem : o ∈ s.statics.objects :=
    hTypeHierarchy.2.2.2.2.2.2.1 o htypes.1

  have hmMem : m ∈ s.statics.objects :=
    hTypeHierarchy.2.2.2.2.1 m htypes.2

  unfold gpRequestedImages
  simp only [List.mem_flatMap]
  refine ⟨o, hoMem, ?_⟩
  simp only [List.mem_filterMap]
  refine ⟨m, hmMem, ?_⟩
  simp [gpIsSomeTrue, hreq]

/--
A list obtained by optionally mapping each distinct object `m` to the pair
`(o, m)` contains no duplicates.
-/
lemma gpPairFilterMap_nodup
    (xs : List Obj)
    (p : Obj → Bool)
    (o : Obj)
    (hxs : xs.Nodup) :
    (xs.filterMap (fun m =>
      if p m then some (o, m) else none)).Nodup := by
  induction xs with
  | nil =>
      simp
  | cons x rest ih =>
      have hxrest : x ∉ rest :=
        (List.nodup_cons.mp hxs).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hxs).2
      cases hpx : p x with
      | false =>
          simpa [hpx] using ih hrestNodup
      | true =>
          simp only [List.filterMap_cons, hpx, if_true]
          refine List.nodup_cons.mpr ⟨?_, ih hrestNodup⟩
          intro hmem
          simp only [List.mem_filterMap] at hmem
          obtain ⟨y, hyrest, hout⟩ := hmem
          cases hpy : p y with
          | false =>
              simp [hpy] at hout
          | true =>
              have heq : (o, y) = (o, x) := by
                simpa [hpy] using hout
              have hyx : y = x :=
                congrArg Prod.snd heq
              exact hxrest (hyx ▸ hyrest)

/--
Every pair produced by the image-request `filterMap` has the fixed first
component used for that invocation.
-/
lemma gpPairFilterMap_mem_fst
    (xs : List Obj)
    (p : Obj → Bool)
    (o : Obj)
    (q : Obj × Obj)
    (hq :
      q ∈ xs.filterMap (fun m =>
        if p m then some (o, m) else none)) :
    q.1 = o := by
  simp only [List.mem_filterMap] at hq
  obtain ⟨m, _, hout⟩ := hq
  cases hpm : p m with
  | false =>
      simp [hpm] at hout
  | true =>
      have heq : (o, m) = q := by
        simpa [hpm] using hout
      exact (congrArg Prod.fst heq).symm

/--
Flat-mapping distinct outer objects to pairs whose first component is that
outer object preserves duplicate-freedom, provided the mode list is also
duplicate-free.
-/
lemma gpPairFlatMap_nodup
    (objectives modes : List Obj)
    (p : Obj → Obj → Bool)
    (hObjectives : objectives.Nodup)
    (hModes : modes.Nodup) :
    (objectives.flatMap (fun o =>
      modes.filterMap (fun m =>
        if p o m then some (o, m) else none))).Nodup := by
  induction objectives with
  | nil =>
      simp
  | cons o rest ih =>
      have hoRest : o ∉ rest :=
        (List.nodup_cons.mp hObjectives).1
      have hRestNodup : rest.Nodup :=
        (List.nodup_cons.mp hObjectives).2

      simp only [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨?_, ?_, ?_⟩
      · exact gpPairFilterMap_nodup modes (p o) o hModes
      · exact ih hRestNodup
      · intro q hqHead q' hqRest hqq'
        obtain ⟨o', ho'Rest, hq'Inner⟩ :=
          List.mem_flatMap.mp hqRest

        have hqFstO : q.1 = o :=
          gpPairFilterMap_mem_fst modes (p o) o q hqHead
        have hq'FstO' : q'.1 = o' :=
          gpPairFilterMap_mem_fst modes (p o') o' q' hq'Inner

        have hqFstEq : q.1 = q'.1 :=
          congrArg Prod.fst hqq'

        have hoo' : o = o' :=
          hqFstO.symm.trans (hqFstEq.trans hq'FstO')

        exact hoRest (hoo'.symm ▸ ho'Rest)

/--
The image request list contains no duplicate objective/mode pairs.
-/
lemma gpRequestedImages_nodup
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics) :
    (gpRequestedImages s g).Nodup := by
  have hobjects : s.statics.objects.Nodup :=
    hstatic.1
  unfold gpRequestedImages
  exact
    gpPairFlatMap_nodup
      s.statics.objects
      s.statics.objects
      (fun objective mode =>
        gpIsSomeTrue
          (g.dynamic.communicated_image_data_p objective mode))
      hobjects
      hobjects

/--
A nonempty soil request list implies that the conditional solvability
assumption in `WellFormedGoal` supplies an equipped soil rover.
-/
lemma soil_requests_have_equipped_rover
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (hne : gpRequestedSoilWaypoints s g ≠ []) :
    ∃ r, s.statics.equipped_for_soil_analysis_p r = true := by
  have hsolv : GoalCommunicatedSoilOnlySolvable s g := by
    rcases hgoal with
      ⟨_, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, hsolv, _⟩
    exact hsolv

  unfold GoalCommunicatedSoilOnlySolvable at hsolv

  cases hrequests : gpRequestedSoilWaypoints s g with
  | nil =>
      exact (hne hrequests).elim
  | cons w rest =>
      have hwmem : w ∈ gpRequestedSoilWaypoints s g := by
        rw [hrequests]
        simp
      have hwreq :
          g.dynamic.communicated_soil_data_p w = some true :=
        gpRequestedSoilWaypoints_sound s g w hwmem
      exact hsolv ⟨w, hwreq⟩

/--
A nonempty rock request list implies that an equipped rock rover exists.
-/
lemma rock_requests_have_equipped_rover
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (hne : gpRequestedRockWaypoints s g ≠ []) :
    ∃ r, s.statics.equipped_for_rock_analysis_p r = true := by
  have hsolv : GoalCommunicatedRockOnlySolvable s g := by
    rcases hgoal with
      ⟨_, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, hsolv, _⟩
    exact hsolv

  unfold GoalCommunicatedRockOnlySolvable at hsolv

  cases hrequests : gpRequestedRockWaypoints s g with
  | nil =>
      exact (hne hrequests).elim
  | cons w rest =>
      have hwmem : w ∈ gpRequestedRockWaypoints s g := by
        rw [hrequests]
        simp
      have hwreq :
          g.dynamic.communicated_rock_data_p w = some true :=
        gpRequestedRockWaypoints_sound s g w hwmem
      exact hsolv ⟨w, hwreq⟩

/--
Every requested soil waypoint initially contains a soil sample.
-/
lemma requested_soil_samples_initially_present
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g) :
    ∀ w, w ∈ gpRequestedSoilWaypoints s g →
      s.dynamic.at_soil_sample_p w = true := by
  intro w hw

  have hreq :
      g.dynamic.communicated_soil_data_p w = some true :=
    gpRequestedSoilWaypoints_sound s g w hw

  have hsample :
      GoalCommunicatedSoilImpliesSampleAtWaypoint s g := by
    rcases hgoal with
      ⟨_, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, hsample, _⟩
    exact hsample

  exact hsample w hreq

/--
Every requested rock waypoint initially contains a rock sample.
-/
lemma requested_rock_samples_initially_present
    (s : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g) :
    ∀ w, w ∈ gpRequestedRockWaypoints s g →
      s.dynamic.at_rock_sample_p w = true := by
  intro w hw

  have hreq :
      g.dynamic.communicated_rock_data_p w = some true :=
    gpRequestedRockWaypoints_sound s g w hw

  have hsample :
      GoalCommunicatedRockImpliesSampleAtWaypoint s g := by
    rcases hgoal with
      ⟨_, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, _, _, _,
       _, _, _, _, _, _, _, hsample⟩
    exact hsample

  exact hsample w hreq

/-!
  Part 3: navigation.
-/

/--
`gpRoverLocation` selects the actual unique location of a typed rover.
-/
lemma gpRoverLocation_spec
    (s : State)
    (rover : Obj)
    (hwf : WellFormed s)
    (hr : s.statics.rover_t rover = true) :
    gpRoverLocation s rover ∈ s.statics.objects ∧
    s.statics.waypoint_t (gpRoverLocation s rover) = true ∧
    s.dynamic.at_p rover (gpRoverLocation s rover) = true := by
  rcases hwf with
    ⟨hstatic, hVAt, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
     _, _, _, hRoverLoc, _, _, _, _⟩

  rcases hstatic with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hTypes, _⟩

  obtain ⟨w, hwAt⟩ := hRoverLoc rover hr

  have hwT : s.statics.waypoint_t w = true :=
    (hVAt rover w hwAt).2

  have hwMem : w ∈ s.statics.objects :=
    hTypes.2.1 w hwT

  have hchoice :=
    gpChooseObj_spec
      s.statics.objects
      (fun waypoint => s.dynamic.at_p rover waypoint)
      ⟨w, hwMem, hwAt⟩

  have hchosenMem :
      gpRoverLocation s rover ∈ s.statics.objects := by
    simpa only [gpRoverLocation] using hchoice.1

  have hchosenAt :
      s.dynamic.at_p rover (gpRoverLocation s rover) = true := by
    simpa only [gpRoverLocation] using hchoice.2

  have hchosenT :
      s.statics.waypoint_t (gpRoverLocation s rover) = true :=
    (hVAt rover (gpRoverLocation s rover) hchosenAt).2

  exact ⟨hchosenMem, hchosenT, hchosenAt⟩

/--
A route stores the waypoints following its initial waypoint.  Thus the
empty route starts and ends at the same object, while `cons` prepends one
edge to an existing route.
-/
inductive GPRoute {α : Type} (r : α → α → Prop) :
    α → List α → α → Prop
  | nil (a : α) :
      GPRoute r a [] a
  | cons {a b t : α} {tail : List α}
      (hab : r a b)
      (hrest : GPRoute r b tail t) :
      GPRoute r a (b :: tail) t

/--
Appending one edge to the end of a route produces a route to the edge's
target.
-/
lemma gpRoute_append_edge
    {α : Type}
    {r : α → α → Prop}
    {a b c : α}
    {xs : List α}
    (hroute : GPRoute r a xs b)
    (hedge : r b c) :
    GPRoute r a (xs ++ [c]) c := by
  induction hroute with
  | nil =>
      exact GPRoute.cons hedge (GPRoute.nil c)
  | cons hab hrest ih =>
      exact GPRoute.cons hab (ih hedge)

/--
Every reflexive-transitive path can be represented as a `GPRoute`.
-/
lemma gpRoute_of_reflTransGen
    {α : Type}
    {r : α → α → Prop}
    {a b : α}
    (hpath : Relation.ReflTransGen r a b) :
    ∃ xs, GPRoute r a xs b := by
  induction hpath with
  | refl =>
      exact ⟨[], GPRoute.nil a⟩
  | tail hprefix hedge ih =>
      obtain ⟨xs, hroute⟩ := ih
      exact ⟨xs ++ [_], gpRoute_append_edge hroute hedge⟩

/--
If an object occurs in the tail of a route, the suffix beginning at that
occurrence is itself a route to the original target.
-/
lemma gpRoute_suffix_of_mem
    {α : Type}
    {r : α → α → Prop}
    {a t x : α}
    {tail : List α}
    (hroute : GPRoute r a tail t)
    (hx : x ∈ tail) :
    ∃ suffix, GPRoute r x suffix t := by
  induction hroute with
  | nil =>
      simp at hx
  | cons hab hrest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨_, hrest⟩
      · exact ih hx

/--
If an object occurs in the tail of a route, the suffix beginning at that
occurrence is strictly shorter than the original tail and remains a route
to the same target.
-/
lemma gpRoute_suffix_of_mem_shorter
    {α : Type}
    {r : α → α → Prop}
    {a t x : α}
    {tail : List α}
    (hroute : GPRoute r a tail t)
    (hx : x ∈ tail) :
    ∃ suffix,
      GPRoute r x suffix t ∧
      suffix.length < tail.length := by
  induction hroute with
  | nil =>
      simp at hx
  | @cons a b t tail hab hrest ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · refine ⟨tail, hrest, ?_⟩
        simp
      · obtain ⟨suffix, hsuffix, hlength⟩ := ih hx
        refine ⟨suffix, hsuffix, ?_⟩
        exact lt_trans hlength (by simp)

/--
A route containing a repeated object can be shortened while preserving
its endpoints.
-/
lemma gpRoute_loop_shorter
    {α : Type}
    {r : α → α → Prop}
    {a t : α}
    {tail : List α}
    (hroute : GPRoute r a tail t)
    (hnotNodup : ¬(a :: tail).Nodup) :
    ∃ shorter,
      GPRoute r a shorter t ∧
      shorter.length < tail.length := by
  induction hroute with
  | nil =>
      simp at hnotNodup
  | @cons a b t tail hab hrest ih =>
      by_cases ha : a ∈ b :: tail
      · obtain ⟨shorter, hshorterRoute, hshorterLength⟩ :=
          gpRoute_suffix_of_mem_shorter
            (GPRoute.cons hab hrest)
            ha
        exact ⟨shorter, hshorterRoute, hshorterLength⟩
      · have htailNotNodup : ¬(b :: tail).Nodup := by
          intro htailNodup
          apply hnotNodup
          exact List.nodup_cons.mpr ⟨ha, htailNodup⟩
        obtain ⟨shorter, hshorterRoute, hshorterLength⟩ :=
          ih htailNotNodup
        refine
          ⟨b :: shorter,
           GPRoute.cons hab hshorterRoute,
           ?_⟩
        simpa only [List.length_cons] using
          Nat.succ_lt_succ hshorterLength

/--
Strong-induction helper used to remove all loops from a route.
-/
lemma gpRoute_simple_exists_aux
    {α : Type}
    {r : α → α → Prop}
    {a t : α}
    (n : Nat) :
    ∀ tail,
      tail.length = n →
      GPRoute r a tail t →
      ∃ simple,
        GPRoute r a simple t ∧
        (a :: simple).Nodup := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro tail hlength hroute
      by_cases hnodup : (a :: tail).Nodup
      · exact ⟨tail, hroute, hnodup⟩
      · obtain ⟨shorter, hshorterRoute, hshorterLength⟩ :=
          gpRoute_loop_shorter hroute hnodup
        exact
          ih shorter.length
            (by omega)
            shorter
            rfl
            hshorterRoute

/--
Every route can be shortened to a route containing no repeated objects.
-/
lemma gpRoute_simple_exists
    {α : Type}
    {r : α → α → Prop}
    {a t : α}
    {tail : List α}
    (hroute : GPRoute r a tail t) :
    ∃ simple,
      GPRoute r a simple t ∧
      (a :: simple).Nodup := by
  exact
    gpRoute_simple_exists_aux tail.length tail rfl hroute

/--
All waypoints in a navigable route belong to the static object list.
-/
lemma gpNavigableRoute_nodes_mem
    (ss : StaticState)
    (rover start target : Obj)
    (tail : List Obj)
    (hCanValid : ValidCanTraverseParam ss)
    (hTypes : ValidTypeHierarchy ss)
    (hStartT : ss.waypoint_t start = true)
    (hroute :
      GPRoute
        (fun a b =>
          ss.can_traverse_p rover a b = true ∧
          ss.visible_p a b = true)
        start tail target) :
    ∀ x, x ∈ start :: tail → x ∈ ss.objects := by
  induction hroute with
  | nil =>
      intro x hx
      simp only [List.mem_singleton] at hx
      subst x
      exact hTypes.2.1 _ hStartT
  | @cons a b t rest hedge hrest ih =>
      have hbT : ss.waypoint_t b = true :=
        (hCanValid rover _ b hedge.1).2.2
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hxrest
      · exact hTypes.2.1 _ hStartT
      · exact ih hbT x hxrest

/--
The DFS succeeds whenever it is supplied with a simple navigable route
whose remaining waypoints are fresh with respect to `visited` and whose
length fits within the available fuel.
-/
lemma gpNavDfs_succeeds_of_route
    (ss : StaticState)
    (rover target : Obj)
    (hCanValid : ValidCanTraverseParam ss)
    (hTypes : ValidTypeHierarchy ss)
    {current : Obj}
    {tail visited : List Obj}
    {fuel : Nat}
    (hroute :
      GPRoute
        (fun a b =>
          ss.can_traverse_p rover a b = true ∧
          ss.visible_p a b = true)
        current tail target)
    (hnodup : (current :: tail).Nodup)
    (hfresh : ∀ x, x ∈ tail → x ∉ visited)
    (hfuel : tail.length ≤ fuel) :
    ∃ path,
      gpNavDfs ss rover target fuel visited current = some path := by
  induction hroute generalizing visited fuel with
  | @nil current =>
      cases fuel with
      | zero =>
          exact ⟨[current], by simp [gpNavDfs]⟩
      | succ fuel =>
          exact ⟨[current], by simp [gpNavDfs]⟩
  | @cons current next target rest hedge hrest ih =>
      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          by_cases hcurrent : current = target
          · exact ⟨[current], by simp [gpNavDfs, hcurrent]⟩
          · have hnodupRest : (next :: rest).Nodup :=
              (List.nodup_cons.mp hnodup).2

            have hnextFresh : next ∉ visited :=
              hfresh next (by simp)

            have hrestFresh :
                ∀ x, x ∈ rest → x ∉ next :: visited := by
              intro x hx
              simp only [List.mem_cons, not_or]
              refine ⟨?_, hfresh x (by simp [hx])⟩
              intro hxeq
              have hnextMem : next ∈ rest := by
                simpa [hxeq] using hx
              exact
                (List.nodup_cons.mp hnodupRest).1 hnextMem

            have hfuelRest : rest.length ≤ fuel := by
              simp only [List.length_cons] at hfuel
              omega

            obtain ⟨path, hpath⟩ :=
              ih hnodupRest hrestFresh hfuelRest

            have hnextT : ss.waypoint_t next = true :=
              (hCanValid rover current next hedge.1).2.2

            have hnextMem : next ∈ ss.objects :=
              hTypes.2.1 next hnextT

            let nextWaypoints :=
              ss.objects.filter (fun candidate =>
                ss.waypoint_t candidate &&
                ss.can_traverse_p rover current candidate &&
                ss.visible_p current candidate &&
                decide (candidate ∉ visited))

            have hnextIn : next ∈ nextWaypoints := by
              unfold nextWaypoints
              exact List.mem_filter.mpr
                ⟨hnextMem,
                 by
                   simp [hnextT, hedge.1, hedge.2, hnextFresh]⟩

            have hbranch :
                (fun candidate =>
                  match
                    gpNavDfs
                      ss rover target fuel
                      (candidate :: visited) candidate
                  with
                  | some route => some (current :: route)
                  | none => none) next =
                  some (current :: path) := by
              simp [hpath]

            obtain ⟨result, hresult⟩ :=
              gpFirstSome_complete
                (fun candidate =>
                  match
                    gpNavDfs
                      ss rover target fuel
                      (candidate :: visited) candidate
                  with
                  | some route => some (current :: route)
                  | none => none)
                nextWaypoints
                next
                (current :: path)
                hnextIn
                hbranch

            refine ⟨result, ?_⟩
            change
              (if current = target then
                some [current]
              else
                gpFirstSome
                  (fun candidate =>
                    match
                      gpNavDfs
                        ss rover target fuel
                        (candidate :: visited) candidate
                    with
                    | some route => some (current :: route)
                    | none => none)
                  nextWaypoints) =
                some result
            rw [if_neg hcurrent]
            exact hresult

/--
Core DFS theorem.

Under the well-formed static assumptions, navigable connectedness and the
chosen fuel bound imply that the top-level DFS call succeeds with a path
from the current rover location to `target`.
-/
lemma gpNavDfs_top_level_succeeds
    (s : State)
    (rover target : Obj)
    (hwf : WellFormed s)
    (hr : s.statics.rover_t rover = true)
    (ht : s.statics.waypoint_t target = true) :
    ∃ path,
      gpNavDfs
          s.statics
          rover
          target
          (s.statics.objects.length + 1)
          [gpRoverLocation s rover]
          (gpRoverLocation s rover) =
        some path := by
  let start := gpRoverLocation s rover

  have hstartSpec :=
    gpRoverLocation_spec s rover hwf hr

  have hstartMem : start ∈ s.statics.objects := by
    simpa [start] using hstartSpec.1

  have hstartT : s.statics.waypoint_t start = true := by
    simpa [start] using hstartSpec.2.1

  have hstatic : WellFormedStatic s.statics :=
    hwf.1

  rcases hstatic with
    ⟨hObjects, _, hCanValid, _, _, _, _, _, _, _, _, _, hTypes,
     _, _, _, _, _,
     _, _, _, _, _,
     _, _, _, _, _,
     _, _, _, _, _,
     hNavigable⟩

  have hconnected :
      Relation.ReflTransGen
        (fun a b =>
          s.statics.can_traverse_p rover a b = true ∧
          s.statics.visible_p a b = true)
        start target :=
    hNavigable rover hr start target hstartT ht

  obtain ⟨route, hroute⟩ :=
    gpRoute_of_reflTransGen hconnected

  obtain ⟨simple, hsimpleRoute, hsimpleNodup⟩ :=
    gpRoute_simple_exists hroute

  have hnodes :
      ∀ x, x ∈ start :: simple → x ∈ s.statics.objects :=
    gpNavigableRoute_nodes_mem
      s.statics
      rover
      start
      target
      simple
      hCanValid
      hTypes
      hstartT
      hsimpleRoute

  have hsubset :
      (start :: simple).toFinset ⊆
        s.statics.objects.toFinset := by
    intro x hx
    have hxList : x ∈ start :: simple := by
      simpa using hx
    have hxObjects : x ∈ s.statics.objects :=
      hnodes x hxList
    simpa using hxObjects

  have hlengthNodes :
      (start :: simple).length ≤ s.statics.objects.length := by
    have hcard := Finset.card_le_card hsubset
    rw [List.toFinset_card_of_nodup hsimpleNodup,
        List.toFinset_card_of_nodup hObjects] at hcard
    exact hcard

  have hfresh :
      ∀ x, x ∈ simple → x ∉ [start] := by
    intro x hx
    simp only [List.mem_singleton]
    intro hxeq
    subst x
    exact (List.nodup_cons.mp hsimpleNodup).1 hx

  have hfuel :
      simple.length ≤ s.statics.objects.length + 1 := by
    simp only [List.length_cons] at hlengthNodes
    omega

  simpa [start] using
    gpNavDfs_succeeds_of_route
      s.statics
      rover
      target
      hCanValid
      hTypes
      hsimpleRoute
      hsimpleNodup
      hfresh
      hfuel

/--
Every path returned by `gpNavDfs` begins at `current` and describes a
navigable route ending at `target`.
-/
lemma gpNavDfs_sound
    (ss : StaticState)
    (rover target : Obj) :
    ∀ fuel visited current path,
      gpNavDfs ss rover target fuel visited current = some path →
      ∃ tail,
        path = current :: tail ∧
        GPRoute
          (fun a b =>
            ss.can_traverse_p rover a b = true ∧
            ss.visible_p a b = true)
          current tail target := by
  intro fuel
  induction fuel with
  | zero =>
      intro visited current path hresult
      by_cases hcurrent : current = target
      · subst target
        have hpath : [current] = path := by
          simpa [gpNavDfs] using hresult
        refine ⟨[], hpath.symm, GPRoute.nil current⟩
      · simp [gpNavDfs, hcurrent] at hresult
  | succ fuel ih =>
      intro visited current path hresult
      by_cases hcurrent : current = target
      · subst target
        have hpath : [current] = path := by
          simpa [gpNavDfs] using hresult
        refine ⟨[], hpath.symm, GPRoute.nil current⟩
      · let candidates :=
          ss.objects.filter (fun next =>
            ss.waypoint_t next &&
            ss.can_traverse_p rover current next &&
            ss.visible_p current next &&
            decide (next ∉ visited))

        let branch : Obj → Option (List Obj) :=
          fun next =>
            match
              gpNavDfs
                ss rover target fuel
                (next :: visited) next
            with
            | some route => some (current :: route)
            | none => none

        have hfirst :
            gpFirstSome branch candidates = some path := by
          simpa [gpNavDfs, hcurrent, candidates, branch] using hresult

        obtain ⟨next, hnextMem, hbranch⟩ :=
          gpFirstSome_sound branch candidates path hfirst

        have hnextMem' :
            next ∈ ss.objects.filter (fun candidate =>
              ss.waypoint_t candidate &&
              ss.can_traverse_p rover current candidate &&
              ss.visible_p current candidate &&
              decide (candidate ∉ visited)) := by
          simpa [candidates] using hnextMem

        have hnextBool :=
          (List.mem_filter.mp hnextMem').2

        have hnextProps :
            ss.waypoint_t next = true ∧
            ss.can_traverse_p rover current next = true ∧
            ss.visible_p current next = true ∧
            next ∉ visited := by
          simpa [and_assoc] using hnextBool

        cases hrecursive :
            gpNavDfs
              ss rover target fuel
              (next :: visited) next with
        | none =>
            simp [branch, hrecursive] at hbranch
        | some child =>
            have hpath : current :: child = path := by
              simpa [branch, hrecursive] using hbranch

            obtain ⟨tail, hchild, hroute⟩ :=
              ih (next :: visited) next child hrecursive

            refine
              ⟨next :: tail,
               hpath.symm.trans
                 (congrArg (List.cons current) hchild),
               ?_⟩

            exact
              GPRoute.cons
                ⟨hnextProps.2.1, hnextProps.2.2.1⟩
                hroute

/--
Executing navigation actions corresponding to a route is valid, ends with
the rover at the route target, and preserves well-formedness.
-/
lemma gpNavigationActionsFrom_correct
    (ss : StaticState)
    (rover : Obj)
    {current target : Obj}
    {tail : List Obj}
    (hroute :
      GPRoute
        (fun a b =>
          ss.can_traverse_p rover a b = true ∧
          ss.visible_p a b = true)
        current tail target)
    (s : State)
    (hstat : s.statics = ss)
    (hwf : WellFormed s)
    (hr : s.statics.rover_t rover = true)
    (hat : s.dynamic.at_p rover current = true) :
    ValidPlan
        (gpNavigationActionsFrom rover current tail) s ∧
    (runPlan
        (gpNavigationActionsFrom rover current tail) s).dynamic.at_p
          rover target = true ∧
    WellFormed
      (runPlan
        (gpNavigationActionsFrom rover current tail) s) := by
  induction hroute generalizing s with
  | nil a =>
      simp only [gpNavigationActionsFrom, ValidPlan, runPlan]
      exact ⟨True.intro, hat, hwf⟩
  | @cons a b t rest hedge hrest ih =>
      have hcan :
          s.statics.can_traverse_p rover a b = true := by
        simpa [hstat] using hedge.1

      have hvisible :
          s.statics.visible_p a b = true := by
        simpa [hstat] using hedge.2

      have hCanValid :
          ValidCanTraverseParam s.statics :=
        hwf.1.2.2.1

      have htypes :
          s.statics.rover_t rover = true ∧
          s.statics.waypoint_t a = true ∧
          s.statics.waypoint_t b = true :=
        hCanValid rover a b hcan

      have hpre : navigatePre rover a b s :=
        ⟨hr,
         htypes.2.1,
         htypes.2.2,
         hcan,
         hat,
         hvisible⟩

      let s' := navigate rover a b s

      have hwf' : WellFormed s' := by
        exact navigate_preserves_wf rover a b s hwf hpre

      have hstat' : s'.statics = ss := by
        change s.statics = ss
        exact hstat

      have hr' : s'.statics.rover_t rover = true := by
        change s.statics.rover_t rover = true
        exact hr

      have hat' : s'.dynamic.at_p rover b = true := by
        exact navigate_at_p_eq1 rover a b s

      have hrec :=
        ih s' hstat' hwf' hr' hat'

      have hvalid :
          ValidPlan
            (gpNavigationActionsFrom rover a (b :: rest)) s := by
        simp only
          [gpNavigationActionsFrom, ValidPlan, actionPre, actionApply]
        exact ⟨hpre, hrec.1⟩

      have hfinal :
          (runPlan
              (gpNavigationActionsFrom rover a (b :: rest)) s).dynamic.at_p
            rover t = true := by
        simp only [gpNavigationActionsFrom, runPlan, actionApply]
        exact hrec.2.1

      have hfinalWf :
          WellFormed
            (runPlan
              (gpNavigationActionsFrom rover a (b :: rest)) s) := by
        simp only [gpNavigationActionsFrom, runPlan, actionApply]
        exact hrec.2.2

      exact ⟨hvalid, hfinal, hfinalWf⟩

/--
The navigation actions generated from a successful DFS path are valid and
place the rover at the final waypoint.
-/
lemma gpNavigationPlan_correct
    (s : State)
    (rover target : Obj)
    (hwf : WellFormed s)
    (hr : s.statics.rover_t rover = true)
    (ht : s.statics.waypoint_t target = true) :
    ValidPlan (gpNavigationPlan s rover target) s ∧
    (runPlan (gpNavigationPlan s rover target) s).dynamic.at_p
        rover target = true ∧
    WellFormed (runPlan (gpNavigationPlan s rover target) s) := by
  let start := gpRoverLocation s rover

  obtain ⟨path, hdfs₀⟩ :=
    gpNavDfs_top_level_succeeds s rover target hwf hr ht

  have hdfs :
      gpNavDfs
          s.statics
          rover
          target
          (s.statics.objects.length + 1)
          [start]
          start =
        some path := by
    simpa [start] using hdfs₀

  obtain ⟨tail, hpath, hroute⟩ :=
    gpNavDfs_sound
      s.statics
      rover
      target
      (s.statics.objects.length + 1)
      [start]
      start
      path
      hdfs

  subst path

  have hstartSpec :=
    gpRoverLocation_spec s rover hwf hr

  have hstartAt :
      s.dynamic.at_p rover start = true := by
    simpa [start] using hstartSpec.2.2

  have hactions :=
    gpNavigationActionsFrom_correct
      s.statics
      rover
      hroute
      s
      rfl
      hwf
      hr
      hstartAt

  simpa
    [gpNavigationPlan, start, hdfs, gpPathToNavigationActions]
    using hactions

/--
Executing navigation actions changes only `at_p`.
-/
lemma gpNavigationActionsFrom_frame
    (rover current : Obj)
    (tail : List Obj)
    (s : State) :
    GPSameExceptAt
      s
      (runPlan (gpNavigationActionsFrom rover current tail) s) := by
  induction tail generalizing current s with
  | nil =>
      simp [gpNavigationActionsFrom, runPlan, GPSameExceptAt]
  | cons next rest ih =>
      simp only [gpNavigationActionsFrom, runPlan, actionApply]
      have hrec :=
        ih
          (current := next)
          (s := navigate rover current next s)
      simpa [GPSameExceptAt, navigate] using hrec

/--
A generated navigation plan changes only rover locations.
-/
lemma gpNavigationPlan_frame
    (s : State)
    (rover target : Obj) :
    GPSameExceptAt
      s
      (runPlan (gpNavigationPlan s rover target) s) := by
  cases hdfs :
      gpNavDfs
        s.statics
        rover
        target
        (s.statics.objects.length + 1)
        [gpRoverLocation s rover]
        (gpRoverLocation s rover) with
  | none =>
      simp [gpNavigationPlan, hdfs, GPSameExceptAt, runPlan]
  | some path =>
      cases path with
      | nil =>
          simp
            [gpNavigationPlan, hdfs, gpPathToNavigationActions,
             GPSameExceptAt, runPlan]
      | cons start rest =>
          simpa [gpNavigationPlan, hdfs, gpPathToNavigationActions] using
            (gpNavigationActionsFrom_frame rover start rest s)

/-!
  Part 4: accumulator and task lemmas.
-/

/--
The empty initial accumulator satisfies the accumulator invariant.
-/
lemma gpAccInv_initial
    (s : State)
    (hwf : WellFormed s) :
    GPAccInv s ([], s) := by
  simp [GPAccInv, ValidPlan, runPlan, hwf]

/--
Appending a valid suffix to a correct accumulator preserves the
accumulator invariant.
-/
lemma gpAccInv_extend
    {base : State}
    {acc : List PlanAction × State}
    {suffix : List PlanAction}
    (hacc : GPAccInv base acc)
    (hvalid : ValidPlan suffix acc.2) :
    GPAccInv
      base
      (acc.1 ++ suffix, runPlan suffix acc.2) := by
  rcases hacc with ⟨hprefix, hrun, hwf⟩

  have hsuffix :
      ValidPlan suffix (runPlan acc.1 base) := by
    rw [← hrun]
    exact hvalid

  have happ :
      ValidPlan (acc.1 ++ suffix) base := by
    exact
      (validPlan_append acc.1 suffix base).2
        ⟨hprefix, hsuffix⟩

  have hrun' :
      runPlan suffix acc.2 =
        runPlan (acc.1 ++ suffix) base := by
    rw [runPlan_append, ← hrun]

  have hwf' :
      WellFormed (runPlan suffix acc.2) := by
    exact validPlan_preserves_wf hvalid hwf

  exact ⟨happ, hrun', hwf'⟩

/--
Correctness contract for one soil task.

Besides validity and achievement of the current soil request, this records
the frame properties needed by the fold:
* the store is empty again;
* other soil samples are unchanged;
* already communicated soil facts remain true;
* rock and image communication predicates are unchanged;
* rock samples are unchanged.
-/
lemma gpSoilTask_correct
    {base : State}
    (mailbox lander landerWaypoint rover store sampleWaypoint : Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      GPSoilResource acc.2.statics rover store)
    (hsample :
      acc.2.dynamic.at_soil_sample_p sampleWaypoint = true)
    (hempty :
      acc.2.dynamic.empty_p store = true) :
    let out :=
      gpSoilTask
        mailbox lander landerWaypoint rover store sampleWaypoint acc
    GPAccInv base out ∧
    out.2.dynamic.communicated_soil_data_p sampleWaypoint = true ∧
    out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
    (∀ w, w ≠ sampleWaypoint →
      out.2.dynamic.at_soil_sample_p w =
        acc.2.dynamic.at_soil_sample_p w) ∧
    (∀ w,
      acc.2.dynamic.communicated_soil_data_p w = true →
      out.2.dynamic.communicated_soil_data_p w = true) ∧
    out.2.dynamic.communicated_rock_data_p =
      acc.2.dynamic.communicated_rock_data_p ∧
    out.2.dynamic.communicated_image_data_p =
      acc.2.dynamic.communicated_image_data_p ∧
    out.2.dynamic.at_rock_sample_p =
      acc.2.dynamic.at_rock_sample_p := by
  have hwf0 : WellFormed acc.2 :=
    hacc.2.2

  unfold GPCommunicationSite at hsite
  rcases hsite with
    ⟨hLanderT, hLanderWaypointT, hMailboxT,
     hAtLander, hMailboxVisible⟩

  unfold GPSoilResource at hresource
  rcases hresource with
    ⟨hRoverT, hStoreT, hEquipped, hStoreOf⟩

  have hwfParts := hwf0
  rcases hwfParts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hValidAtSoil, _⟩

  have hSampleWaypointT :
      acc.2.statics.waypoint_t sampleWaypoint = true :=
    hValidAtSoil sampleWaypoint hsample

  let navToSample :=
    gpNavigationPlan acc.2 rover sampleWaypoint
  let state1 :=
    runPlan navToSample acc.2

  have hnavToSample :
      ValidPlan navToSample acc.2 ∧
      state1.dynamic.at_p rover sampleWaypoint = true ∧
      WellFormed state1 := by
    simpa [navToSample, state1] using
      gpNavigationPlan_correct
        acc.2 rover sampleWaypoint
        hwf0 hRoverT hSampleWaypointT

  have hnavToSampleValid :
      ValidPlan navToSample acc.2 :=
    hnavToSample.1

  have hAtSample :
      state1.dynamic.at_p rover sampleWaypoint = true :=
    hnavToSample.2.1

  have hwf1 : WellFormed state1 :=
    hnavToSample.2.2

  have hframe1 :
      GPSameExceptAt acc.2 state1 := by
    simpa [navToSample, state1] using
      gpNavigationPlan_frame acc.2 rover sampleWaypoint

  rcases hframe1 with
    ⟨hstat1, hEmpty1, hRockAnalysis1, hSoilAnalysis1,
     hFull1, hCalibrated1, hImage1,
     hCommunicatedSoil1, hCommunicatedRock1,
     hCommunicatedImage1, hAtSoil1, hAtRock1⟩

  have hpreSample :
      sample_soilPre rover store sampleWaypoint state1 := by
    unfold sample_soilPre
    refine ⟨?_, ?_, ?_, hAtSample, ?_, ?_, ?_, ?_⟩
    · rw [hstat1]
      exact hRoverT
    · rw [hstat1]
      exact hStoreT
    · rw [hstat1]
      exact hSampleWaypointT
    · rw [hAtSoil1]
      exact hsample
    · rw [hstat1]
      exact hEquipped
    · rw [hstat1]
      exact hStoreOf
    · rw [hEmpty1]
      exact hempty

  let sampleAct : PlanAction :=
    .sample_soil rover store sampleWaypoint
  let state2 :=
    actionApply sampleAct state1

  have hpreSampleAct :
      actionPre sampleAct state1 := by
    simpa [sampleAct, actionPre] using hpreSample

  have hwf2 : WellFormed state2 := by
    simpa [state2] using
      action_preserves_wf hwf1 hpreSampleAct

  have hFull2 :
      state2.dynamic.full_p store = true := by
    simpa [state2, sampleAct, actionApply] using
      sample_soil_full_p_eq1
        rover store sampleWaypoint state1

  have hpreDrop :
      dropPre rover store state2 := by
    unfold dropPre
    refine ⟨?_, ?_, ?_, hFull2⟩
    · change state1.statics.rover_t rover = true
      rw [hstat1]
      exact hRoverT
    · change state1.statics.store_t store = true
      rw [hstat1]
      exact hStoreT
    · change state1.statics.store_of_p store rover = true
      rw [hstat1]
      exact hStoreOf

  let dropAct : PlanAction :=
    .drop rover store
  let state3 :=
    actionApply dropAct state2

  have hpreDropAct :
      actionPre dropAct state2 := by
    simpa [dropAct, actionPre] using hpreDrop

  have hwf3 : WellFormed state3 := by
    simpa [state3] using
      action_preserves_wf hwf2 hpreDropAct

  have hstat3 :
      state3.statics = acc.2.statics := by
    calc
      state3.statics = state2.statics := by
        change (drop rover store state2).statics = state2.statics
        rfl
      _ = state1.statics := by
        change
          (sample_soil rover store sampleWaypoint state1).statics =
            state1.statics
        rfl
      _ = acc.2.statics := hstat1

  have hRoverT3 :
      state3.statics.rover_t rover = true := by
    rw [hstat3]
    exact hRoverT

  have hMailboxT3 :
      state3.statics.waypoint_t mailbox = true := by
    rw [hstat3]
    exact hMailboxT

  let navToMailbox :=
    gpNavigationPlan state3 rover mailbox
  let state4 :=
    runPlan navToMailbox state3

  have hnavToMailbox :
      ValidPlan navToMailbox state3 ∧
      state4.dynamic.at_p rover mailbox = true ∧
      WellFormed state4 := by
    simpa [navToMailbox, state4] using
      gpNavigationPlan_correct
        state3 rover mailbox
        hwf3 hRoverT3 hMailboxT3

  have hnavToMailboxValid :
      ValidPlan navToMailbox state3 :=
    hnavToMailbox.1

  have hAtMailbox :
      state4.dynamic.at_p rover mailbox = true :=
    hnavToMailbox.2.1

  have hwf4 : WellFormed state4 :=
    hnavToMailbox.2.2

  have hframe2 :
      GPSameExceptAt state3 state4 := by
    simpa [navToMailbox, state4] using
      gpNavigationPlan_frame state3 rover mailbox

  rcases hframe2 with
    ⟨hstat4to3, hEmpty4to3, hRockAnalysis4to3,
     hSoilAnalysis4to3, hFull4to3, hCalibrated4to3,
     hImage4to3, hCommunicatedSoil4to3,
     hCommunicatedRock4to3, hCommunicatedImage4to3,
     hAtSoil4to3, hAtRock4to3⟩

  have hstat4 :
      state4.statics = acc.2.statics :=
    hstat4to3.trans hstat3

  have hHaveSoil2 :
      state2.dynamic.have_soil_analysis_p rover sampleWaypoint =
        true := by
    simpa [state2, sampleAct, actionApply] using
      sample_soil_have_soil_analysis_p_eq1
        rover store sampleWaypoint state1

  have hHaveSoil3 :
      state3.dynamic.have_soil_analysis_p rover sampleWaypoint =
        true := by
    change
      (drop rover store state2).dynamic.have_soil_analysis_p
          rover sampleWaypoint =
        true
    rw [drop_have_soil_analysis_p rover store state2]
    exact hHaveSoil2

  have hHaveSoil4 :
      state4.dynamic.have_soil_analysis_p rover sampleWaypoint =
        true := by
    rw [hSoilAnalysis4to3]
    exact hHaveSoil3

  have hpreCommunicate :
      communicate_soil_dataPre
        rover lander sampleWaypoint mailbox landerWaypoint state4 := by
    unfold communicate_soil_dataPre
    refine
      ⟨?_, ?_, ?_, ?_, ?_,
       hAtMailbox, ?_, hHaveSoil4, ?_⟩
    · rw [hstat4]
      exact hRoverT
    · rw [hstat4]
      exact hLanderT
    · rw [hstat4]
      exact hSampleWaypointT
    · rw [hstat4]
      exact hMailboxT
    · rw [hstat4]
      exact hLanderWaypointT
    · rw [hstat4]
      exact hAtLander
    · rw [hstat4]
      exact hMailboxVisible

  let communicateAct : PlanAction :=
    .communicate_soil_data
      rover lander sampleWaypoint mailbox landerWaypoint
  let state5 :=
    actionApply communicateAct state4

  have hpreCommunicateAct :
      actionPre communicateAct state4 := by
    simpa [communicateAct, actionPre] using hpreCommunicate

  have hwf5 : WellFormed state5 := by
    simpa [state5] using
      action_preserves_wf hwf4 hpreCommunicateAct

  have hEmpty3 :
      state3.dynamic.empty_p = acc.2.dynamic.empty_p := by
    funext st
    by_cases hst : st = store
    · subst st
      calc
        state3.dynamic.empty_p store = true := by
          change (drop rover store state2).dynamic.empty_p store = true
          exact drop_empty_p_eq1 rover store state2
        _ = acc.2.dynamic.empty_p store := hempty.symm
    · calc
        state3.dynamic.empty_p st = state2.dynamic.empty_p st := by
          change
            (drop rover store state2).dynamic.empty_p st =
              state2.dynamic.empty_p st
          exact drop_empty_p_ne rover store state2 hst
        _ = state1.dynamic.empty_p st := by
          change
            (sample_soil rover store sampleWaypoint state1).dynamic.empty_p st =
              state1.dynamic.empty_p st
          exact sample_soil_empty_p_ne
            rover store sampleWaypoint state1 hst
        _ = acc.2.dynamic.empty_p st :=
          congrFun hEmpty1 st

  have hAtSoil3 :
      ∀ w, w ≠ sampleWaypoint →
        state3.dynamic.at_soil_sample_p w =
          acc.2.dynamic.at_soil_sample_p w := by
    intro w hw
    calc
      state3.dynamic.at_soil_sample_p w =
          state2.dynamic.at_soil_sample_p w := by
        change
          (drop rover store state2).dynamic.at_soil_sample_p w =
            state2.dynamic.at_soil_sample_p w
        exact congrFun (drop_at_soil_sample_p rover store state2) w
      _ = state1.dynamic.at_soil_sample_p w := by
        change
          (sample_soil rover store sampleWaypoint state1).dynamic.at_soil_sample_p w =
            state1.dynamic.at_soil_sample_p w
        exact sample_soil_at_soil_sample_p_ne
          rover store sampleWaypoint state1 hw
      _ = acc.2.dynamic.at_soil_sample_p w :=
        congrFun hAtSoil1 w

  have hCommunicatedSoil3 :
      state3.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p := by
    calc
      state3.dynamic.communicated_soil_data_p =
          state2.dynamic.communicated_soil_data_p := by
        change
          (drop rover store state2).dynamic.communicated_soil_data_p =
            state2.dynamic.communicated_soil_data_p
        exact drop_communicated_soil_data_p rover store state2
      _ = state1.dynamic.communicated_soil_data_p := by
        change
          (sample_soil rover store sampleWaypoint state1).dynamic.communicated_soil_data_p =
            state1.dynamic.communicated_soil_data_p
        exact sample_soil_communicated_soil_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil1

  have hCommunicatedRock3 :
      state3.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p := by
    calc
      state3.dynamic.communicated_rock_data_p =
          state2.dynamic.communicated_rock_data_p := by
        change
          (drop rover store state2).dynamic.communicated_rock_data_p =
            state2.dynamic.communicated_rock_data_p
        exact drop_communicated_rock_data_p rover store state2
      _ = state1.dynamic.communicated_rock_data_p := by
        change
          (sample_soil rover store sampleWaypoint state1).dynamic.communicated_rock_data_p =
            state1.dynamic.communicated_rock_data_p
        exact sample_soil_communicated_rock_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock1

  have hCommunicatedImage3 :
      state3.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p := by
    calc
      state3.dynamic.communicated_image_data_p =
          state2.dynamic.communicated_image_data_p := by
        change
          (drop rover store state2).dynamic.communicated_image_data_p =
            state2.dynamic.communicated_image_data_p
        exact drop_communicated_image_data_p rover store state2
      _ = state1.dynamic.communicated_image_data_p := by
        change
          (sample_soil rover store sampleWaypoint state1).dynamic.communicated_image_data_p =
            state1.dynamic.communicated_image_data_p
        exact sample_soil_communicated_image_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_image_data_p :=
        hCommunicatedImage1

  have hAtRock3 :
      state3.dynamic.at_rock_sample_p =
        acc.2.dynamic.at_rock_sample_p := by
    calc
      state3.dynamic.at_rock_sample_p =
          state2.dynamic.at_rock_sample_p := by
        change
          (drop rover store state2).dynamic.at_rock_sample_p =
            state2.dynamic.at_rock_sample_p
        exact drop_at_rock_sample_p rover store state2
      _ = state1.dynamic.at_rock_sample_p := by
        change
          (sample_soil rover store sampleWaypoint state1).dynamic.at_rock_sample_p =
            state1.dynamic.at_rock_sample_p
        exact sample_soil_at_rock_sample_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.at_rock_sample_p :=
        hAtRock1

  have hEmpty4 :
      state4.dynamic.empty_p = acc.2.dynamic.empty_p :=
    hEmpty4to3.trans hEmpty3

  have hCommunicatedSoil4 :
      state4.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p :=
    hCommunicatedSoil4to3.trans hCommunicatedSoil3

  have hCommunicatedRock4 :
      state4.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p :=
    hCommunicatedRock4to3.trans hCommunicatedRock3

  have hCommunicatedImage4 :
      state4.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p :=
    hCommunicatedImage4to3.trans hCommunicatedImage3

  have hAtRock4 :
      state4.dynamic.at_rock_sample_p =
        acc.2.dynamic.at_rock_sample_p :=
    hAtRock4to3.trans hAtRock3

  have hCommunicatedCurrent :
      state5.dynamic.communicated_soil_data_p sampleWaypoint =
        true := by
    simpa [state5, communicateAct, actionApply] using
      communicate_soil_data_communicated_soil_data_p_eq1
        rover lander sampleWaypoint mailbox landerWaypoint state4

  have hEmpty5 :
      state5.dynamic.empty_p = acc.2.dynamic.empty_p := by
    calc
      state5.dynamic.empty_p = state4.dynamic.empty_p := by
        change
          (communicate_soil_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.empty_p =
          state4.dynamic.empty_p
        exact communicate_soil_data_empty_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.empty_p := hEmpty4

  have hAtSoil5 :
      ∀ w, w ≠ sampleWaypoint →
        state5.dynamic.at_soil_sample_p w =
          acc.2.dynamic.at_soil_sample_p w := by
    intro w hw
    calc
      state5.dynamic.at_soil_sample_p w =
          state4.dynamic.at_soil_sample_p w := by
        change
          (communicate_soil_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.at_soil_sample_p w =
          state4.dynamic.at_soil_sample_p w
        exact congrFun
          (communicate_soil_data_at_soil_sample_p
            rover lander sampleWaypoint mailbox landerWaypoint state4)
          w
      _ = state3.dynamic.at_soil_sample_p w :=
        congrFun hAtSoil4to3 w
      _ = acc.2.dynamic.at_soil_sample_p w :=
        hAtSoil3 w hw

  have hPreservesCommunicatedSoil :
      ∀ w,
        acc.2.dynamic.communicated_soil_data_p w = true →
        state5.dynamic.communicated_soil_data_p w = true := by
    intro w hw
    by_cases heq : w = sampleWaypoint
    · subst w
      exact hCommunicatedCurrent
    · have hw4 :
          state4.dynamic.communicated_soil_data_p w = true := by
        rw [hCommunicatedSoil4]
        exact hw
      calc
        state5.dynamic.communicated_soil_data_p w =
            state4.dynamic.communicated_soil_data_p w := by
          change
            (communicate_soil_data
              rover lander sampleWaypoint mailbox landerWaypoint
              state4).dynamic.communicated_soil_data_p w =
            state4.dynamic.communicated_soil_data_p w
          exact
            communicate_soil_data_communicated_soil_data_p_ne
              rover lander sampleWaypoint mailbox landerWaypoint
              state4 heq
        _ = true := hw4

  have hCommunicatedRock5 :
      state5.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p := by
    calc
      state5.dynamic.communicated_rock_data_p =
          state4.dynamic.communicated_rock_data_p := by
        change
          (communicate_soil_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.communicated_rock_data_p =
          state4.dynamic.communicated_rock_data_p
        exact communicate_soil_data_communicated_rock_data_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock4

  have hCommunicatedImage5 :
      state5.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p := by
    calc
      state5.dynamic.communicated_image_data_p =
          state4.dynamic.communicated_image_data_p := by
        change
          (communicate_soil_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.communicated_image_data_p =
          state4.dynamic.communicated_image_data_p
        exact communicate_soil_data_communicated_image_data_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.communicated_image_data_p :=
        hCommunicatedImage4

  have hAtRock5 :
      state5.dynamic.at_rock_sample_p =
        acc.2.dynamic.at_rock_sample_p := by
    calc
      state5.dynamic.at_rock_sample_p =
          state4.dynamic.at_rock_sample_p := by
        change
          (communicate_soil_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.at_rock_sample_p =
          state4.dynamic.at_rock_sample_p
        exact communicate_soil_data_at_rock_sample_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.at_rock_sample_p :=
        hAtRock4

  have hSampleDropValid :
      ValidPlan [sampleAct, dropAct] state1 := by
    simp only [ValidPlan]
    refine ⟨hpreSampleAct, ?_⟩
    refine ⟨?_, True.intro⟩
    change actionPre dropAct state2
    exact hpreDropAct

  have hCommunicateValid :
      ValidPlan [communicateAct] state4 := by
    simp only [ValidPlan]
    exact ⟨hpreCommunicateAct, True.intro⟩

  have hRunSampleDrop :
      runPlan [sampleAct, dropAct] state1 = state3 := by
    simp [runPlan, state2, state3]

  have hNavCommunicateValid :
      ValidPlan
        (navToMailbox ++ [communicateAct]) state3 := by
    apply
      (validPlan_append
        navToMailbox [communicateAct] state3).2
    refine ⟨hnavToMailboxValid, ?_⟩
    simpa [state4] using hCommunicateValid

  have hAfterSampleValid :
      ValidPlan
        ([sampleAct, dropAct] ++
          (navToMailbox ++ [communicateAct]))
        state1 := by
    apply
      (validPlan_append
        [sampleAct, dropAct]
        (navToMailbox ++ [communicateAct])
        state1).2
    refine ⟨hSampleDropValid, ?_⟩
    rw [hRunSampleDrop]
    exact hNavCommunicateValid

  have hWholeSuffixValid :
      ValidPlan
        (navToSample ++
          ([sampleAct, dropAct] ++
            (navToMailbox ++ [communicateAct])))
        acc.2 := by
    apply
      (validPlan_append
        navToSample
        ([sampleAct, dropAct] ++
          (navToMailbox ++ [communicateAct]))
        acc.2).2
    refine ⟨hnavToSampleValid, ?_⟩
    simpa [state1] using hAfterSampleValid

  let suffix :=
    navToSample ++
      [sampleAct, dropAct] ++
      navToMailbox ++
      [communicateAct]

  have hSuffixValid :
      ValidPlan suffix acc.2 := by
    simpa [suffix, List.append_assoc] using hWholeSuffixValid

  have hRunSuffix :
      runPlan suffix acc.2 = state5 := by
    simp
      [suffix, runPlan_append, state1, state2, state3,
       state4, state5, runPlan]

  have hExtended :=
    gpAccInv_extend
      (base := base)
      (acc := acc)
      (suffix := suffix)
      hacc hSuffixValid

  have hOutInv :
      GPAccInv base (acc.1 ++ suffix, state5) := by
    rw [hRunSuffix] at hExtended
    exact hExtended

  have hTaskEq :
      gpSoilTask
          mailbox lander landerWaypoint
          rover store sampleWaypoint acc =
        (acc.1 ++ suffix, state5) := by
    simp
      [gpSoilTask, suffix, navToSample, state1,
       sampleAct, state2, dropAct, state3,
       navToMailbox, state4, communicateAct, state5,
       List.append_assoc]

  dsimp only
  rw [hTaskEq]
  exact
    ⟨hOutInv,
     hCommunicatedCurrent,
     hEmpty5,
     hAtSoil5,
     hPreservesCommunicatedSoil,
     hCommunicatedRock5,
     hCommunicatedImage5,
     hAtRock5⟩

/--
Correctness contract for one rock task.
-/
lemma gpRockTask_correct
    {base : State}
    (mailbox lander landerWaypoint rover store sampleWaypoint : Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      GPRockResource acc.2.statics rover store)
    (hsample :
      acc.2.dynamic.at_rock_sample_p sampleWaypoint = true)
    (hempty :
      acc.2.dynamic.empty_p store = true) :
    let out :=
      gpRockTask
        mailbox lander landerWaypoint rover store sampleWaypoint acc
    GPAccInv base out ∧
    out.2.dynamic.communicated_rock_data_p sampleWaypoint = true ∧
    out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
    (∀ w, w ≠ sampleWaypoint →
      out.2.dynamic.at_rock_sample_p w =
        acc.2.dynamic.at_rock_sample_p w) ∧
    (∀ w,
      acc.2.dynamic.communicated_rock_data_p w = true →
      out.2.dynamic.communicated_rock_data_p w = true) ∧
    out.2.dynamic.communicated_soil_data_p =
      acc.2.dynamic.communicated_soil_data_p ∧
    out.2.dynamic.communicated_image_data_p =
      acc.2.dynamic.communicated_image_data_p := by
  have hwf0 : WellFormed acc.2 :=
    hacc.2.2

  unfold GPCommunicationSite at hsite
  rcases hsite with
    ⟨hLanderT, hLanderWaypointT, hMailboxT,
     hAtLander, hMailboxVisible⟩

  unfold GPRockResource at hresource
  rcases hresource with
    ⟨hRoverT, hStoreT, hEquipped, hStoreOf⟩

  have hwfParts := hwf0
  rcases hwfParts with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hValidAtRock, _⟩

  have hSampleWaypointT :
      acc.2.statics.waypoint_t sampleWaypoint = true :=
    hValidAtRock sampleWaypoint hsample

  let navToSample :=
    gpNavigationPlan acc.2 rover sampleWaypoint
  let state1 :=
    runPlan navToSample acc.2

  have hnavToSample :
      ValidPlan navToSample acc.2 ∧
      state1.dynamic.at_p rover sampleWaypoint = true ∧
      WellFormed state1 := by
    simpa [navToSample, state1] using
      gpNavigationPlan_correct
        acc.2 rover sampleWaypoint
        hwf0 hRoverT hSampleWaypointT

  have hnavToSampleValid :
      ValidPlan navToSample acc.2 :=
    hnavToSample.1

  have hAtSample :
      state1.dynamic.at_p rover sampleWaypoint = true :=
    hnavToSample.2.1

  have hwf1 : WellFormed state1 :=
    hnavToSample.2.2

  have hframe1 :
      GPSameExceptAt acc.2 state1 := by
    simpa [navToSample, state1] using
      gpNavigationPlan_frame acc.2 rover sampleWaypoint

  rcases hframe1 with
    ⟨hstat1, hEmpty1, hRockAnalysis1, hSoilAnalysis1,
     hFull1, hCalibrated1, hImage1,
     hCommunicatedSoil1, hCommunicatedRock1,
     hCommunicatedImage1, hAtSoil1, hAtRock1⟩

  have hpreSample :
      sample_rockPre rover store sampleWaypoint state1 := by
    unfold sample_rockPre
    refine ⟨?_, ?_, ?_, hAtSample, ?_, ?_, ?_, ?_⟩
    · rw [hstat1]
      exact hRoverT
    · rw [hstat1]
      exact hStoreT
    · rw [hstat1]
      exact hSampleWaypointT
    · rw [hAtRock1]
      exact hsample
    · rw [hstat1]
      exact hEquipped
    · rw [hstat1]
      exact hStoreOf
    · rw [hEmpty1]
      exact hempty

  let sampleAct : PlanAction :=
    .sample_rock rover store sampleWaypoint
  let state2 :=
    actionApply sampleAct state1

  have hpreSampleAct :
      actionPre sampleAct state1 := by
    simpa [sampleAct, actionPre] using hpreSample

  have hwf2 : WellFormed state2 := by
    simpa [state2] using
      action_preserves_wf hwf1 hpreSampleAct

  have hFull2 :
      state2.dynamic.full_p store = true := by
    simpa [state2, sampleAct, actionApply] using
      sample_rock_full_p_eq1
        rover store sampleWaypoint state1

  have hpreDrop :
      dropPre rover store state2 := by
    unfold dropPre
    refine ⟨?_, ?_, ?_, hFull2⟩
    · change state1.statics.rover_t rover = true
      rw [hstat1]
      exact hRoverT
    · change state1.statics.store_t store = true
      rw [hstat1]
      exact hStoreT
    · change state1.statics.store_of_p store rover = true
      rw [hstat1]
      exact hStoreOf

  let dropAct : PlanAction :=
    .drop rover store
  let state3 :=
    actionApply dropAct state2

  have hpreDropAct :
      actionPre dropAct state2 := by
    simpa [dropAct, actionPre] using hpreDrop

  have hwf3 : WellFormed state3 := by
    simpa [state3] using
      action_preserves_wf hwf2 hpreDropAct

  have hstat3 :
      state3.statics = acc.2.statics := by
    calc
      state3.statics = state2.statics := by
        change (drop rover store state2).statics = state2.statics
        rfl
      _ = state1.statics := by
        change
          (sample_rock rover store sampleWaypoint state1).statics =
            state1.statics
        rfl
      _ = acc.2.statics := hstat1

  have hRoverT3 :
      state3.statics.rover_t rover = true := by
    rw [hstat3]
    exact hRoverT

  have hMailboxT3 :
      state3.statics.waypoint_t mailbox = true := by
    rw [hstat3]
    exact hMailboxT

  let navToMailbox :=
    gpNavigationPlan state3 rover mailbox
  let state4 :=
    runPlan navToMailbox state3

  have hnavToMailbox :
      ValidPlan navToMailbox state3 ∧
      state4.dynamic.at_p rover mailbox = true ∧
      WellFormed state4 := by
    simpa [navToMailbox, state4] using
      gpNavigationPlan_correct
        state3 rover mailbox
        hwf3 hRoverT3 hMailboxT3

  have hnavToMailboxValid :
      ValidPlan navToMailbox state3 :=
    hnavToMailbox.1

  have hAtMailbox :
      state4.dynamic.at_p rover mailbox = true :=
    hnavToMailbox.2.1

  have hwf4 : WellFormed state4 :=
    hnavToMailbox.2.2

  have hframe2 :
      GPSameExceptAt state3 state4 := by
    simpa [navToMailbox, state4] using
      gpNavigationPlan_frame state3 rover mailbox

  rcases hframe2 with
    ⟨hstat4to3, hEmpty4to3, hRockAnalysis4to3,
     hSoilAnalysis4to3, hFull4to3, hCalibrated4to3,
     hImage4to3, hCommunicatedSoil4to3,
     hCommunicatedRock4to3, hCommunicatedImage4to3,
     hAtSoil4to3, hAtRock4to3⟩

  have hstat4 :
      state4.statics = acc.2.statics :=
    hstat4to3.trans hstat3

  have hHaveRock2 :
      state2.dynamic.have_rock_analysis_p rover sampleWaypoint =
        true := by
    simpa [state2, sampleAct, actionApply] using
      sample_rock_have_rock_analysis_p_eq1
        rover store sampleWaypoint state1

  have hHaveRock3 :
      state3.dynamic.have_rock_analysis_p rover sampleWaypoint =
        true := by
    change
      (drop rover store state2).dynamic.have_rock_analysis_p
          rover sampleWaypoint =
        true
    rw [drop_have_rock_analysis_p rover store state2]
    exact hHaveRock2

  have hHaveRock4 :
      state4.dynamic.have_rock_analysis_p rover sampleWaypoint =
        true := by
    rw [hRockAnalysis4to3]
    exact hHaveRock3

  have hpreCommunicate :
      communicate_rock_dataPre
        rover lander sampleWaypoint mailbox landerWaypoint state4 := by
    unfold communicate_rock_dataPre
    refine
      ⟨?_, ?_, ?_, ?_, ?_,
       hAtMailbox, ?_, hHaveRock4, ?_⟩
    · rw [hstat4]
      exact hRoverT
    · rw [hstat4]
      exact hLanderT
    · rw [hstat4]
      exact hSampleWaypointT
    · rw [hstat4]
      exact hMailboxT
    · rw [hstat4]
      exact hLanderWaypointT
    · rw [hstat4]
      exact hAtLander
    · rw [hstat4]
      exact hMailboxVisible

  let communicateAct : PlanAction :=
    .communicate_rock_data
      rover lander sampleWaypoint mailbox landerWaypoint
  let state5 :=
    actionApply communicateAct state4

  have hpreCommunicateAct :
      actionPre communicateAct state4 := by
    simpa [communicateAct, actionPre] using hpreCommunicate

  have hwf5 : WellFormed state5 := by
    simpa [state5] using
      action_preserves_wf hwf4 hpreCommunicateAct

  have hEmpty3 :
      state3.dynamic.empty_p = acc.2.dynamic.empty_p := by
    funext st
    by_cases hst : st = store
    · subst st
      calc
        state3.dynamic.empty_p store = true := by
          change (drop rover store state2).dynamic.empty_p store = true
          exact drop_empty_p_eq1 rover store state2
        _ = acc.2.dynamic.empty_p store := hempty.symm
    · calc
        state3.dynamic.empty_p st = state2.dynamic.empty_p st := by
          change
            (drop rover store state2).dynamic.empty_p st =
              state2.dynamic.empty_p st
          exact drop_empty_p_ne rover store state2 hst
        _ = state1.dynamic.empty_p st := by
          change
            (sample_rock rover store sampleWaypoint state1).dynamic.empty_p st =
              state1.dynamic.empty_p st
          exact sample_rock_empty_p_ne
            rover store sampleWaypoint state1 hst
        _ = acc.2.dynamic.empty_p st :=
          congrFun hEmpty1 st

  have hAtRock3 :
      ∀ w, w ≠ sampleWaypoint →
        state3.dynamic.at_rock_sample_p w =
          acc.2.dynamic.at_rock_sample_p w := by
    intro w hw
    calc
      state3.dynamic.at_rock_sample_p w =
          state2.dynamic.at_rock_sample_p w := by
        change
          (drop rover store state2).dynamic.at_rock_sample_p w =
            state2.dynamic.at_rock_sample_p w
        exact congrFun (drop_at_rock_sample_p rover store state2) w
      _ = state1.dynamic.at_rock_sample_p w := by
        change
          (sample_rock rover store sampleWaypoint state1).dynamic.at_rock_sample_p w =
            state1.dynamic.at_rock_sample_p w
        exact sample_rock_at_rock_sample_p_ne
          rover store sampleWaypoint state1 hw
      _ = acc.2.dynamic.at_rock_sample_p w :=
        congrFun hAtRock1 w

  have hCommunicatedRock3 :
      state3.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p := by
    calc
      state3.dynamic.communicated_rock_data_p =
          state2.dynamic.communicated_rock_data_p := by
        change
          (drop rover store state2).dynamic.communicated_rock_data_p =
            state2.dynamic.communicated_rock_data_p
        exact drop_communicated_rock_data_p rover store state2
      _ = state1.dynamic.communicated_rock_data_p := by
        change
          (sample_rock rover store sampleWaypoint state1).dynamic.communicated_rock_data_p =
            state1.dynamic.communicated_rock_data_p
        exact sample_rock_communicated_rock_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock1

  have hCommunicatedSoil3 :
      state3.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p := by
    calc
      state3.dynamic.communicated_soil_data_p =
          state2.dynamic.communicated_soil_data_p := by
        change
          (drop rover store state2).dynamic.communicated_soil_data_p =
            state2.dynamic.communicated_soil_data_p
        exact drop_communicated_soil_data_p rover store state2
      _ = state1.dynamic.communicated_soil_data_p := by
        change
          (sample_rock rover store sampleWaypoint state1).dynamic.communicated_soil_data_p =
            state1.dynamic.communicated_soil_data_p
        exact sample_rock_communicated_soil_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil1

  have hCommunicatedImage3 :
      state3.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p := by
    calc
      state3.dynamic.communicated_image_data_p =
          state2.dynamic.communicated_image_data_p := by
        change
          (drop rover store state2).dynamic.communicated_image_data_p =
            state2.dynamic.communicated_image_data_p
        exact drop_communicated_image_data_p rover store state2
      _ = state1.dynamic.communicated_image_data_p := by
        change
          (sample_rock rover store sampleWaypoint state1).dynamic.communicated_image_data_p =
            state1.dynamic.communicated_image_data_p
        exact sample_rock_communicated_image_data_p
          rover store sampleWaypoint state1
      _ = acc.2.dynamic.communicated_image_data_p :=
        hCommunicatedImage1

  have hEmpty4 :
      state4.dynamic.empty_p = acc.2.dynamic.empty_p :=
    hEmpty4to3.trans hEmpty3

  have hCommunicatedRock4 :
      state4.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p :=
    hCommunicatedRock4to3.trans hCommunicatedRock3

  have hCommunicatedSoil4 :
      state4.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p :=
    hCommunicatedSoil4to3.trans hCommunicatedSoil3

  have hCommunicatedImage4 :
      state4.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p :=
    hCommunicatedImage4to3.trans hCommunicatedImage3

  have hCommunicatedCurrent :
      state5.dynamic.communicated_rock_data_p sampleWaypoint =
        true := by
    simpa [state5, communicateAct, actionApply] using
      communicate_rock_data_communicated_rock_data_p_eq1
        rover lander sampleWaypoint mailbox landerWaypoint state4

  have hEmpty5 :
      state5.dynamic.empty_p = acc.2.dynamic.empty_p := by
    calc
      state5.dynamic.empty_p = state4.dynamic.empty_p := by
        change
          (communicate_rock_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.empty_p =
          state4.dynamic.empty_p
        exact communicate_rock_data_empty_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.empty_p := hEmpty4

  have hAtRock5 :
      ∀ w, w ≠ sampleWaypoint →
        state5.dynamic.at_rock_sample_p w =
          acc.2.dynamic.at_rock_sample_p w := by
    intro w hw
    calc
      state5.dynamic.at_rock_sample_p w =
          state4.dynamic.at_rock_sample_p w := by
        change
          (communicate_rock_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.at_rock_sample_p w =
          state4.dynamic.at_rock_sample_p w
        exact congrFun
          (communicate_rock_data_at_rock_sample_p
            rover lander sampleWaypoint mailbox landerWaypoint state4)
          w
      _ = state3.dynamic.at_rock_sample_p w :=
        congrFun hAtRock4to3 w
      _ = acc.2.dynamic.at_rock_sample_p w :=
        hAtRock3 w hw

  have hPreservesCommunicatedRock :
      ∀ w,
        acc.2.dynamic.communicated_rock_data_p w = true →
        state5.dynamic.communicated_rock_data_p w = true := by
    intro w hw
    by_cases heq : w = sampleWaypoint
    · subst w
      exact hCommunicatedCurrent
    · have hw4 :
          state4.dynamic.communicated_rock_data_p w = true := by
        rw [hCommunicatedRock4]
        exact hw
      calc
        state5.dynamic.communicated_rock_data_p w =
            state4.dynamic.communicated_rock_data_p w := by
          change
            (communicate_rock_data
              rover lander sampleWaypoint mailbox landerWaypoint
              state4).dynamic.communicated_rock_data_p w =
            state4.dynamic.communicated_rock_data_p w
          exact
            communicate_rock_data_communicated_rock_data_p_ne
              rover lander sampleWaypoint mailbox landerWaypoint
              state4 heq
        _ = true := hw4

  have hCommunicatedSoil5 :
      state5.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p := by
    calc
      state5.dynamic.communicated_soil_data_p =
          state4.dynamic.communicated_soil_data_p := by
        change
          (communicate_rock_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.communicated_soil_data_p =
          state4.dynamic.communicated_soil_data_p
        exact communicate_rock_data_communicated_soil_data_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil4

  have hCommunicatedImage5 :
      state5.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p := by
    calc
      state5.dynamic.communicated_image_data_p =
          state4.dynamic.communicated_image_data_p := by
        change
          (communicate_rock_data
            rover lander sampleWaypoint mailbox landerWaypoint
            state4).dynamic.communicated_image_data_p =
          state4.dynamic.communicated_image_data_p
        exact communicate_rock_data_communicated_image_data_p
          rover lander sampleWaypoint mailbox landerWaypoint state4
      _ = acc.2.dynamic.communicated_image_data_p :=
        hCommunicatedImage4

  have hSampleDropValid :
      ValidPlan [sampleAct, dropAct] state1 := by
    simp only [ValidPlan]
    refine ⟨hpreSampleAct, ?_⟩
    refine ⟨?_, True.intro⟩
    change actionPre dropAct state2
    exact hpreDropAct

  have hCommunicateValid :
      ValidPlan [communicateAct] state4 := by
    simp only [ValidPlan]
    exact ⟨hpreCommunicateAct, True.intro⟩

  have hRunSampleDrop :
      runPlan [sampleAct, dropAct] state1 = state3 := by
    simp [runPlan, state2, state3]

  have hNavCommunicateValid :
      ValidPlan
        (navToMailbox ++ [communicateAct]) state3 := by
    apply
      (validPlan_append
        navToMailbox [communicateAct] state3).2
    refine ⟨hnavToMailboxValid, ?_⟩
    simpa [state4] using hCommunicateValid

  have hAfterSampleValid :
      ValidPlan
        ([sampleAct, dropAct] ++
          (navToMailbox ++ [communicateAct]))
        state1 := by
    apply
      (validPlan_append
        [sampleAct, dropAct]
        (navToMailbox ++ [communicateAct])
        state1).2
    refine ⟨hSampleDropValid, ?_⟩
    rw [hRunSampleDrop]
    exact hNavCommunicateValid

  have hWholeSuffixValid :
      ValidPlan
        (navToSample ++
          ([sampleAct, dropAct] ++
            (navToMailbox ++ [communicateAct])))
        acc.2 := by
    apply
      (validPlan_append
        navToSample
        ([sampleAct, dropAct] ++
          (navToMailbox ++ [communicateAct]))
        acc.2).2
    refine ⟨hnavToSampleValid, ?_⟩
    simpa [state1] using hAfterSampleValid

  let suffix :=
    navToSample ++
      [sampleAct, dropAct] ++
      navToMailbox ++
      [communicateAct]

  have hSuffixValid :
      ValidPlan suffix acc.2 := by
    simpa [suffix, List.append_assoc] using hWholeSuffixValid

  have hRunSuffix :
      runPlan suffix acc.2 = state5 := by
    simp
      [suffix, runPlan_append, state1, state2, state3,
       state4, state5, runPlan]

  have hExtended :=
    gpAccInv_extend
      (base := base)
      (acc := acc)
      (suffix := suffix)
      hacc hSuffixValid

  have hOutInv :
      GPAccInv base (acc.1 ++ suffix, state5) := by
    rw [hRunSuffix] at hExtended
    exact hExtended

  have hTaskEq :
      gpRockTask
          mailbox lander landerWaypoint
          rover store sampleWaypoint acc =
        (acc.1 ++ suffix, state5) := by
    simp
      [gpRockTask, suffix, navToSample, state1,
       sampleAct, state2, dropAct, state3,
       navToMailbox, state4, communicateAct, state5,
       List.append_assoc]

  dsimp only
  rw [hTaskEq]
  exact
    ⟨hOutInv,
     hCommunicatedCurrent,
     hEmpty5,
     hAtRock5,
     hPreservesCommunicatedRock,
     hCommunicatedSoil5,
     hCommunicatedImage5⟩

/--
Correctness contract for one image task.

The well-formed static state supplies:
* a camera supporting the requested mode;
* an imaging rover carrying that camera;
* a calibration target;
* visible calibration and shooting waypoints.
-/
lemma gpImageTask_correct
    {base : State}
    (mailbox lander landerWaypoint : Obj)
    (request : Obj × Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hobjective :
      acc.2.statics.objective_t request.1 = true)
    (hmode :
      acc.2.statics.mode_t request.2 = true) :
    let out :=
      gpImageTask mailbox lander landerWaypoint request acc
    GPAccInv base out ∧
    out.2.dynamic.communicated_image_data_p
        request.1 request.2 = true ∧
    (∀ o m,
      acc.2.dynamic.communicated_image_data_p o m = true →
      out.2.dynamic.communicated_image_data_p o m = true) ∧
    out.2.dynamic.communicated_soil_data_p =
      acc.2.dynamic.communicated_soil_data_p ∧
    out.2.dynamic.communicated_rock_data_p =
      acc.2.dynamic.communicated_rock_data_p := by
  have hwf0 : WellFormed acc.2 :=
    hacc.2.2

  unfold GPCommunicationSite at hsite
  rcases hsite with
    ⟨hLanderT, hLanderWaypointT, hMailboxT,
     hAtLander, hMailboxVisible⟩

  have hstaticParts := hwf0.1
  rcases hstaticParts with
    ⟨_, _, _, _, _, hEquipImagingValid, hSupportsValid, _,
     hVisibleFromValid, _, hCalibrationTargetValid, hOnBoardValid,
     hTypes, _, _, _, _, _, _, _, _, _, hCameraTarget,
     hCameraOnBoard, _, hOnBoardFunctional, _, hModeSupported,
     _, _, _, _, hObjectiveVisible, _⟩

  let objective := request.1
  let mode := request.2

  have hObjectiveT :
      acc.2.statics.objective_t objective = true := by
    simpa [objective] using hobjective

  have hModeT :
      acc.2.statics.mode_t mode = true := by
    simpa [mode] using hmode

  obtain ⟨someCamera, hSomeSupports⟩ :=
    hModeSupported mode hModeT

  have hSomeCameraT :
      acc.2.statics.camera_t someCamera = true :=
    (hSupportsValid someCamera mode hSomeSupports).1

  have hSomeCameraMem :
      someCamera ∈ acc.2.statics.objects :=
    hTypes.2.2.2.1 someCamera hSomeCameraT

  let camera :=
    gpChooseObj acc.2.statics.objects (fun candidate =>
      acc.2.statics.supports_p candidate mode)

  have hCameraChoice :=
    gpChooseObj_spec
      acc.2.statics.objects
      (fun candidate =>
        acc.2.statics.supports_p candidate mode)
      ⟨someCamera, hSomeCameraMem, hSomeSupports⟩

  have hSupports :
      acc.2.statics.supports_p camera mode = true := by
    simpa [camera] using hCameraChoice.2

  have hCameraT :
      acc.2.statics.camera_t camera = true :=
    (hSupportsValid camera mode hSupports).1

  obtain
    ⟨someRover, hSomeOnBoard, hSomeRoverEquipped⟩ :=
      hCameraOnBoard camera hCameraT

  have hSomeRoverT :
      acc.2.statics.rover_t someRover = true :=
    (hOnBoardValid camera someRover hSomeOnBoard).2

  have hSomeRoverMem :
      someRover ∈ acc.2.statics.objects :=
    hTypes.1 someRover hSomeRoverT

  let rover :=
    gpChooseObj acc.2.statics.objects (fun candidate =>
      acc.2.statics.on_board_p camera candidate)

  have hRoverChoice :=
    gpChooseObj_spec
      acc.2.statics.objects
      (fun candidate =>
        acc.2.statics.on_board_p camera candidate)
      ⟨someRover, hSomeRoverMem, hSomeOnBoard⟩

  have hOnBoard :
      acc.2.statics.on_board_p camera rover = true := by
    simpa [rover] using hRoverChoice.2

  have hRoverT :
      acc.2.statics.rover_t rover = true :=
    (hOnBoardValid camera rover hOnBoard).2

  have hRoverEq :
      rover = someRover :=
    hOnBoardFunctional
      camera rover someRover hOnBoard hSomeOnBoard

  have hRoverEquipped :
      acc.2.statics.equipped_for_imaging_p rover = true := by
    rw [hRoverEq]
    exact hSomeRoverEquipped

  obtain ⟨someTarget, hSomeTarget⟩ :=
    hCameraTarget camera hCameraT

  have hSomeTargetT :
      acc.2.statics.objective_t someTarget = true :=
    (hCalibrationTargetValid camera someTarget hSomeTarget).2

  have hSomeTargetMem :
      someTarget ∈ acc.2.statics.objects :=
    hTypes.2.2.2.2.2.2.1 someTarget hSomeTargetT

  let calibrationTarget :=
    gpChooseObj acc.2.statics.objects (fun candidate =>
      acc.2.statics.calibration_target_p camera candidate)

  have hTargetChoice :=
    gpChooseObj_spec
      acc.2.statics.objects
      (fun candidate =>
        acc.2.statics.calibration_target_p camera candidate)
      ⟨someTarget, hSomeTargetMem, hSomeTarget⟩

  have hCalibrationTarget :
      acc.2.statics.calibration_target_p
        camera calibrationTarget = true := by
    simpa [calibrationTarget] using hTargetChoice.2

  have hCalibrationTargetT :
      acc.2.statics.objective_t calibrationTarget = true :=
    (hCalibrationTargetValid
      camera calibrationTarget hCalibrationTarget).2

  obtain ⟨someCalibrationWaypoint, hSomeCalibrationVisible⟩ :=
    hObjectiveVisible calibrationTarget hCalibrationTargetT

  have hSomeCalibrationWaypointT :
      acc.2.statics.waypoint_t someCalibrationWaypoint = true :=
    (hVisibleFromValid
      calibrationTarget
      someCalibrationWaypoint
      hSomeCalibrationVisible).2

  have hSomeCalibrationWaypointMem :
      someCalibrationWaypoint ∈ acc.2.statics.objects :=
    hTypes.2.1
      someCalibrationWaypoint hSomeCalibrationWaypointT

  let calibrationWaypoint :=
    gpChooseObj acc.2.statics.objects (fun waypoint =>
      acc.2.statics.visible_from_p calibrationTarget waypoint)

  have hCalibrationWaypointChoice :=
    gpChooseObj_spec
      acc.2.statics.objects
      (fun waypoint =>
        acc.2.statics.visible_from_p calibrationTarget waypoint)
      ⟨someCalibrationWaypoint,
       hSomeCalibrationWaypointMem,
       hSomeCalibrationVisible⟩

  have hCalibrationVisible :
      acc.2.statics.visible_from_p
        calibrationTarget calibrationWaypoint = true := by
    simpa [calibrationWaypoint] using hCalibrationWaypointChoice.2

  have hCalibrationWaypointT :
      acc.2.statics.waypoint_t calibrationWaypoint = true :=
    (hVisibleFromValid
      calibrationTarget calibrationWaypoint hCalibrationVisible).2

  obtain ⟨someShootingWaypoint, hSomeShootingVisible⟩ :=
    hObjectiveVisible objective hObjectiveT

  have hSomeShootingWaypointT :
      acc.2.statics.waypoint_t someShootingWaypoint = true :=
    (hVisibleFromValid
      objective someShootingWaypoint hSomeShootingVisible).2

  have hSomeShootingWaypointMem :
      someShootingWaypoint ∈ acc.2.statics.objects :=
    hTypes.2.1 someShootingWaypoint hSomeShootingWaypointT

  let shootingWaypoint :=
    gpChooseObj acc.2.statics.objects (fun waypoint =>
      acc.2.statics.visible_from_p objective waypoint)

  have hShootingWaypointChoice :=
    gpChooseObj_spec
      acc.2.statics.objects
      (fun waypoint =>
        acc.2.statics.visible_from_p objective waypoint)
      ⟨someShootingWaypoint,
       hSomeShootingWaypointMem,
       hSomeShootingVisible⟩

  have hShootingVisible :
      acc.2.statics.visible_from_p objective shootingWaypoint = true := by
    simpa [shootingWaypoint] using hShootingWaypointChoice.2

  have hShootingWaypointT :
      acc.2.statics.waypoint_t shootingWaypoint = true :=
    (hVisibleFromValid
      objective shootingWaypoint hShootingVisible).2

  let navToCalibration :=
    gpNavigationPlan acc.2 rover calibrationWaypoint
  let state1 :=
    runPlan navToCalibration acc.2

  have hnavToCalibration :
      ValidPlan navToCalibration acc.2 ∧
      state1.dynamic.at_p rover calibrationWaypoint = true ∧
      WellFormed state1 := by
    simpa [navToCalibration, state1] using
      gpNavigationPlan_correct
        acc.2 rover calibrationWaypoint
        hwf0 hRoverT hCalibrationWaypointT

  have hnavToCalibrationValid :
      ValidPlan navToCalibration acc.2 :=
    hnavToCalibration.1

  have hAtCalibration :
      state1.dynamic.at_p rover calibrationWaypoint = true :=
    hnavToCalibration.2.1

  have hwf1 : WellFormed state1 :=
    hnavToCalibration.2.2

  have hframe1 :
      GPSameExceptAt acc.2 state1 := by
    simpa [navToCalibration, state1] using
      gpNavigationPlan_frame acc.2 rover calibrationWaypoint

  rcases hframe1 with
    ⟨hstat1, hEmpty1, hRockAnalysis1, hSoilAnalysis1,
     hFull1, hCalibrated1, hImage1,
     hCommunicatedSoil1, hCommunicatedRock1,
     hCommunicatedImage1, hAtSoil1, hAtRock1⟩

  have hpreCalibrate :
      calibratePre
        rover camera calibrationTarget calibrationWaypoint state1 := by
    unfold calibratePre
    refine
      ⟨?_, ?_, ?_, ?_, ?_, ?_,
       hAtCalibration, ?_, ?_⟩
    · rw [hstat1]
      exact hRoverT
    · rw [hstat1]
      exact hCameraT
    · rw [hstat1]
      exact hCalibrationTargetT
    · rw [hstat1]
      exact hCalibrationWaypointT
    · rw [hstat1]
      exact hRoverEquipped
    · rw [hstat1]
      exact hCalibrationTarget
    · rw [hstat1]
      exact hCalibrationVisible
    · rw [hstat1]
      exact hOnBoard

  let calibrateAct : PlanAction :=
    .calibrate
      rover camera calibrationTarget calibrationWaypoint
  let state2 :=
    actionApply calibrateAct state1

  have hpreCalibrateAct :
      actionPre calibrateAct state1 := by
    simpa [calibrateAct, actionPre] using hpreCalibrate

  have hwf2 : WellFormed state2 := by
    simpa [state2] using
      action_preserves_wf hwf1 hpreCalibrateAct

  have hstat2 :
      state2.statics = acc.2.statics := by
    calc
      state2.statics = state1.statics := by
        change
          (calibrate
            rover camera calibrationTarget calibrationWaypoint
            state1).statics =
          state1.statics
        rfl
      _ = acc.2.statics := hstat1

  have hCalibrated2 :
      state2.dynamic.calibrated_p camera rover = true := by
    simpa [state2, calibrateAct, actionApply] using
      calibrate_calibrated_p_eq1
        rover camera calibrationTarget calibrationWaypoint state1

  have hRoverT2 :
      state2.statics.rover_t rover = true := by
    rw [hstat2]
    exact hRoverT

  have hShootingWaypointT2 :
      state2.statics.waypoint_t shootingWaypoint = true := by
    rw [hstat2]
    exact hShootingWaypointT

  let navToShooting :=
    gpNavigationPlan state2 rover shootingWaypoint
  let state3 :=
    runPlan navToShooting state2

  have hnavToShooting :
      ValidPlan navToShooting state2 ∧
      state3.dynamic.at_p rover shootingWaypoint = true ∧
      WellFormed state3 := by
    simpa [navToShooting, state3] using
      gpNavigationPlan_correct
        state2 rover shootingWaypoint
        hwf2 hRoverT2 hShootingWaypointT2

  have hnavToShootingValid :
      ValidPlan navToShooting state2 :=
    hnavToShooting.1

  have hAtShooting :
      state3.dynamic.at_p rover shootingWaypoint = true :=
    hnavToShooting.2.1

  have hwf3 : WellFormed state3 :=
    hnavToShooting.2.2

  have hframe3 :
      GPSameExceptAt state2 state3 := by
    simpa [navToShooting, state3] using
      gpNavigationPlan_frame state2 rover shootingWaypoint

  rcases hframe3 with
    ⟨hstat3to2, hEmpty3to2, hRockAnalysis3to2,
     hSoilAnalysis3to2, hFull3to2, hCalibrated3to2,
     hImage3to2, hCommunicatedSoil3to2,
     hCommunicatedRock3to2, hCommunicatedImage3to2,
     hAtSoil3to2, hAtRock3to2⟩

  have hstat3 :
      state3.statics = acc.2.statics :=
    hstat3to2.trans hstat2

  have hCalibrated3 :
      state3.dynamic.calibrated_p camera rover = true := by
    rw [hCalibrated3to2]
    exact hCalibrated2

  have hpreTakeImage :
      take_imagePre
        rover shootingWaypoint objective camera mode state3 := by
    unfold take_imagePre
    refine
      ⟨?_, ?_, ?_, ?_, ?_, hCalibrated3,
       ?_, ?_, ?_, ?_, hAtShooting⟩
    · rw [hstat3]
      exact hRoverT
    · rw [hstat3]
      exact hShootingWaypointT
    · rw [hstat3]
      exact hObjectiveT
    · rw [hstat3]
      exact hCameraT
    · rw [hstat3]
      exact hModeT
    · rw [hstat3]
      exact hOnBoard
    · rw [hstat3]
      exact hRoverEquipped
    · rw [hstat3]
      exact hSupports
    · rw [hstat3]
      exact hShootingVisible

  let takeImageAct : PlanAction :=
    .take_image
      rover shootingWaypoint objective camera mode
  let state4 :=
    actionApply takeImageAct state3

  have hpreTakeImageAct :
      actionPre takeImageAct state3 := by
    simpa [takeImageAct, actionPre] using hpreTakeImage

  have hwf4 : WellFormed state4 := by
    simpa [state4] using
      action_preserves_wf hwf3 hpreTakeImageAct

  have hstat4 :
      state4.statics = acc.2.statics := by
    calc
      state4.statics = state3.statics := by
        change
          (take_image
            rover shootingWaypoint objective camera mode state3).statics =
          state3.statics
        rfl
      _ = acc.2.statics := hstat3

  have hHaveImage4 :
      state4.dynamic.have_image_p rover objective mode = true := by
    simpa [state4, takeImageAct, actionApply] using
      take_image_have_image_p_eq1
        rover shootingWaypoint objective camera mode state3

  have hRoverT4 :
      state4.statics.rover_t rover = true := by
    rw [hstat4]
    exact hRoverT

  have hMailboxT4 :
      state4.statics.waypoint_t mailbox = true := by
    rw [hstat4]
    exact hMailboxT

  let navToMailbox :=
    gpNavigationPlan state4 rover mailbox
  let state5 :=
    runPlan navToMailbox state4

  have hnavToMailbox :
      ValidPlan navToMailbox state4 ∧
      state5.dynamic.at_p rover mailbox = true ∧
      WellFormed state5 := by
    simpa [navToMailbox, state5] using
      gpNavigationPlan_correct
        state4 rover mailbox
        hwf4 hRoverT4 hMailboxT4

  have hnavToMailboxValid :
      ValidPlan navToMailbox state4 :=
    hnavToMailbox.1

  have hAtMailbox :
      state5.dynamic.at_p rover mailbox = true :=
    hnavToMailbox.2.1

  have hwf5 : WellFormed state5 :=
    hnavToMailbox.2.2

  have hframe5 :
      GPSameExceptAt state4 state5 := by
    simpa [navToMailbox, state5] using
      gpNavigationPlan_frame state4 rover mailbox

  rcases hframe5 with
    ⟨hstat5to4, hEmpty5to4, hRockAnalysis5to4,
     hSoilAnalysis5to4, hFull5to4, hCalibrated5to4,
     hImage5to4, hCommunicatedSoil5to4,
     hCommunicatedRock5to4, hCommunicatedImage5to4,
     hAtSoil5to4, hAtRock5to4⟩

  have hstat5 :
      state5.statics = acc.2.statics :=
    hstat5to4.trans hstat4

  have hHaveImage5 :
      state5.dynamic.have_image_p rover objective mode = true := by
    rw [hImage5to4]
    exact hHaveImage4

  have hpreCommunicate :
      communicate_image_dataPre
        rover lander objective mode mailbox landerWaypoint state5 := by
    unfold communicate_image_dataPre
    refine
      ⟨?_, ?_, ?_, ?_, ?_, ?_,
       hAtMailbox, ?_, hHaveImage5, ?_⟩
    · rw [hstat5]
      exact hRoverT
    · rw [hstat5]
      exact hLanderT
    · rw [hstat5]
      exact hObjectiveT
    · rw [hstat5]
      exact hModeT
    · rw [hstat5]
      exact hMailboxT
    · rw [hstat5]
      exact hLanderWaypointT
    · rw [hstat5]
      exact hAtLander
    · rw [hstat5]
      exact hMailboxVisible

  let communicateAct : PlanAction :=
    .communicate_image_data
      rover lander objective mode mailbox landerWaypoint
  let state6 :=
    actionApply communicateAct state5

  have hpreCommunicateAct :
      actionPre communicateAct state5 := by
    simpa [communicateAct, actionPre] using hpreCommunicate

  have hwf6 : WellFormed state6 := by
    simpa [state6] using
      action_preserves_wf hwf5 hpreCommunicateAct

  have hCommunicatedImage5 :
      state5.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p := by
    calc
      state5.dynamic.communicated_image_data_p =
          state4.dynamic.communicated_image_data_p :=
        hCommunicatedImage5to4
      _ = state3.dynamic.communicated_image_data_p := by
        change
          (take_image
            rover shootingWaypoint objective camera mode
            state3).dynamic.communicated_image_data_p =
          state3.dynamic.communicated_image_data_p
        exact take_image_communicated_image_data_p
          rover shootingWaypoint objective camera mode state3
      _ = state2.dynamic.communicated_image_data_p :=
        hCommunicatedImage3to2
      _ = state1.dynamic.communicated_image_data_p := by
        change
          (calibrate
            rover camera calibrationTarget calibrationWaypoint
            state1).dynamic.communicated_image_data_p =
          state1.dynamic.communicated_image_data_p
        exact calibrate_communicated_image_data_p
          rover camera calibrationTarget calibrationWaypoint state1
      _ = acc.2.dynamic.communicated_image_data_p :=
        hCommunicatedImage1

  have hCommunicatedSoil5 :
      state5.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p := by
    calc
      state5.dynamic.communicated_soil_data_p =
          state4.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil5to4
      _ = state3.dynamic.communicated_soil_data_p := by
        change
          (take_image
            rover shootingWaypoint objective camera mode
            state3).dynamic.communicated_soil_data_p =
          state3.dynamic.communicated_soil_data_p
        exact take_image_communicated_soil_data_p
          rover shootingWaypoint objective camera mode state3
      _ = state2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil3to2
      _ = state1.dynamic.communicated_soil_data_p := by
        change
          (calibrate
            rover camera calibrationTarget calibrationWaypoint
            state1).dynamic.communicated_soil_data_p =
          state1.dynamic.communicated_soil_data_p
        exact calibrate_communicated_soil_data_p
          rover camera calibrationTarget calibrationWaypoint state1
      _ = acc.2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil1

  have hCommunicatedRock5 :
      state5.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p := by
    calc
      state5.dynamic.communicated_rock_data_p =
          state4.dynamic.communicated_rock_data_p :=
        hCommunicatedRock5to4
      _ = state3.dynamic.communicated_rock_data_p := by
        change
          (take_image
            rover shootingWaypoint objective camera mode
            state3).dynamic.communicated_rock_data_p =
          state3.dynamic.communicated_rock_data_p
        exact take_image_communicated_rock_data_p
          rover shootingWaypoint objective camera mode state3
      _ = state2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock3to2
      _ = state1.dynamic.communicated_rock_data_p := by
        change
          (calibrate
            rover camera calibrationTarget calibrationWaypoint
            state1).dynamic.communicated_rock_data_p =
          state1.dynamic.communicated_rock_data_p
        exact calibrate_communicated_rock_data_p
          rover camera calibrationTarget calibrationWaypoint state1
      _ = acc.2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock1

  have hCommunicatedCurrent :
      state6.dynamic.communicated_image_data_p objective mode = true := by
    simpa [state6, communicateAct, actionApply] using
      communicate_image_data_communicated_image_data_p_eq1
        rover lander objective mode mailbox landerWaypoint state5

  have hPreservesCommunicatedImage :
      ∀ o m,
        acc.2.dynamic.communicated_image_data_p o m = true →
        state6.dynamic.communicated_image_data_p o m = true := by
    intro o m hom
    by_cases hmatch : o = objective ∧ m = mode
    · rcases hmatch with ⟨rfl, rfl⟩
      exact hCommunicatedCurrent
    · have hOld5 :
          state5.dynamic.communicated_image_data_p o m = true := by
        rw [hCommunicatedImage5]
        exact hom
      change
        (if o = objective ∧ m = mode then
          true
        else
          state5.dynamic.communicated_image_data_p o m) =
        true
      simp [hmatch, hOld5]

  have hCommunicatedSoil6 :
      state6.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p := by
    calc
      state6.dynamic.communicated_soil_data_p =
          state5.dynamic.communicated_soil_data_p := by
        change
          (communicate_image_data
            rover lander objective mode mailbox landerWaypoint
            state5).dynamic.communicated_soil_data_p =
          state5.dynamic.communicated_soil_data_p
        exact communicate_image_data_communicated_soil_data_p
          rover lander objective mode mailbox landerWaypoint state5
      _ = acc.2.dynamic.communicated_soil_data_p :=
        hCommunicatedSoil5

  have hCommunicatedRock6 :
      state6.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p := by
    calc
      state6.dynamic.communicated_rock_data_p =
          state5.dynamic.communicated_rock_data_p := by
        change
          (communicate_image_data
            rover lander objective mode mailbox landerWaypoint
            state5).dynamic.communicated_rock_data_p =
          state5.dynamic.communicated_rock_data_p
        exact communicate_image_data_communicated_rock_data_p
          rover lander objective mode mailbox landerWaypoint state5
      _ = acc.2.dynamic.communicated_rock_data_p :=
        hCommunicatedRock5

  have hCalibrateValid :
      ValidPlan [calibrateAct] state1 := by
    simp only [ValidPlan]
    exact ⟨hpreCalibrateAct, True.intro⟩

  have hTakeImageValid :
      ValidPlan [takeImageAct] state3 := by
    simp only [ValidPlan]
    exact ⟨hpreTakeImageAct, True.intro⟩

  have hCommunicateValid :
      ValidPlan [communicateAct] state5 := by
    simp only [ValidPlan]
    exact ⟨hpreCommunicateAct, True.intro⟩

  have hNavCommunicateValid :
      ValidPlan
        (navToMailbox ++ [communicateAct]) state4 := by
    apply
      (validPlan_append
        navToMailbox [communicateAct] state4).2
    refine ⟨hnavToMailboxValid, ?_⟩
    simpa [state5] using hCommunicateValid

  have hAfterTakeValid :
      ValidPlan
        ([takeImageAct] ++
          (navToMailbox ++ [communicateAct]))
        state3 := by
    apply
      (validPlan_append
        [takeImageAct]
        (navToMailbox ++ [communicateAct])
        state3).2
    refine ⟨hTakeImageValid, ?_⟩
    simpa [state4, runPlan] using hNavCommunicateValid

  have hAfterShootingValid :
      ValidPlan
        (navToShooting ++
          ([takeImageAct] ++
            (navToMailbox ++ [communicateAct])))
        state2 := by
    apply
      (validPlan_append
        navToShooting
        ([takeImageAct] ++
          (navToMailbox ++ [communicateAct]))
        state2).2
    refine ⟨hnavToShootingValid, ?_⟩
    simpa [state3] using hAfterTakeValid

  have hAfterCalibrateValid :
      ValidPlan
        ([calibrateAct] ++
          (navToShooting ++
            ([takeImageAct] ++
              (navToMailbox ++ [communicateAct]))))
        state1 := by
    apply
      (validPlan_append
        [calibrateAct]
        (navToShooting ++
          ([takeImageAct] ++
            (navToMailbox ++ [communicateAct])))
        state1).2
    refine ⟨hCalibrateValid, ?_⟩
    simpa [state2, runPlan] using hAfterShootingValid

  have hWholeSuffixValid :
      ValidPlan
        (navToCalibration ++
          ([calibrateAct] ++
            (navToShooting ++
              ([takeImageAct] ++
                (navToMailbox ++ [communicateAct])))))
        acc.2 := by
    apply
      (validPlan_append
        navToCalibration
        ([calibrateAct] ++
          (navToShooting ++
            ([takeImageAct] ++
              (navToMailbox ++ [communicateAct]))))
        acc.2).2
    refine ⟨hnavToCalibrationValid, ?_⟩
    simpa [state1] using hAfterCalibrateValid

  let suffix :=
    navToCalibration ++
      [calibrateAct] ++
      navToShooting ++
      [takeImageAct] ++
      navToMailbox ++
      [communicateAct]

  have hSuffixValid :
      ValidPlan suffix acc.2 := by
    simpa [suffix, List.append_assoc] using hWholeSuffixValid

  have hRunSuffix :
      runPlan suffix acc.2 = state6 := by
    simp
      [suffix, runPlan_append, state1, state2, state3,
       state4, state5, state6, runPlan]

  have hExtended :=
    gpAccInv_extend
      (base := base)
      (acc := acc)
      (suffix := suffix)
      hacc hSuffixValid

  have hOutInv :
      GPAccInv base (acc.1 ++ suffix, state6) := by
    rw [hRunSuffix] at hExtended
    exact hExtended

  have hTaskEq :
      gpImageTask
          mailbox lander landerWaypoint request acc =
        (acc.1 ++ suffix, state6) := by
    simp
      [gpImageTask, suffix, objective, mode, camera, rover,
       calibrationTarget, calibrationWaypoint, shootingWaypoint,
       navToCalibration, state1, calibrateAct, state2,
       navToShooting, state3, takeImageAct, state4,
       navToMailbox, state5, communicateAct, state6,
       List.append_assoc]

  dsimp only
  rw [hTaskEq]
  exact
    ⟨hOutInv,
     by simpa [objective, mode] using hCommunicatedCurrent,
     by
       intro o m hom
       exact hPreservesCommunicatedImage o m hom,
     hCommunicatedSoil6,
     hCommunicatedRock6⟩

/--
Strengthened correctness theorem for the soil-task fold.

In addition to the public fold contract, this records that every soil
communication fact already true in the input accumulator remains true in
the output accumulator.
-/
lemma gpSoilFold_correct_strong
    {base : State}
    (mailbox lander landerWaypoint rover store : Obj)
    (goals : List Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      goals ≠ [] →
      GPSoilResource acc.2.statics rover store)
    (hnodup : goals.Nodup)
    (hsamples :
      ∀ w, w ∈ goals →
        acc.2.dynamic.at_soil_sample_p w = true)
    (hempty :
      goals ≠ [] →
      acc.2.dynamic.empty_p store = true) :
    let out :=
      goals.foldl
        (fun a w =>
          gpSoilTask
            mailbox lander landerWaypoint rover store w a)
        acc
    (GPAccInv base out ∧
      GPSoilDone goals out.2 ∧
      out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
      out.2.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p ∧
      out.2.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p ∧
      out.2.dynamic.at_rock_sample_p =
        acc.2.dynamic.at_rock_sample_p) ∧
    (∀ w,
      acc.2.dynamic.communicated_soil_data_p w = true →
      out.2.dynamic.communicated_soil_data_p w = true) := by
  dsimp only
  induction goals generalizing acc with
  | nil =>
      simp only [List.foldl]
      refine
        ⟨⟨hacc, ?_, by simp, by simp, by simp, by simp⟩, ?_⟩
      · simp [GPSoilDone]
      · intro w hw
        exact hw

  | cons w ws ih =>
      simp only [List.foldl]

      have hnonempty : w :: ws ≠ [] := by
        simp

      have hwNotMem : w ∉ ws :=
        (List.nodup_cons.mp hnodup).1

      have hwsNodup : ws.Nodup :=
        (List.nodup_cons.mp hnodup).2

      have hResource0 :
          GPSoilResource acc.2.statics rover store :=
        hresource hnonempty

      have hSample0 :
          acc.2.dynamic.at_soil_sample_p w = true :=
        hsamples w (List.mem_cons_self)

      have hEmpty0 :
          acc.2.dynamic.empty_p store = true :=
        hempty hnonempty

      let acc1 :=
        gpSoilTask
          mailbox lander landerWaypoint rover store w acc

      have htask :
          GPAccInv base acc1 ∧
          acc1.2.dynamic.communicated_soil_data_p w = true ∧
          acc1.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
          (∀ x, x ≠ w →
            acc1.2.dynamic.at_soil_sample_p x =
              acc.2.dynamic.at_soil_sample_p x) ∧
          (∀ x,
            acc.2.dynamic.communicated_soil_data_p x = true →
            acc1.2.dynamic.communicated_soil_data_p x = true) ∧
          acc1.2.dynamic.communicated_rock_data_p =
            acc.2.dynamic.communicated_rock_data_p ∧
          acc1.2.dynamic.communicated_image_data_p =
            acc.2.dynamic.communicated_image_data_p ∧
          acc1.2.dynamic.at_rock_sample_p =
            acc.2.dynamic.at_rock_sample_p := by
        simpa only [acc1] using
          (gpSoilTask_correct
            (base := base)
            mailbox lander landerWaypoint rover store w acc
            hacc hsite hResource0 hSample0 hEmpty0)

      rcases htask with
        ⟨hacc1, hCommunicatedCurrent, hEmptyTask,
         hSampleFrame, hCommunicatedFrame,
         hRockTask, hImageTask, hAtRockTask⟩

      have hstatAcc :
          acc.2.statics = base.statics := by
        calc
          acc.2.statics =
              (runPlan acc.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc.2.1
          _ = base.statics :=
            runPlan_statics acc.1 base

      have hstatAcc1 :
          acc1.2.statics = base.statics := by
        calc
          acc1.2.statics =
              (runPlan acc1.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc1.2.1
          _ = base.statics :=
            runPlan_statics acc1.1 base

      have hstat1 :
          acc1.2.statics = acc.2.statics :=
        hstatAcc1.trans hstatAcc.symm

      have hsite1 :
          GPCommunicationSite
            acc1.2.statics mailbox lander landerWaypoint := by
        rw [hstat1]
        exact hsite

      have hresource1 :
          ws ≠ [] →
          GPSoilResource acc1.2.statics rover store := by
        intro _
        rw [hstat1]
        exact hResource0

      have hsamples1 :
          ∀ x, x ∈ ws →
            acc1.2.dynamic.at_soil_sample_p x = true := by
        intro x hx
        have hxne : x ≠ w := by
          intro hxw
          subst x
          exact hwNotMem hx
        rw [hSampleFrame x hxne]
        exact hsamples x (List.mem_cons_of_mem w hx)

      have hempty1 :
          ws ≠ [] →
          acc1.2.dynamic.empty_p store = true := by
        intro _
        rw [hEmptyTask]
        exact hEmpty0

      have hrec :=
        ih
          (acc := acc1)
          hacc1
          hsite1
          hresource1
          hwsNodup
          hsamples1
          hempty1

      rcases hrec with
        ⟨⟨haccFinal, hDoneWs, hEmptyRec,
           hRockRec, hImageRec, hAtRockRec⟩,
         hCommunicatedRec⟩

      have hDoneCons :
          GPSoilDone
            (w :: ws)
            (ws.foldl
              (fun a x =>
                gpSoilTask
                  mailbox lander landerWaypoint
                  rover store x a)
              acc1).2 := by
        intro x hx
        rcases List.mem_cons.mp hx with hxeq | hxws
        · subst x
          exact
            hCommunicatedRec w hCommunicatedCurrent
        · exact hDoneWs x hxws

      refine ⟨?_, ?_⟩
      · exact
          ⟨haccFinal,
           hDoneCons,
           hEmptyRec.trans hEmptyTask,
           hRockRec.trans hRockTask,
           hImageRec.trans hImageTask,
           hAtRockRec.trans hAtRockTask⟩
      · intro x hx
        exact
          hCommunicatedRec x
            (hCommunicatedFrame x hx)

/--
Correctness of folding all soil tasks.

Nodup is essential because sampling consumes the sample at the processed
waypoint. The frame theorem for one task guarantees that all unprocessed
samples remain available.
-/
lemma gpSoilFold_correct
    {base : State}
    (mailbox lander landerWaypoint rover store : Obj)
    (goals : List Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      goals ≠ [] →
      GPSoilResource acc.2.statics rover store)
    (hnodup : goals.Nodup)
    (hsamples :
      ∀ w, w ∈ goals →
        acc.2.dynamic.at_soil_sample_p w = true)
    (hempty :
      goals ≠ [] →
      acc.2.dynamic.empty_p store = true) :
    let out :=
      goals.foldl
        (fun a w =>
          gpSoilTask
            mailbox lander landerWaypoint rover store w a)
        acc
    GPAccInv base out ∧
    GPSoilDone goals out.2 ∧
    out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
    out.2.dynamic.communicated_rock_data_p =
      acc.2.dynamic.communicated_rock_data_p ∧
    out.2.dynamic.communicated_image_data_p =
      acc.2.dynamic.communicated_image_data_p ∧
    out.2.dynamic.at_rock_sample_p =
      acc.2.dynamic.at_rock_sample_p := by
  dsimp only
  have hstrong :=
    gpSoilFold_correct_strong
      (base := base)
      mailbox lander landerWaypoint rover store
      goals acc hacc hsite hresource hnodup hsamples hempty
  dsimp only at hstrong
  exact hstrong.1

/--
Strengthened correctness theorem for the rock-task fold.

In addition to the public fold contract, this records that every rock
communication fact already true in the input accumulator remains true in
the output accumulator.
-/
lemma gpRockFold_correct_strong
    {base : State}
    (mailbox lander landerWaypoint rover store : Obj)
    (goals : List Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      goals ≠ [] →
      GPRockResource acc.2.statics rover store)
    (hnodup : goals.Nodup)
    (hsamples :
      ∀ w, w ∈ goals →
        acc.2.dynamic.at_rock_sample_p w = true)
    (hempty :
      goals ≠ [] →
      acc.2.dynamic.empty_p store = true) :
    let out :=
      goals.foldl
        (fun a w =>
          gpRockTask
            mailbox lander landerWaypoint rover store w a)
        acc
    (GPAccInv base out ∧
      GPRockDone goals out.2 ∧
      out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
      out.2.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p ∧
      out.2.dynamic.communicated_image_data_p =
        acc.2.dynamic.communicated_image_data_p) ∧
    (∀ w,
      acc.2.dynamic.communicated_rock_data_p w = true →
      out.2.dynamic.communicated_rock_data_p w = true) := by
  dsimp only
  induction goals generalizing acc with
  | nil =>
      simp only [List.foldl]
      refine
        ⟨⟨hacc, ?_, by simp, by simp, by simp⟩, ?_⟩
      · simp [GPRockDone]
      · intro w hw
        exact hw

  | cons w ws ih =>
      simp only [List.foldl]

      have hnonempty : w :: ws ≠ [] := by
        simp

      have hwNotMem : w ∉ ws :=
        (List.nodup_cons.mp hnodup).1

      have hwsNodup : ws.Nodup :=
        (List.nodup_cons.mp hnodup).2

      have hResource0 :
          GPRockResource acc.2.statics rover store :=
        hresource hnonempty

      have hSample0 :
          acc.2.dynamic.at_rock_sample_p w = true :=
        hsamples w List.mem_cons_self

      have hEmpty0 :
          acc.2.dynamic.empty_p store = true :=
        hempty hnonempty

      let acc1 :=
        gpRockTask
          mailbox lander landerWaypoint rover store w acc

      have htask :
          GPAccInv base acc1 ∧
          acc1.2.dynamic.communicated_rock_data_p w = true ∧
          acc1.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
          (∀ x, x ≠ w →
            acc1.2.dynamic.at_rock_sample_p x =
              acc.2.dynamic.at_rock_sample_p x) ∧
          (∀ x,
            acc.2.dynamic.communicated_rock_data_p x = true →
            acc1.2.dynamic.communicated_rock_data_p x = true) ∧
          acc1.2.dynamic.communicated_soil_data_p =
            acc.2.dynamic.communicated_soil_data_p ∧
          acc1.2.dynamic.communicated_image_data_p =
            acc.2.dynamic.communicated_image_data_p := by
        simpa only [acc1] using
          (gpRockTask_correct
            (base := base)
            mailbox lander landerWaypoint rover store w acc
            hacc hsite hResource0 hSample0 hEmpty0)

      rcases htask with
        ⟨hacc1, hCommunicatedCurrent, hEmptyTask,
         hSampleFrame, hCommunicatedFrame,
         hSoilTask, hImageTask⟩

      have hstatAcc :
          acc.2.statics = base.statics := by
        calc
          acc.2.statics =
              (runPlan acc.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc.2.1
          _ = base.statics :=
            runPlan_statics acc.1 base

      have hstatAcc1 :
          acc1.2.statics = base.statics := by
        calc
          acc1.2.statics =
              (runPlan acc1.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc1.2.1
          _ = base.statics :=
            runPlan_statics acc1.1 base

      have hstat1 :
          acc1.2.statics = acc.2.statics :=
        hstatAcc1.trans hstatAcc.symm

      have hsite1 :
          GPCommunicationSite
            acc1.2.statics mailbox lander landerWaypoint := by
        rw [hstat1]
        exact hsite

      have hresource1 :
          ws ≠ [] →
          GPRockResource acc1.2.statics rover store := by
        intro _
        rw [hstat1]
        exact hResource0

      have hsamples1 :
          ∀ x, x ∈ ws →
            acc1.2.dynamic.at_rock_sample_p x = true := by
        intro x hx
        have hxne : x ≠ w := by
          intro hxw
          subst x
          exact hwNotMem hx
        rw [hSampleFrame x hxne]
        exact hsamples x (List.mem_cons_of_mem w hx)

      have hempty1 :
          ws ≠ [] →
          acc1.2.dynamic.empty_p store = true := by
        intro _
        rw [hEmptyTask]
        exact hEmpty0

      have hrec :=
        ih
          (acc := acc1)
          hacc1
          hsite1
          hresource1
          hwsNodup
          hsamples1
          hempty1

      rcases hrec with
        ⟨⟨haccFinal, hDoneWs, hEmptyRec,
           hSoilRec, hImageRec⟩,
         hCommunicatedRec⟩

      have hDoneCons :
          GPRockDone
            (w :: ws)
            (ws.foldl
              (fun a x =>
                gpRockTask
                  mailbox lander landerWaypoint
                  rover store x a)
              acc1).2 := by
        intro x hx
        rcases List.mem_cons.mp hx with hxeq | hxws
        · subst x
          exact
            hCommunicatedRec w hCommunicatedCurrent
        · exact hDoneWs x hxws

      refine ⟨?_, ?_⟩
      · exact
          ⟨haccFinal,
           hDoneCons,
           hEmptyRec.trans hEmptyTask,
           hSoilRec.trans hSoilTask,
           hImageRec.trans hImageTask⟩
      · intro x hx
        exact
          hCommunicatedRec x
            (hCommunicatedFrame x hx)

/--
Correctness of folding all rock tasks.

Duplicate-freedom ensures that a consumed rock sample is not requested
again. The strengthened fold invariant also preserves every previously
communicated rock-data fact.
-/
lemma gpRockFold_correct
    {base : State}
    (mailbox lander landerWaypoint rover store : Obj)
    (goals : List Obj)
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (hresource :
      goals ≠ [] →
      GPRockResource acc.2.statics rover store)
    (hnodup : goals.Nodup)
    (hsamples :
      ∀ w, w ∈ goals →
        acc.2.dynamic.at_rock_sample_p w = true)
    (hempty :
      goals ≠ [] →
      acc.2.dynamic.empty_p store = true) :
    let out :=
      goals.foldl
        (fun a w =>
          gpRockTask
            mailbox lander landerWaypoint rover store w a)
        acc
    GPAccInv base out ∧
    GPRockDone goals out.2 ∧
    out.2.dynamic.empty_p = acc.2.dynamic.empty_p ∧
    out.2.dynamic.communicated_soil_data_p =
      acc.2.dynamic.communicated_soil_data_p ∧
    out.2.dynamic.communicated_image_data_p =
      acc.2.dynamic.communicated_image_data_p := by
  dsimp only
  have hstrong :=
    gpRockFold_correct_strong
      (base := base)
      mailbox lander landerWaypoint rover store
      goals acc hacc hsite hresource hnodup hsamples hempty
  dsimp only at hstrong
  exact hstrong.1

/--
Strengthened correctness theorem for the image-task fold.

Besides proving all image requests are completed, this records that every
image communication fact already true in the input accumulator remains
true in the output accumulator.
-/
lemma gpImageFold_correct_strong
    {base : State}
    (mailbox lander landerWaypoint : Obj)
    (goals : List (Obj × Obj))
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (htyped :
      ∀ q, q ∈ goals →
        acc.2.statics.objective_t q.1 = true ∧
        acc.2.statics.mode_t q.2 = true) :
    let out :=
      goals.foldl
        (fun a request =>
          gpImageTask
            mailbox lander landerWaypoint request a)
        acc
    (GPAccInv base out ∧
      GPImageDone goals out.2 ∧
      out.2.dynamic.communicated_soil_data_p =
        acc.2.dynamic.communicated_soil_data_p ∧
      out.2.dynamic.communicated_rock_data_p =
        acc.2.dynamic.communicated_rock_data_p) ∧
    (∀ o m,
      acc.2.dynamic.communicated_image_data_p o m = true →
      out.2.dynamic.communicated_image_data_p o m = true) := by
  dsimp only
  induction goals generalizing acc with
  | nil =>
      change
        (GPAccInv base acc ∧
          GPImageDone [] acc.2 ∧
          acc.2.dynamic.communicated_soil_data_p =
            acc.2.dynamic.communicated_soil_data_p ∧
          acc.2.dynamic.communicated_rock_data_p =
            acc.2.dynamic.communicated_rock_data_p) ∧
        (∀ o m,
          acc.2.dynamic.communicated_image_data_p o m = true →
          acc.2.dynamic.communicated_image_data_p o m = true)
      refine ⟨⟨hacc, ?_, rfl, rfl⟩, ?_⟩
      · simp [GPImageDone]
      · intro o m h
        exact h

  | cons request rest ih =>
      simp only [List.foldl]

      have hRequestTyped :
          acc.2.statics.objective_t request.1 = true ∧
          acc.2.statics.mode_t request.2 = true :=
        htyped request List.mem_cons_self

      let acc1 :=
        gpImageTask
          mailbox lander landerWaypoint request acc

      have htask :
          GPAccInv base acc1 ∧
          acc1.2.dynamic.communicated_image_data_p
              request.1 request.2 = true ∧
          (∀ o m,
            acc.2.dynamic.communicated_image_data_p o m = true →
            acc1.2.dynamic.communicated_image_data_p o m = true) ∧
          acc1.2.dynamic.communicated_soil_data_p =
            acc.2.dynamic.communicated_soil_data_p ∧
          acc1.2.dynamic.communicated_rock_data_p =
            acc.2.dynamic.communicated_rock_data_p := by
        simpa only [acc1] using
          (gpImageTask_correct
            (base := base)
            mailbox lander landerWaypoint request acc
            hacc hsite hRequestTyped.1 hRequestTyped.2)

      rcases htask with
        ⟨hacc1, hCommunicatedCurrent, hImageFrame,
         hSoilTask, hRockTask⟩

      have hstatAcc :
          acc.2.statics = base.statics := by
        calc
          acc.2.statics =
              (runPlan acc.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc.2.1
          _ = base.statics :=
            runPlan_statics acc.1 base

      have hstatAcc1 :
          acc1.2.statics = base.statics := by
        calc
          acc1.2.statics =
              (runPlan acc1.1 base).statics := by
            exact congrArg
              (fun st : State => st.statics)
              hacc1.2.1
          _ = base.statics :=
            runPlan_statics acc1.1 base

      have hstat1 :
          acc1.2.statics = acc.2.statics :=
        hstatAcc1.trans hstatAcc.symm

      have hsite1 :
          GPCommunicationSite
            acc1.2.statics mailbox lander landerWaypoint := by
        rw [hstat1]
        exact hsite

      have htyped1 :
          ∀ q, q ∈ rest →
            acc1.2.statics.objective_t q.1 = true ∧
            acc1.2.statics.mode_t q.2 = true := by
        intro q hq
        rw [hstat1]
        exact htyped q (List.mem_cons_of_mem request hq)

      have hrec :=
        ih
          (acc := acc1)
          hacc1
          hsite1
          htyped1

      rcases hrec with
        ⟨⟨haccFinal, hDoneRest, hSoilRec, hRockRec⟩,
         hImageRec⟩

      have hDoneCons :
          GPImageDone
            (request :: rest)
            (rest.foldl
              (fun a q =>
                gpImageTask
                  mailbox lander landerWaypoint q a)
              acc1).2 := by
        intro q hq
        rcases List.mem_cons.mp hq with hqeq | hqrest
        · subst q
          exact
            hImageRec
              request.1 request.2
              hCommunicatedCurrent
        · exact hDoneRest q hqrest

      refine ⟨?_, ?_⟩
      · exact
          ⟨haccFinal,
           hDoneCons,
           hSoilRec.trans hSoilTask,
           hRockRec.trans hRockTask⟩
      · intro o m h
        exact hImageRec o m (hImageFrame o m h)

/--
Correctness of folding all image tasks.
-/
lemma gpImageFold_correct
    {base : State}
    (mailbox lander landerWaypoint : Obj)
    (goals : List (Obj × Obj))
    (acc : List PlanAction × State)
    (hacc : GPAccInv base acc)
    (hsite :
      GPCommunicationSite
        acc.2.statics mailbox lander landerWaypoint)
    (htyped :
      ∀ q, q ∈ goals →
        acc.2.statics.objective_t q.1 = true ∧
        acc.2.statics.mode_t q.2 = true) :
    let out :=
      goals.foldl
        (fun a request =>
          gpImageTask
            mailbox lander landerWaypoint request a)
        acc
    GPAccInv base out ∧
    GPImageDone goals out.2 ∧
    out.2.dynamic.communicated_soil_data_p =
      acc.2.dynamic.communicated_soil_data_p ∧
    out.2.dynamic.communicated_rock_data_p =
      acc.2.dynamic.communicated_rock_data_p := by
  dsimp only
  have hstrong :=
    gpImageFold_correct_strong
      (base := base)
      mailbox lander landerWaypoint
      goals acc hacc hsite htyped
  dsimp only at hstrong
  exact hstrong.1

/-!
  Part 5: connecting the generated request lists to the original goal.
-/

/--
Completion of the enumerated soil requests covers every positive soil
communication goal.
-/
lemma gpSoilDone_covers_goal
    (s initialFinal : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (hdone :
      GPSoilDone
        (gpRequestedSoilWaypoints s g)
        initialFinal) :
    ∀ w,
      g.dynamic.communicated_soil_data_p w = some true →
      initialFinal.dynamic.communicated_soil_data_p w = true := by
  intro w hw
  apply hdone w
  exact gpRequestedSoilWaypoints_complete s g hgoal w hw

/--
Completion of the enumerated rock requests covers every positive rock
communication goal.
-/
lemma gpRockDone_covers_goal
    (s initialFinal : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (hdone :
      GPRockDone
        (gpRequestedRockWaypoints s g)
        initialFinal) :
    ∀ w,
      g.dynamic.communicated_rock_data_p w = some true →
      initialFinal.dynamic.communicated_rock_data_p w = true := by
  intro w hw
  apply hdone w
  exact gpRequestedRockWaypoints_complete s g hgoal w hw

/--
Completion of the enumerated image requests covers every positive image
communication goal.
-/
lemma gpImageDone_covers_goal
    (s initialFinal : State)
    (g : Goal)
    (hgoal : WellFormedGoal s g)
    (hdone :
      GPImageDone
        (gpRequestedImages s g)
        initialFinal) :
    ∀ o m,
      g.dynamic.communicated_image_data_p o m = some true →
      initialFinal.dynamic.communicated_image_data_p o m = true := by
  intro o m hreq
  exact
    hdone
      (o, m)
      (gpRequestedImages_complete s g hgoal o m hreq)

/--
Because a well-formed goal ignores every non-communication predicate and
permits only positive communication literals, covering all positive
communication literals is sufficient for `SatisfiesGoal`.
-/
lemma satisfiesGoal_of_communication_cover
    (initial final : State)
    (g : Goal)
    (hgoal : WellFormedGoal initial g)
    (hcover : GPCoversGoalCommunications final g) :
    SatisfiesGoal final g := by
  rcases hgoal with
    ⟨hStatic,
     hValidAt,
     hValidEmpty,
     hValidRock,
     hValidSoil,
     hValidFull,
     hValidCalibrated,
     hValidImage,
     hValidCommunicatedSoil,
     hValidCommunicatedRock,
     hValidCommunicatedImage,
     hValidAtSoil,
     hValidAtRock,
     hAtMostOneLocation,
     hEmptyFullExclusive,
     hSoilAnalysisInvariant,
     hRockAnalysisInvariant,
     hCalibratedInvariant,
     hImageEquippedInvariant,
     hSoilEquippedInvariant,
     hRockEquippedInvariant,
     hIgnoreAt,
     hIgnoreEmpty,
     hIgnoreFull,
     hIgnoreRock,
     hIgnoreSoil,
     hIgnoreCalibrated,
     hIgnoreImage,
     hIgnoreAtSoil,
     hIgnoreAtRock,
     hPositiveSoil,
     hPositiveRock,
     hPositiveImage,
     hSolvableSoil,
     hSolvableRock,
     hSolvableImage,
     hSoilSample,
     hRockSample⟩

  rcases hcover with
    ⟨hCoverSoil, hCoverRock, hCoverImage⟩

  unfold SatisfiesGoal
  refine
    ⟨?_, ?_, ?_, ?_, ?_, ?_,
     ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro r w
    rw [hIgnoreAt r w]
    trivial

  · intro st
    rw [hIgnoreEmpty st]
    trivial

  · intro r w
    rw [hIgnoreRock r w]
    trivial

  · intro r w
    rw [hIgnoreSoil r w]
    trivial

  · intro st
    rw [hIgnoreFull st]
    trivial

  · intro c r
    rw [hIgnoreCalibrated c r]
    trivial

  · intro r o m
    rw [hIgnoreImage r o m]
    trivial

  · intro w
    cases hopt :
        g.dynamic.communicated_soil_data_p w with
    | none =>
        simp
    | some b =>
        cases b with
        | false =>
            have hfalse : False :=
              hPositiveSoil w hopt
            exact hfalse.elim
        | true =>
            exact hCoverSoil w hopt

  · intro w
    cases hopt :
        g.dynamic.communicated_rock_data_p w with
    | none =>
        simp
    | some b =>
        cases b with
        | false =>
            have hfalse : False :=
              hPositiveRock w hopt
            exact hfalse.elim
        | true =>
            exact hCoverRock w hopt

  · intro o m
    cases hopt :
        g.dynamic.communicated_image_data_p o m with
    | none =>
        simp
    | some b =>
        cases b with
        | false =>
            have hfalse : False :=
              hPositiveImage o m hopt
            exact hfalse.elim
        | true =>
            exact hCoverImage o m hopt

  · intro w
    rw [hIgnoreAtSoil w]
    trivial

  · intro w
    rw [hIgnoreAtRock w]
    trivial

/--
The static state stored in any accumulator satisfying `GPAccInv` is the
static state of the base state.
-/
lemma gpAccInv_statics
    {base : State}
    {acc : List PlanAction × State}
    (hacc : GPAccInv base acc) :
    acc.2.statics = base.statics := by
  calc
    acc.2.statics =
        (runPlan acc.1 base).statics := by
      exact congrArg
        (fun st : State => st.statics)
        hacc.2.1
    _ = base.statics :=
      runPlan_statics acc.1 base

/--
This is the main construction lemma. It unfolds `solve`, applies the three
fold-correctness theorems in sequence, and transports already established
communication facts through the frame equalities of later folds.
-/
lemma solve_valid_and_covers
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    GPCoversGoalCommunications
      (runPlan (solve s g) s) g := by
  let objects := s.statics.objects

  let lander :=
    gpChooseObj objects (fun candidate =>
      s.statics.lander_t candidate)

  let landerWaypoint :=
    gpChooseObj objects (fun waypoint =>
      s.statics.at_lander_p lander waypoint)

  let mailbox :=
    gpChooseObj objects (fun waypoint =>
      s.statics.visible_p waypoint landerWaypoint)

  let soilGoals :=
    gpRequestedSoilWaypoints s g

  let rockGoals :=
    gpRequestedRockWaypoints s g

  let imageGoals :=
    gpRequestedImages s g

  let soilRover :=
    gpChooseObj objects (fun rover =>
      s.statics.equipped_for_soil_analysis_p rover)

  let soilStore :=
    gpChooseObj objects (fun store =>
      s.statics.store_of_p store soilRover)

  let rockRover :=
    gpChooseObj objects (fun rover =>
      s.statics.equipped_for_rock_analysis_p rover)

  let rockStore :=
    gpChooseObj objects (fun store =>
      s.statics.store_of_p store rockRover)

  let initialAccumulator : List PlanAction × State :=
    ([], s)

  let afterSoil :=
    soilGoals.foldl
      (fun acc waypoint =>
        gpSoilTask
          mailbox lander landerWaypoint
          soilRover soilStore waypoint
          acc)
      initialAccumulator

  let afterRock :=
    rockGoals.foldl
      (fun acc waypoint =>
        gpRockTask
          mailbox lander landerWaypoint
          rockRover rockStore waypoint
          acc)
      afterSoil

  let afterImages :=
    imageGoals.foldl
      (fun acc request =>
        gpImageTask
          mailbox lander landerWaypoint
          request acc)
      afterRock

  have hwf : WellFormed s :=
    hinit.1

  have hsite0 :
      GPCommunicationSite
        s.statics mailbox lander landerWaypoint := by
    simpa [objects, lander, landerWaypoint, mailbox] using
      (gpCommunicationSite_spec s hstatic)

  have hacc0 :
      GPAccInv s initialAccumulator := by
    simpa [initialAccumulator] using
      (gpAccInv_initial s hwf)

  have hsiteAcc0 :
      GPCommunicationSite
        initialAccumulator.2.statics
        mailbox lander landerWaypoint := by
    simpa [initialAccumulator] using hsite0

  have hsoilNodup :
      soilGoals.Nodup := by
    simpa [soilGoals] using
      (gpRequestedSoilWaypoints_nodup s g hstatic)

  have hsoilSamples0 :
      ∀ w, w ∈ soilGoals →
        s.dynamic.at_soil_sample_p w = true := by
    simpa [soilGoals] using
      (requested_soil_samples_initially_present s g hgoal)

  have hsoilSamplesAcc :
      ∀ w, w ∈ soilGoals →
        initialAccumulator.2.dynamic.at_soil_sample_p w = true := by
    simpa [initialAccumulator] using hsoilSamples0

  have hsoilResource0 :
      soilGoals ≠ [] →
      GPSoilResource s.statics soilRover soilStore := by
    intro hne
    have hex :
        ∃ r,
          s.statics.equipped_for_soil_analysis_p r = true :=
      soil_requests_have_equipped_rover
        s g hgoal (by simpa [soilGoals] using hne)
    simpa [objects, soilRover, soilStore] using
      (gpSoilResource_spec s hstatic hex)

  have hsoilResourceAcc :
      soilGoals ≠ [] →
      GPSoilResource
        initialAccumulator.2.statics soilRover soilStore := by
    intro hne
    simpa [initialAccumulator] using
      (hsoilResource0 hne)

  have hsoilEmptyAcc :
      soilGoals ≠ [] →
      initialAccumulator.2.dynamic.empty_p soilStore = true := by
    intro hne
    have hresource := hsoilResource0 hne
    unfold GPSoilResource at hresource
    rcases hresource with
      ⟨_, hStoreT, _, _⟩
    change s.dynamic.empty_p soilStore = true
    exact hinit.2.1 soilStore hStoreT

  have hsoilFold :
      GPAccInv s afterSoil ∧
      GPSoilDone soilGoals afterSoil.2 ∧
      afterSoil.2.dynamic.empty_p =
        s.dynamic.empty_p ∧
      afterSoil.2.dynamic.communicated_rock_data_p =
        s.dynamic.communicated_rock_data_p ∧
      afterSoil.2.dynamic.communicated_image_data_p =
        s.dynamic.communicated_image_data_p ∧
      afterSoil.2.dynamic.at_rock_sample_p =
        s.dynamic.at_rock_sample_p := by
    simpa [afterSoil, initialAccumulator] using
      (gpSoilFold_correct
        (base := s)
        mailbox lander landerWaypoint
        soilRover soilStore
        soilGoals initialAccumulator
        hacc0
        hsiteAcc0
        hsoilResourceAcc
        hsoilNodup
        hsoilSamplesAcc
        hsoilEmptyAcc)

  rcases hsoilFold with
    ⟨haccSoil, hsoilDone, hsoilEmpty,
     hsoilRockCommunication, hsoilImageCommunication,
     hsoilRockSamples⟩

  have hstatSoil :
      afterSoil.2.statics = s.statics :=
    gpAccInv_statics haccSoil

  have hsiteSoil :
      GPCommunicationSite
        afterSoil.2.statics
        mailbox lander landerWaypoint := by
    rw [hstatSoil]
    exact hsite0

  have hrockNodup :
      rockGoals.Nodup := by
    simpa [rockGoals] using
      (gpRequestedRockWaypoints_nodup s g hstatic)

  have hrockSamples0 :
      ∀ w, w ∈ rockGoals →
        s.dynamic.at_rock_sample_p w = true := by
    simpa [rockGoals] using
      (requested_rock_samples_initially_present s g hgoal)

  have hrockSamplesSoil :
      ∀ w, w ∈ rockGoals →
        afterSoil.2.dynamic.at_rock_sample_p w = true := by
    intro w hw
    rw [hsoilRockSamples]
    exact hrockSamples0 w hw

  have hrockResource0 :
      rockGoals ≠ [] →
      GPRockResource s.statics rockRover rockStore := by
    intro hne
    have hex :
        ∃ r,
          s.statics.equipped_for_rock_analysis_p r = true :=
      rock_requests_have_equipped_rover
        s g hgoal (by simpa [rockGoals] using hne)
    simpa [objects, rockRover, rockStore] using
      (gpRockResource_spec s hstatic hex)

  have hrockResourceSoil :
      rockGoals ≠ [] →
      GPRockResource
        afterSoil.2.statics rockRover rockStore := by
    intro hne
    rw [hstatSoil]
    exact hrockResource0 hne

  have hrockEmptySoil :
      rockGoals ≠ [] →
      afterSoil.2.dynamic.empty_p rockStore = true := by
    intro hne
    have hresource := hrockResource0 hne
    unfold GPRockResource at hresource
    rcases hresource with
      ⟨_, hStoreT, _, _⟩
    rw [hsoilEmpty]
    exact hinit.2.1 rockStore hStoreT

  have hrockFold :
      GPAccInv s afterRock ∧
      GPRockDone rockGoals afterRock.2 ∧
      afterRock.2.dynamic.empty_p =
        afterSoil.2.dynamic.empty_p ∧
      afterRock.2.dynamic.communicated_soil_data_p =
        afterSoil.2.dynamic.communicated_soil_data_p ∧
      afterRock.2.dynamic.communicated_image_data_p =
        afterSoil.2.dynamic.communicated_image_data_p := by
    simpa [afterRock] using
      (gpRockFold_correct
        (base := s)
        mailbox lander landerWaypoint
        rockRover rockStore
        rockGoals afterSoil
        haccSoil
        hsiteSoil
        hrockResourceSoil
        hrockNodup
        hrockSamplesSoil
        hrockEmptySoil)

  rcases hrockFold with
    ⟨haccRock, hrockDone, hrockEmpty,
     hrockSoilCommunication, hrockImageCommunication⟩

  have hsoilDoneRock :
      GPSoilDone soilGoals afterRock.2 := by
    intro w hw
    rw [hrockSoilCommunication]
    exact hsoilDone w hw

  have hstatRock :
      afterRock.2.statics = s.statics :=
    gpAccInv_statics haccRock

  have hsiteRock :
      GPCommunicationSite
        afterRock.2.statics
        mailbox lander landerWaypoint := by
    rw [hstatRock]
    exact hsite0

  have himageTyped0 :
      ∀ q, q ∈ imageGoals →
        s.statics.objective_t q.1 = true ∧
        s.statics.mode_t q.2 = true := by
    intro q hq
    rcases q with ⟨o, m⟩
    have hmem :
        (o, m) ∈ gpRequestedImages s g := by
      simpa [imageGoals] using hq
    have hsound :=
      gpRequestedImages_sound s g o m hmem hgoal
    exact ⟨hsound.2.1, hsound.2.2⟩

  have himageTypedRock :
      ∀ q, q ∈ imageGoals →
        afterRock.2.statics.objective_t q.1 = true ∧
        afterRock.2.statics.mode_t q.2 = true := by
    intro q hq
    rw [hstatRock]
    exact himageTyped0 q hq

  have himageFold :
      GPAccInv s afterImages ∧
      GPImageDone imageGoals afterImages.2 ∧
      afterImages.2.dynamic.communicated_soil_data_p =
        afterRock.2.dynamic.communicated_soil_data_p ∧
      afterImages.2.dynamic.communicated_rock_data_p =
        afterRock.2.dynamic.communicated_rock_data_p := by
    simpa [afterImages] using
      (gpImageFold_correct
        (base := s)
        mailbox lander landerWaypoint
        imageGoals afterRock
        haccRock
        hsiteRock
        himageTypedRock)

  rcases himageFold with
    ⟨haccImages, himageDone,
     himageSoilCommunication, himageRockCommunication⟩

  have hsoilDoneFinal :
      GPSoilDone soilGoals afterImages.2 := by
    intro w hw
    rw [himageSoilCommunication]
    exact hsoilDoneRock w hw

  have hrockDoneFinal :
      GPRockDone rockGoals afterImages.2 := by
    intro w hw
    rw [himageRockCommunication]
    exact hrockDone w hw

  have hcoverFinal :
      GPCoversGoalCommunications afterImages.2 g := by
    unfold GPCoversGoalCommunications
    refine ⟨?_, ?_, ?_⟩
    · exact
        gpSoilDone_covers_goal
          s afterImages.2 g hgoal
          (by simpa [soilGoals] using hsoilDoneFinal)
    · exact
        gpRockDone_covers_goal
          s afterImages.2 g hgoal
          (by simpa [rockGoals] using hrockDoneFinal)
    · exact
        gpImageDone_covers_goal
          s afterImages.2 g hgoal
          (by simpa [imageGoals] using himageDone)

  have hsolve :
      solve s g = afterImages.1 := by
    rfl

  constructor
  · rw [hsolve]
    exact haccImages.1
  · rw [hsolve]
    rw [← haccImages.2.1]
    exact hcoverFinal

theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  rcases
      solve_valid_and_covers s g hstatic hinit hgoal with
    ⟨hvalid, hcover⟩
  exact
    ⟨hvalid,
     satisfiesGoal_of_communication_cover
       s
       (runPlan (solve s g) s)
       g
       hgoal
       hcover⟩

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)

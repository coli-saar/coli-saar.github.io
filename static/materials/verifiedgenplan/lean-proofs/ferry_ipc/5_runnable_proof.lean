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
  car_t : Obj → Bool
  location_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_ferry_p : Obj → α
  at_p : Obj → Obj → α
  empty_ferry_p : α
  on_p : Obj → α

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
  (∀ x, s.car_t x = true → x ∈ s.objects) ∧
  (∀ x, s.location_t x = true → x ∈ s.objects) ∧
  (∀ x, s.car_t x = true → s.location_t x = false)

def MinObjNum (s : StaticState) : Prop :=
  ∃ c, s.car_t c = true ∧
  ∃ l, s.location_t l = true

def WellFormedStatic (s : StaticState) : Prop := 
  ObjectsUnique s ∧
  ValidTypeHierarchy s ∧
  MinObjNum s

def ValidAtFerryParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_l, Truthy.isTrue (d.at_ferry_p var_l) → s.location_t var_l = true

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_c var_l, Truthy.isTrue (d.at_p var_c var_l) → s.car_t var_c = true ∧ s.location_t var_l = true

def ValidOnParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_c, Truthy.isTrue (d.on_p var_c) → s.car_t var_c = true

def FerryCapacity {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ c1 c2, Truthy.isTrue (d.on_p c1) → Truthy.isTrue (d.on_p c2) → c1 = c2

def UniqueFerryLoc {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ l1 l2, Truthy.isTrue (d.at_ferry_p l1) → Truthy.isTrue (d.at_ferry_p l2) → l1 = l2

def EmptyFerryXor {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  (Truthy.isTrue d.empty_ferry_p → ¬∃ c, Truthy.isTrue (d.on_p c)) ∧
  ((∃ c, Truthy.isTrue (d.on_p c)) → ¬ Truthy.isTrue d.empty_ferry_p)

def CarOnXorAt {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ c, s.car_t c = true → ¬ (Truthy.isTrue (d.on_p c) ∧ ∃ l, Truthy.isTrue (d.at_p c l))

def CarUniqueLoc {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ c, s.car_t c = true → ∀ l1 l2, Truthy.isTrue (d.at_p c l1) → Truthy.isTrue (d.at_p c l2) → l1 = l2

def EachCarHasLoc (s : State) : Prop :=
     ∀ c, s.statics.car_t c = true →
    (s.dynamic.on_p c = true ∨ ∃ l, s.dynamic.at_p c l = true ∧ s.statics.location_t l = true)

def ExistsFerryLoc (s : State) : Prop :=
∃ l, s.dynamic.at_ferry_p l = true ∧ s.statics.location_t l = true

def WellFormed (s : State) : Prop := 
  WellFormedStatic s.statics ∧
  ValidAtFerryParam s.statics s.dynamic ∧
  ValidAtParam s.statics s.dynamic ∧
  ValidOnParam s.statics s.dynamic ∧
  FerryCapacity s.statics s.dynamic ∧
  UniqueFerryLoc s.statics s.dynamic ∧
  EmptyFerryXor s.statics s.dynamic ∧
  CarOnXorAt s.statics s.dynamic ∧
  CarUniqueLoc s.statics s.dynamic ∧
  EachCarHasLoc s ∧
  ExistsFerryLoc s

def InitEmptyFerry (s : State) : Prop :=
  s.dynamic.empty_ferry_p = true

def WellFormedInit (s : State) : Prop := 
  WellFormed s ∧
  InitEmptyFerry s

def GoalMoveAllCars (initial : State) (g : Goal) : Prop :=
  (∀ c, initial.statics.car_t c = true → ∃! l, initial.statics.location_t l = true ∧ g.dynamic.at_p c l = true) ∧
  (∀ c l, g.dynamic.at_p c l = true → initial.statics.car_t c = true ∧ initial.statics.location_t l = true)

def GoalIgnoreFerryLoc (initial : State) (g : Goal) : Prop :=
  ∀ l, g.dynamic.at_ferry_p l = none

def GoalNoCarOn (initial : State) (g : Goal) : Prop :=
  ∀ c, g.dynamic.on_p c = none

def GoalIgnoreEmpty (initial : State) (g : Goal) : Prop :=
  g.dynamic.empty_ferry_p.isNone

def GoalCarsOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ c l, g.dynamic.at_p c l ≠ some false

def WellFormedGoal (initial : State) (g : Goal) : Prop := 
  WellFormedStatic initial.statics ∧
  ValidAtFerryParam initial.statics g.dynamic ∧
  ValidAtParam initial.statics g.dynamic ∧
  ValidOnParam initial.statics g.dynamic ∧
  FerryCapacity initial.statics g.dynamic ∧
  UniqueFerryLoc initial.statics g.dynamic ∧
  EmptyFerryXor initial.statics g.dynamic ∧
  CarOnXorAt initial.statics g.dynamic ∧
  CarUniqueLoc initial.statics g.dynamic ∧
  GoalMoveAllCars initial g ∧
  GoalIgnoreFerryLoc initial g ∧
  GoalNoCarOn initial g ∧
  GoalIgnoreEmpty initial g ∧
  GoalCarsOnlyPositive initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_l,
    match g.dynamic.at_ferry_p var_l with
    | none => True
    | some b => s.dynamic.at_ferry_p var_l = b) ∧
  (∀ var_c var_l,
    match g.dynamic.at_p var_c var_l with
    | none => True
    | some b => s.dynamic.at_p var_c var_l = b) ∧
  (match g.dynamic.empty_ferry_p with
  | none => True
  | some b => s.dynamic.empty_ferry_p = b) ∧
  (∀ var_c,
    match g.dynamic.on_p var_c with
    | none => True
    | some b => s.dynamic.on_p var_c = b)

def sailPre (var_from : Obj) (var_to : Obj) (s : State) : Prop :=
  s.statics.location_t var_from = true ∧
  s.statics.location_t var_to = true ∧
  s.dynamic.at_ferry_p var_from = true ∧
  s.dynamic.at_ferry_p var_to = false

def boardPre (var_car : Obj) (var_loc : Obj) (s : State) : Prop :=
  s.statics.car_t var_car = true ∧
  s.statics.location_t var_loc = true ∧
  s.dynamic.at_p var_car var_loc = true ∧
  s.dynamic.at_ferry_p var_loc = true ∧
  s.dynamic.empty_ferry_p = true

def debarkPre (var_car : Obj) (var_loc : Obj) (s : State) : Prop :=
  s.statics.car_t var_car = true ∧
  s.statics.location_t var_loc = true ∧
  s.dynamic.on_p var_car = true ∧
  s.dynamic.at_ferry_p var_loc = true

def sail (var_from : Obj) (var_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_ferry_p :=
      fun var_to' =>
        if var_to' = var_to then
          true
        else if var_to' = var_from then
          false
        else
          s.dynamic.at_ferry_p var_to'
  }
}

def board (var_car : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_car' var_loc' =>
        if var_car' = var_car ∧ var_loc' = var_loc then
          false
        else
          s.dynamic.at_p var_car' var_loc',
    empty_ferry_p := false,
    on_p :=
      fun var_car' =>
        if var_car' = var_car then
          true
        else
          s.dynamic.on_p var_car'
  }
}

def debark (var_car : Obj) (var_loc : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_car' var_loc' =>
        if var_car' = var_car ∧ var_loc' = var_loc then
          true
        else
          s.dynamic.at_p var_car' var_loc',
    empty_ferry_p := true,
    on_p :=
      fun var_car' =>
        if var_car' = var_car then
          false
        else
          s.dynamic.on_p var_car'
  }
}

inductive PlanAction where
  | sail   (var_from : Obj) (var_to : Obj)
  | board  (var_car : Obj) (var_loc : Obj)
  | debark (var_car : Obj) (var_loc : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .sail   var_from var_to, s => sailPre var_from var_to s
  | .board  var_car var_loc, s => boardPre var_car var_loc s
  | .debark var_car var_loc, s => debarkPre var_car var_loc s

def actionApply : PlanAction → State → State
  | .sail   var_from var_to, s => sail var_from var_to s
  | .board  var_car var_loc, s => board var_car var_loc s
  | .debark var_car var_loc, s => debark var_car var_loc s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def findFerryLocation? (s : State) : Option Obj :=
  s.statics.objects.find? (fun l =>
    s.dynamic.at_ferry_p l)

def findCarLocation? (s : State) (c : Obj) : Option Obj :=
  s.statics.objects.find? (fun l =>
    s.dynamic.at_p c l)

def findCarGoalLocation? (s : State) (g : Goal) (c : Obj) : Option Obj :=
  s.statics.objects.find? (fun l =>
    match g.dynamic.at_p c l with
    | some true => true
    | _ => false)

def solveCars : List Obj → State → Goal → List PlanAction
  | [], _, _ => []
  | c :: cs, currentState, g =>
      match findCarLocation? currentState c,
            findCarGoalLocation? currentState g c with
      | some currentLocation, some goalLocation =>
          if currentLocation = goalLocation then
            solveCars cs currentState g
          else
            match findFerryLocation? currentState with
            | none =>
                solveCars cs currentState g
            | some ferryLocation =>
                let actions : List PlanAction :=
                  if ferryLocation = currentLocation then
                    [ .board c currentLocation,
                      .sail currentLocation goalLocation,
                      .debark c goalLocation ]
                  else
                    [ .sail ferryLocation currentLocation,
                      .board c currentLocation,
                      .sail currentLocation goalLocation,
                      .debark c goalLocation ]
                actions ++
                  solveCars cs (runPlan actions currentState) g
      | _, _ =>
          solveCars cs currentState g

def solve (s : State) (g : Goal) : List PlanAction :=
  let cars := s.statics.objects.filter (fun o =>
    s.statics.car_t o)
  solveCars cars s g

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

lemma sail_statics (var_from var_to : Obj) (s : State) :
    (sail var_from var_to s).statics = s.statics := rfl

lemma board_statics (var_car var_loc : Obj) (s : State) :
    (board var_car var_loc s).statics = s.statics := rfl

lemma debark_statics (var_car var_loc : Obj) (s : State) :
    (debark var_car var_loc s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | sail var_from var_to   => exact sail_statics var_from var_to s
      | board var_car var_loc  => exact board_statics var_car var_loc s
      | debark var_car var_loc => exact debark_statics var_car var_loc s

-- sail only touches at_ferry_p
lemma sail_at_ferry_p_ne (var_from var_to : Obj) (s : State) {var_to' : Obj} (h1 : var_to' ≠ var_to) (h2 : var_to' ≠ var_from) :
    (sail var_from var_to s).dynamic.at_ferry_p var_to' = s.dynamic.at_ferry_p var_to' := by
  unfold sail
  simp [h1, h2]

-- sail never touches at_p
lemma sail_at_p (var_from var_to : Obj) (s : State) :
    (sail var_from var_to s).dynamic.at_p = s.dynamic.at_p := rfl

-- sail never touches empty_ferry_p
lemma sail_empty_ferry_p (var_from var_to : Obj) (s : State) :
    (sail var_from var_to s).dynamic.empty_ferry_p = s.dynamic.empty_ferry_p := rfl

-- sail never touches on_p
lemma sail_on_p (var_from var_to : Obj) (s : State) :
    (sail var_from var_to s).dynamic.on_p = s.dynamic.on_p := rfl

-- board only touches on_p, at_p
lemma board_at_p_ne (var_car var_loc : Obj) (s : State) {var_car' var_loc' : Obj} (h1 : var_car' ≠ var_car) :
    (board var_car var_loc s).dynamic.at_p var_car' var_loc' = s.dynamic.at_p var_car' var_loc' := by
  unfold board
  simp [h1]

lemma board_at_p_ne_var_l (var_car var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (board var_car var_loc s).dynamic.at_p var_car var_loc' = s.dynamic.at_p var_car var_loc' := by
  unfold board
  simp [h1]

lemma board_on_p_ne (var_car var_loc : Obj) (s : State) {var_car' : Obj} (h1 : var_car' ≠ var_car) :
    (board var_car var_loc s).dynamic.on_p var_car' = s.dynamic.on_p var_car' := by
  unfold board
  simp [h1]

-- board never touches at_ferry_p
lemma board_at_ferry_p (var_car var_loc : Obj) (s : State) :
    (board var_car var_loc s).dynamic.at_ferry_p = s.dynamic.at_ferry_p := rfl

-- debark only touches at_p, on_p
lemma debark_at_p_ne (var_car var_loc : Obj) (s : State) {var_car' var_loc' : Obj} (h1 : var_car' ≠ var_car) :
    (debark var_car var_loc s).dynamic.at_p var_car' var_loc' = s.dynamic.at_p var_car' var_loc' := by
  unfold debark
  simp [h1]

lemma debark_at_p_ne_var_l (var_car var_loc : Obj) (s : State) {var_loc' : Obj} (h1 : var_loc' ≠ var_loc) :
    (debark var_car var_loc s).dynamic.at_p var_car var_loc' = s.dynamic.at_p var_car var_loc' := by
  unfold debark
  simp [h1]

lemma debark_on_p_ne (var_car var_loc : Obj) (s : State) {var_car' : Obj} (h1 : var_car' ≠ var_car) :
    (debark var_car var_loc s).dynamic.on_p var_car' = s.dynamic.on_p var_car' := by
  unfold debark
  simp [h1]

-- debark never touches at_ferry_p
lemma debark_at_ferry_p (var_car var_loc : Obj) (s : State) :
    (debark var_car var_loc s).dynamic.at_ferry_p = s.dynamic.at_ferry_p := rfl

lemma sail_at_ferry_p_eq1 (var_from var_to : Obj) (s : State) :
    (sail var_from var_to s).dynamic.at_ferry_p var_to = true := by
  unfold sail
  simp

lemma sail_at_ferry_p_eq2 (var_from var_to : Obj) (s : State) (h1 : var_from ≠ var_to) :
    (sail var_from var_to s).dynamic.at_ferry_p var_from = false := by
  unfold sail
  simp [h1]

lemma board_at_p_eq1 (var_car var_loc : Obj) (s : State) :
    (board var_car var_loc s).dynamic.at_p var_car var_loc = false := by
  unfold board
  simp

lemma board_empty_ferry_p (var_car var_loc : Obj) (s : State) :
    (board var_car var_loc s).dynamic.empty_ferry_p = false := by
  unfold board
  simp

lemma board_on_p_eq1 (var_car var_loc : Obj) (s : State) :
    (board var_car var_loc s).dynamic.on_p var_car = true := by
  unfold board
  simp

lemma debark_at_p_eq1 (var_car var_loc : Obj) (s : State) :
    (debark var_car var_loc s).dynamic.at_p var_car var_loc = true := by
  unfold debark
  simp

lemma debark_empty_ferry_p (var_car var_loc : Obj) (s : State) :
    (debark var_car var_loc s).dynamic.empty_ferry_p = true := by
  unfold debark
  simp

lemma debark_on_p_eq1 (var_car var_loc : Obj) (s : State) :
    (debark var_car var_loc s).dynamic.on_p var_car = false := by
  unfold debark
  simp

lemma sail_preserves_wf
    (var_from var_to)
    (s : State)
    (hwf : WellFormed s)
    (hpre : sailPre var_from var_to s) :
    WellFormed (sail var_from var_to s) := by
  rcases hwf with
    ⟨hStatic, hValidFerry, hValidAt, hValidOn, hCapacity,
      hUniqueFerry, hEmptyXor, hCarXor, hCarUnique, hEachCar, hFerryExists⟩
  rcases hpre with
    ⟨hLocFrom, hLocTo, hAtFrom, hAtToFalse⟩

  have hOnlyTo :
      ∀ l,
        (sail var_from var_to s).dynamic.at_ferry_p l = true →
        l = var_to := by
    intro l hl
    by_cases hto : l = var_to
    · exact hto
    · by_cases hfrom : l = var_from
      · subst l
        rw [sail_at_ferry_p_eq2 var_from var_to s hto] at hl
        simp at hl
      · rw [sail_at_ferry_p_ne var_from var_to s hto hfrom] at hl
        exfalso
        exact hfrom (hUniqueFerry l var_from hl hAtFrom)

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sail] using hStatic
  · intro l hl
    change (sail var_from var_to s).dynamic.at_ferry_p l = true at hl
    by_cases hto : l = var_to
    · subst l
      exact hLocTo
    · by_cases hfrom : l = var_from
      · subst l
        rw [sail_at_ferry_p_eq2 var_from var_to s hto] at hl
        simp at hl
      · rw [sail_at_ferry_p_ne var_from var_to s hto hfrom] at hl
        exact hValidFerry l hl
  · simpa [ValidAtParam, sail] using hValidAt
  · simpa [ValidOnParam, sail] using hValidOn
  · simpa [FerryCapacity, sail] using hCapacity
  · intro l1 l2 h1 h2
    change (sail var_from var_to s).dynamic.at_ferry_p l1 = true at h1
    change (sail var_from var_to s).dynamic.at_ferry_p l2 = true at h2
    exact (hOnlyTo l1 h1).trans (hOnlyTo l2 h2).symm
  · simpa [EmptyFerryXor, sail] using hEmptyXor
  · simpa [CarOnXorAt, sail] using hCarXor
  · simpa [CarUniqueLoc, sail] using hCarUnique
  · simpa [EachCarHasLoc, sail] using hEachCar
  · refine ⟨var_to, ?_, hLocTo⟩
    exact sail_at_ferry_p_eq1 var_from var_to s

lemma board_preserves_wf
    (var_car var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : boardPre var_car var_loc s) :
    WellFormed (board var_car var_loc s) := by
  rcases hwf with
    ⟨hStatic, hValidFerry, hValidAt, hValidOn, hCapacity,
      hUniqueFerry, hEmptyXor, hCarXor, hCarUnique, hEachCar, hFerryExists⟩
  rcases hpre with
    ⟨hCar, hLoc, hAtCarLoc, hFerryAtLoc, hEmpty⟩

  have hAtOld :
      ∀ c l,
        (board var_car var_loc s).dynamic.at_p c l = true →
        s.dynamic.at_p c l = true := by
    intro c l h
    by_cases hc : c = var_car
    · subst c
      by_cases hl : l = var_loc
      · subst l
        rw [board_at_p_eq1 var_car var_loc s] at h
        simp at h
      · rw [board_at_p_ne_var_l var_car var_loc s hl] at h
        exact h
    · rw [board_at_p_ne var_car var_loc s hc] at h
      exact h

  have hNoOldOn : ¬ ∃ c, s.dynamic.on_p c = true := by
    exact hEmptyXor.1 hEmpty

  have hOnOnly :
      ∀ c,
        (board var_car var_loc s).dynamic.on_p c = true →
        c = var_car := by
    intro c h
    by_cases hc : c = var_car
    · exact hc
    · rw [board_on_p_ne var_car var_loc s hc] at h
      exact (hNoOldOn ⟨c, h⟩).elim

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [board] using hStatic
  · simpa [ValidAtFerryParam, board] using hValidFerry
  · intro c l h
    change (board var_car var_loc s).dynamic.at_p c l = true at h
    exact hValidAt c l (hAtOld c l h)
  · intro c h
    change (board var_car var_loc s).dynamic.on_p c = true at h
    by_cases hc : c = var_car
    · subst c
      exact hCar
    · rw [board_on_p_ne var_car var_loc s hc] at h
      exact hValidOn c h
  · intro c1 c2 h1 h2
    change (board var_car var_loc s).dynamic.on_p c1 = true at h1
    change (board var_car var_loc s).dynamic.on_p c2 = true at h2
    exact (hOnOnly c1 h1).trans (hOnOnly c2 h2).symm
  · simpa [UniqueFerryLoc, board] using hUniqueFerry
  · constructor
    · intro h
      change (board var_car var_loc s).dynamic.empty_ferry_p = true at h
      rw [board_empty_ferry_p var_car var_loc s] at h
      simp at h
    · intro _
      intro h
      change (board var_car var_loc s).dynamic.empty_ferry_p = true at h
      rw [board_empty_ferry_p var_car var_loc s] at h
      simp at h
  · intro c hc
    rintro ⟨hOnNew, ⟨l, hAtNew⟩⟩
    change (board var_car var_loc s).dynamic.on_p c = true at hOnNew
    change (board var_car var_loc s).dynamic.at_p c l = true at hAtNew
    by_cases hcv : c = var_car
    · subst c
      by_cases hl : l = var_loc
      · subst l
        rw [board_at_p_eq1 var_car var_loc s] at hAtNew
        simp at hAtNew
      · rw [board_at_p_ne_var_l var_car var_loc s hl] at hAtNew
        exact hl (hCarUnique var_car hCar l var_loc hAtNew hAtCarLoc)
    · rw [board_on_p_ne var_car var_loc s hcv] at hOnNew
      rw [board_at_p_ne var_car var_loc s hcv] at hAtNew
      exact (hCarXor c hc) ⟨hOnNew, ⟨l, hAtNew⟩⟩
  · intro c hc l1 l2 h1 h2
    change (board var_car var_loc s).dynamic.at_p c l1 = true at h1
    change (board var_car var_loc s).dynamic.at_p c l2 = true at h2
    exact hCarUnique c hc l1 l2 (hAtOld c l1 h1) (hAtOld c l2 h2)
  · intro c hc
    by_cases hcv : c = var_car
    · subst c
      left
      exact board_on_p_eq1 var_car var_loc s
    · rcases hEachCar c hc with hOn | ⟨l, hAt, hLocType⟩
      · left
        rw [board_on_p_ne var_car var_loc s hcv]
        exact hOn
      · right
        refine ⟨l, ?_, hLocType⟩
        rw [board_at_p_ne var_car var_loc s hcv]
        exact hAt
  · simpa [ExistsFerryLoc, board] using hFerryExists

lemma debark_preserves_wf
    (var_car var_loc)
    (s : State)
    (hwf : WellFormed s)
    (hpre : debarkPre var_car var_loc s) :
    WellFormed (debark var_car var_loc s) := by
  rcases hwf with
    ⟨hStatic, hValidFerry, hValidAt, hValidOn, hCapacity,
      hUniqueFerry, hEmptyXor, hCarXor, hCarUnique, hEachCar, hFerryExists⟩
  rcases hpre with
    ⟨hCar, hLoc, hOnCar, hFerryAtLoc⟩

  have hOnOld :
      ∀ c,
        (debark var_car var_loc s).dynamic.on_p c = true →
        s.dynamic.on_p c = true := by
    intro c h
    by_cases hc : c = var_car
    · subst c
      rw [debark_on_p_eq1 var_car var_loc s] at h
      simp at h
    · rw [debark_on_p_ne var_car var_loc s hc] at h
      exact h

  have hNoNewOn :
      ¬ ∃ c, (debark var_car var_loc s).dynamic.on_p c = true := by
    rintro ⟨c, hc⟩
    have hOld : s.dynamic.on_p c = true := hOnOld c hc
    have heq : c = var_car := hCapacity c var_car hOld hOnCar
    subst c
    rw [debark_on_p_eq1 var_car var_loc s] at hc
    simp at hc

  have hOldNoAtCar : ¬ ∃ l, s.dynamic.at_p var_car l = true := by
    intro hAt
    exact (hCarXor var_car hCar) ⟨hOnCar, hAt⟩

  have hAtCarOnly :
      ∀ l,
        (debark var_car var_loc s).dynamic.at_p var_car l = true →
        l = var_loc := by
    intro l h
    by_cases hl : l = var_loc
    · exact hl
    · rw [debark_at_p_ne_var_l var_car var_loc s hl] at h
      exact (hOldNoAtCar ⟨l, h⟩).elim

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [debark] using hStatic
  · simpa [ValidAtFerryParam, debark] using hValidFerry
  · intro c l h
    change (debark var_car var_loc s).dynamic.at_p c l = true at h
    by_cases hc : c = var_car
    · subst c
      by_cases hl : l = var_loc
      · subst l
        exact ⟨hCar, hLoc⟩
      · rw [debark_at_p_ne_var_l var_car var_loc s hl] at h
        exact hValidAt var_car l h
    · rw [debark_at_p_ne var_car var_loc s hc] at h
      exact hValidAt c l h
  · intro c h
    change (debark var_car var_loc s).dynamic.on_p c = true at h
    exact hValidOn c (hOnOld c h)
  · intro c1 c2 h1 h2
    change (debark var_car var_loc s).dynamic.on_p c1 = true at h1
    change (debark var_car var_loc s).dynamic.on_p c2 = true at h2
    exact hCapacity c1 c2 (hOnOld c1 h1) (hOnOld c2 h2)
  · simpa [UniqueFerryLoc, debark] using hUniqueFerry
  · constructor
    · intro _
      intro hExists
      exact hNoNewOn hExists
    · intro hExists
      intro _
      exact hNoNewOn hExists
  · intro c hc
    rintro ⟨hOnNew, ⟨l, hAtNew⟩⟩
    change (debark var_car var_loc s).dynamic.on_p c = true at hOnNew
    change (debark var_car var_loc s).dynamic.at_p c l = true at hAtNew
    by_cases hcv : c = var_car
    · subst c
      rw [debark_on_p_eq1 var_car var_loc s] at hOnNew
      simp at hOnNew
    · rw [debark_on_p_ne var_car var_loc s hcv] at hOnNew
      rw [debark_at_p_ne var_car var_loc s hcv] at hAtNew
      exact (hCarXor c hc) ⟨hOnNew, ⟨l, hAtNew⟩⟩
  · intro c hc l1 l2 h1 h2
    change (debark var_car var_loc s).dynamic.at_p c l1 = true at h1
    change (debark var_car var_loc s).dynamic.at_p c l2 = true at h2
    by_cases hcv : c = var_car
    · subst c
      exact (hAtCarOnly l1 h1).trans (hAtCarOnly l2 h2).symm
    · rw [debark_at_p_ne var_car var_loc s hcv] at h1
      rw [debark_at_p_ne var_car var_loc s hcv] at h2
      exact hCarUnique c hc l1 l2 h1 h2
  · intro c hc
    by_cases hcv : c = var_car
    · subst c
      right
      refine ⟨var_loc, ?_, hLoc⟩
      exact debark_at_p_eq1 var_car var_loc s
    · rcases hEachCar c hc with hOn | ⟨l, hAt, hLocType⟩
      · left
        rw [debark_on_p_ne var_car var_loc s hcv]
        exact hOn
      · right
        refine ⟨l, ?_, hLocType⟩
        rw [debark_at_p_ne var_car var_loc s hcv]
        exact hAt
  · simpa [ExistsFerryLoc, debark] using hFerryExists

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | sail var_from var_to =>
      exact sail_preserves_wf var_from var_to s hwf hpre
  | board var_car var_loc =>
      exact board_preserves_wf var_car var_loc s hwf hpre
  | debark var_car var_loc =>
      exact debark_preserves_wf var_car var_loc s hwf hpre

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

lemma bool_eq_false_of_ne_true (b : Bool) (h : b ≠ true) :
    b = false := by
  cases b <;> simp_all

lemma find?_exists_of_exists_true
    {α : Type}
    (xs : List α)
    (p : α → Bool)
    (h : ∃ x, x ∈ xs ∧ p x = true) :
    ∃ x, xs.find? p = some x := by
  induction xs with
  | nil =>
      simp at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · exact ⟨a, by simp [List.find?, ha]⟩
      · have haf : p a = false :=
          bool_eq_false_of_ne_true (p a) ha
        have htail : ∃ x, x ∈ xs ∧ p x = true := by
          rcases h with ⟨x, hx, hpx⟩
          rcases List.mem_cons.mp hx with hx | hx
          · subst x
            exact (ha hpx).elim
          · exact ⟨x, hx, hpx⟩
        rcases ih htail with ⟨x, hx⟩
        exact ⟨x, by simp [List.find?, haf, hx]⟩

lemma find?_pred_of_eq_some
    {α : Type}
    {xs : List α}
    {p : α → Bool}
    {x : α}
    (h : xs.find? p = some x) :
    p x = true := by
  induction xs with
  | nil =>
      simp [List.find?] at h
  | cons a xs ih =>
      by_cases ha : p a = true
      · simp [List.find?, ha] at h
        subst x
        exact ha
      · have haf : p a = false :=
          bool_eq_false_of_ne_true (p a) ha
        simp [List.find?, haf] at h
        exact ih h

lemma moveCar3_correct
    (c currentLocation goalLocation : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hcar : s.statics.car_t c = true)
    (hCurrentLoc : s.statics.location_t currentLocation = true)
    (hGoalLoc : s.statics.location_t goalLocation = true)
    (hAtCurrent : s.dynamic.at_p c currentLocation = true)
    (hFerryCurrent : s.dynamic.at_ferry_p currentLocation = true)
    (hEmpty : s.dynamic.empty_ferry_p = true)
    (hFerryGoalFalse : s.dynamic.at_ferry_p goalLocation = false)
    (hne : currentLocation ≠ goalLocation) :
    let actions : List PlanAction :=
      [.board c currentLocation,
       .sail currentLocation goalLocation,
       .debark c goalLocation]
    ValidPlan actions s ∧
    WellFormed (runPlan actions s) ∧
    (runPlan actions s).dynamic.empty_ferry_p = true ∧
    (runPlan actions s).dynamic.at_p c goalLocation = true ∧
    (∀ c', c' ≠ c → ∀ l,
      (runPlan actions s).dynamic.at_p c' l =
        s.dynamic.at_p c' l) := by
  dsimp
  have hboard : boardPre c currentLocation s :=
    ⟨hcar, hCurrentLoc, hAtCurrent, hFerryCurrent, hEmpty⟩

  have hsail :
      sailPre currentLocation goalLocation
        (board c currentLocation s) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [board] using hCurrentLoc
    · simpa [board] using hGoalLoc
    · simpa [board] using hFerryCurrent
    · simpa [board] using hFerryGoalFalse

  have hdebark :
      debarkPre c goalLocation
        (sail currentLocation goalLocation
          (board c currentLocation s)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [sail, board] using hcar
    · simpa [sail, board] using hGoalLoc
    · simp [sail, board]
    · simp [sail, board]

  have hvalid :
      ValidPlan
        [.board c currentLocation,
         .sail currentLocation goalLocation,
         .debark c goalLocation] s := by
    simp only [ValidPlan, actionPre, actionApply]
    exact ⟨hboard, hsail, hdebark, trivial⟩

  refine
    ⟨hvalid, validPlan_preserves_wf hvalid hwf, ?_, ?_, ?_⟩
  · simp [runPlan, actionApply, debark]
  · simp [runPlan, actionApply, debark]
  · intro c' hc' l
    simp [runPlan, actionApply, board, sail, debark, hc']

lemma moveCar4_correct
    (c ferryLocation currentLocation goalLocation : Obj)
    (s : State)
    (hwf : WellFormed s)
    (hcar : s.statics.car_t c = true)
    (hFerryLoc : s.statics.location_t ferryLocation = true)
    (hCurrentLoc : s.statics.location_t currentLocation = true)
    (hGoalLoc : s.statics.location_t goalLocation = true)
    (hAtCurrent : s.dynamic.at_p c currentLocation = true)
    (hFerryAt : s.dynamic.at_ferry_p ferryLocation = true)
    (hEmpty : s.dynamic.empty_ferry_p = true)
    (hFerryCurrentNe : ferryLocation ≠ currentLocation)
    (hCurrentGoalNe : currentLocation ≠ goalLocation) :
    let actions : List PlanAction :=
      [.sail ferryLocation currentLocation,
       .board c currentLocation,
       .sail currentLocation goalLocation,
       .debark c goalLocation]
    ValidPlan actions s ∧
    WellFormed (runPlan actions s) ∧
    (runPlan actions s).dynamic.empty_ferry_p = true ∧
    (runPlan actions s).dynamic.at_p c goalLocation = true ∧
    (∀ c', c' ≠ c → ∀ l,
      (runPlan actions s).dynamic.at_p c' l =
        s.dynamic.at_p c' l) := by
  dsimp

  have hwfParts : WellFormed s := hwf
  rcases hwfParts with
    ⟨_, _, _, _, _, hUniqueFerry, _, _, _, _, _⟩

  have hFerryCurrentFalse :
      s.dynamic.at_ferry_p currentLocation = false := by
    apply bool_eq_false_of_ne_true
    intro hAtCurrentFerry
    exact hFerryCurrentNe
      (hUniqueFerry
        ferryLocation currentLocation hFerryAt hAtCurrentFerry)

  have hFirstPre :
      sailPre ferryLocation currentLocation s :=
    ⟨hFerryLoc, hCurrentLoc, hFerryAt, hFerryCurrentFalse⟩

  let s₁ := sail ferryLocation currentLocation s

  have hwf₁ : WellFormed s₁ := by
    exact sail_preserves_wf
      ferryLocation currentLocation s hwf hFirstPre

  have hGoalAfterFirst :
      s₁.dynamic.at_ferry_p goalLocation = false := by
    by_cases hGoalFerry : goalLocation = ferryLocation
    · subst goalLocation
      exact sail_at_ferry_p_eq2
        ferryLocation currentLocation s hFerryCurrentNe
    · have hGoalCurrent : goalLocation ≠ currentLocation := by
        intro h
        exact hCurrentGoalNe h.symm
      have hOldGoalFalse :
          s.dynamic.at_ferry_p goalLocation = false := by
        apply bool_eq_false_of_ne_true
        intro hAtGoal
        have heq :=
          hUniqueFerry ferryLocation goalLocation hFerryAt hAtGoal
        exact hGoalFerry heq.symm
      rw [sail_at_ferry_p_ne
        ferryLocation currentLocation s hGoalCurrent hGoalFerry]
      exact hOldGoalFalse

  have hThree :=
    moveCar3_correct
      c currentLocation goalLocation s₁ hwf₁
      (by simpa [s₁, sail] using hcar)
      (by simpa [s₁, sail] using hCurrentLoc)
      (by simpa [s₁, sail] using hGoalLoc)
      (by simpa [s₁, sail] using hAtCurrent)
      (by
        dsimp [s₁]
        exact sail_at_ferry_p_eq1
          ferryLocation currentLocation s)
      (by simpa [s₁, sail] using hEmpty)
      hGoalAfterFirst
      hCurrentGoalNe

  rcases hThree with
    ⟨hValidThree, hWfThree, hEmptyThree,
      hAtGoalThree, hOtherThree⟩

  have hValidFour :
      ValidPlan
        [.sail ferryLocation currentLocation,
         .board c currentLocation,
         .sail currentLocation goalLocation,
         .debark c goalLocation] s := by
    change
      sailPre ferryLocation currentLocation s ∧
      ValidPlan
        [.board c currentLocation,
         .sail currentLocation goalLocation,
         .debark c goalLocation]
        (sail ferryLocation currentLocation s)
    exact ⟨hFirstPre, hValidThree⟩

  refine ⟨hValidFour, ?_, ?_, ?_, ?_⟩
  · simpa [runPlan, actionApply, s₁] using hWfThree
  · simpa [runPlan, actionApply, s₁] using hEmptyThree
  · simpa [runPlan, actionApply, s₁] using hAtGoalThree
  · intro c' hc' l
    calc
      (runPlan
          [.sail ferryLocation currentLocation,
           .board c currentLocation,
           .sail currentLocation goalLocation,
           .debark c goalLocation] s).dynamic.at_p c' l =
          s₁.dynamic.at_p c' l := by
            simpa [runPlan, actionApply, s₁] using
              hOtherThree c' hc' l
      _ = s.dynamic.at_p c' l := by
        rfl

lemma solveCars_correct_aux
    (cs : List Obj)
    (currentState : State)
    (g : Goal)
    (hnodup : cs.Nodup)
    (hcars :
      ∀ c, c ∈ cs →
        currentState.statics.car_t c = true)
    (hwf : WellFormed currentState)
    (hempty :
      currentState.dynamic.empty_ferry_p = true)
    (htarget :
      ∀ c, currentState.statics.car_t c = true →
        ∃! l,
          currentState.statics.location_t l = true ∧
          g.dynamic.at_p c l = some true)
    (hgoalValid :
      ValidAtParam currentState.statics g.dynamic) :
    ValidPlan (solveCars cs currentState g) currentState ∧
    WellFormed
      (runPlan (solveCars cs currentState g) currentState) ∧
    (runPlan (solveCars cs currentState g) currentState).dynamic.empty_ferry_p =
      true ∧
    (∀ c, c ∈ cs → ∀ l,
      g.dynamic.at_p c l = some true →
      (runPlan (solveCars cs currentState g) currentState).dynamic.at_p c l =
        true) ∧
    (∀ c, c ∉ cs → ∀ l,
      (runPlan (solveCars cs currentState g) currentState).dynamic.at_p c l =
        currentState.dynamic.at_p c l) := by
  induction cs generalizing currentState with
  | nil =>
      simp only [solveCars, runPlan]
      refine ⟨trivial, hwf, hempty, ?_, ?_⟩
      · intro c hc
        simp at hc
      · intro c _ l
        trivial

  | cons c cs ih =>
      have ⟨hcNotMem, hnodupTail⟩ :=
        List.nodup_cons.mp hnodup

      have hcar :
          currentState.statics.car_t c = true :=
        hcars c (by simp)

      have hwfParts : WellFormed currentState := hwf
      rcases hwfParts with
        ⟨hStatic, hValidFerry, hValidAt, _, _, hUniqueFerry,
          hEmptyXor, _, _, hEachCar, hFerryExists⟩

      have hNoOn :
          ¬ ∃ x, currentState.dynamic.on_p x = true :=
        hEmptyXor.1 hempty

      have hCurrentExists :
          ∃ l,
            l ∈ currentState.statics.objects ∧
            currentState.dynamic.at_p c l = true := by
        rcases hEachCar c hcar with hOn | ⟨l, hAt, hLoc⟩
        · exact (hNoOn ⟨c, hOn⟩).elim
        · have hMem :
              l ∈ currentState.statics.objects :=
            hStatic.2.1.2.1 l hLoc
          exact ⟨l, hMem, hAt⟩

      have hFindCurrentExists :
          ∃ l, findCarLocation? currentState c = some l := by
        unfold findCarLocation?
        exact find?_exists_of_exists_true
          currentState.statics.objects
          (fun l => currentState.dynamic.at_p c l)
          hCurrentExists

      rcases hFindCurrentExists with
        ⟨currentLocation, hFindCurrent⟩

      have hAtCurrent :
          currentState.dynamic.at_p c currentLocation = true := by
        unfold findCarLocation? at hFindCurrent
        exact find?_pred_of_eq_some hFindCurrent

      have hCurrentLoc :
          currentState.statics.location_t currentLocation = true :=
        (hValidAt c currentLocation hAtCurrent).2

      obtain ⟨targetLocation, hTargetLocation, _⟩ :=
        htarget c hcar

      have hTargetMem :
          targetLocation ∈ currentState.statics.objects :=
        hStatic.2.1.2.1 targetLocation hTargetLocation.1

      have hFindGoalExists :
          ∃ l, findCarGoalLocation? currentState g c = some l := by
        unfold findCarGoalLocation?
        apply find?_exists_of_exists_true
        exact
          ⟨targetLocation, hTargetMem, by
            simp [hTargetLocation.2]⟩

      rcases hFindGoalExists with
        ⟨goalLocation, hFindGoal⟩

      have hGoalPred :
          (match g.dynamic.at_p c goalLocation with
           | some true => true
           | _ => false) = true := by
        unfold findCarGoalLocation? at hFindGoal
        exact find?_pred_of_eq_some
          (xs := currentState.statics.objects)
          (p := fun l =>
            match g.dynamic.at_p c l with
            | some true => true
            | _ => false)
          hFindGoal

      have hGoalAt :
          g.dynamic.at_p c goalLocation = some true := by
        cases h : g.dynamic.at_p c goalLocation with
        | none =>
            simp [h] at hGoalPred
        | some b =>
            cases b <;> simp [h] at hGoalPred ⊢

      have hGoalLoc :
          currentState.statics.location_t goalLocation = true :=
        (hgoalValid c goalLocation hGoalAt).2

      have hGoalUnique :
          ∀ l, g.dynamic.at_p c l = some true →
            l = goalLocation := by
        intro l hl
        have hLoc := (hgoalValid c l hl).2
        exact
          (htarget c hcar).unique
            ⟨hLoc, hl⟩
            ⟨hGoalLoc, hGoalAt⟩

      have hFerryExistsInObjects :
          ∃ l,
            l ∈ currentState.statics.objects ∧
            currentState.dynamic.at_ferry_p l = true := by
        rcases hFerryExists with ⟨l, hAt, hLoc⟩
        have hMem :
            l ∈ currentState.statics.objects :=
          hStatic.2.1.2.1 l hLoc
        exact ⟨l, hMem, hAt⟩

      have hFindFerryExists :
          ∃ l, findFerryLocation? currentState = some l := by
        unfold findFerryLocation?
        exact find?_exists_of_exists_true
          currentState.statics.objects
          currentState.dynamic.at_ferry_p
          hFerryExistsInObjects

      rcases hFindFerryExists with
        ⟨ferryLocation, hFindFerry⟩

      have hAtFerry :
          currentState.dynamic.at_ferry_p ferryLocation = true := by
        unfold findFerryLocation? at hFindFerry
        exact find?_pred_of_eq_some hFindFerry

      have hFerryLoc :
          currentState.statics.location_t ferryLocation = true :=
        hValidFerry ferryLocation hAtFerry

      rw [solveCars, hFindCurrent, hFindGoal]
      simp only

      by_cases hCurrentGoal :
          currentLocation = goalLocation

      · simp only [if_pos hCurrentGoal]

        have hcarsTail :
            ∀ x, x ∈ cs →
              currentState.statics.car_t x = true := by
          intro x hx
          exact hcars x (List.mem_cons_of_mem c hx)

        have hrec :=
          ih currentState hnodupTail hcarsTail
            hwf hempty htarget hgoalValid

        rcases hrec with
          ⟨hValidRec, hWfRec, hEmptyRec,
            hGoalsRec, hOtherRec⟩

        refine
          ⟨hValidRec, hWfRec, hEmptyRec, ?_, ?_⟩

        · intro x hx l hGoal
          rcases List.mem_cons.mp hx with hxHead | hxTail
          · subst x
            calc
              (runPlan
                (solveCars cs currentState g)
                currentState).dynamic.at_p c l =
                  currentState.dynamic.at_p c l :=
                    hOtherRec c hcNotMem l
              _ = true := by
                have hl : l = goalLocation :=
                  hGoalUnique l hGoal
                rw [hl, ← hCurrentGoal]
                exact hAtCurrent
          · exact hGoalsRec x hxTail l hGoal

        · intro x hx l
          exact hOtherRec x (by
            intro hmem
            exact hx (List.mem_cons_of_mem c hmem)) l

      · simp only [if_neg hCurrentGoal, hFindFerry]

        by_cases hFerryCurrent :
            ferryLocation = currentLocation

        · simp only [if_pos hFerryCurrent]

          have hAtFerryCurrent :
              currentState.dynamic.at_ferry_p currentLocation = true := by
            simpa [hFerryCurrent] using hAtFerry

          let actions : List PlanAction :=
            [.board c currentLocation,
             .sail currentLocation goalLocation,
             .debark c goalLocation]

          have hFerryGoalFalse :
              currentState.dynamic.at_ferry_p goalLocation = false := by
            apply bool_eq_false_of_ne_true
            intro hAtGoalFerry
            have heq :=
              hUniqueFerry
                currentLocation goalLocation
                hAtFerryCurrent hAtGoalFerry
            exact hCurrentGoal heq

          have hmove :=
            moveCar3_correct
              c currentLocation goalLocation currentState hwf
              hcar hCurrentLoc hGoalLoc hAtCurrent
              hAtFerryCurrent hempty hFerryGoalFalse
              hCurrentGoal

          rcases hmove with
            ⟨hValidMove, hWfMove, hEmptyMove,
              hAtGoalMove, hOtherMove⟩

          let nextState := runPlan actions currentState

          have hStatics :
              nextState.statics = currentState.statics := by
            exact runPlan_statics actions currentState

          have hcarsTail :
              ∀ x, x ∈ cs →
                nextState.statics.car_t x = true := by
            intro x hx
            rw [hStatics]
            exact hcars x (List.mem_cons_of_mem c hx)

          have htargetNext :
              ∀ x, nextState.statics.car_t x = true →
                ∃! l,
                  nextState.statics.location_t l = true ∧
                  g.dynamic.at_p x l = some true := by
            rw [hStatics]
            exact htarget

          have hgoalValidNext :
              ValidAtParam nextState.statics g.dynamic := by
            rw [hStatics]
            exact hgoalValid

          have hrec :=
            ih nextState hnodupTail hcarsTail
              hWfMove hEmptyMove htargetNext hgoalValidNext

          rcases hrec with
            ⟨hValidRec, hWfRec, hEmptyRec,
              hGoalsRec, hOtherRec⟩

          have hValidCombined :
              ValidPlan
                (actions ++ solveCars cs nextState g)
                currentState :=
            (validPlan_append
              actions (solveCars cs nextState g)
              currentState).2
              ⟨hValidMove, hValidRec⟩

          refine
            ⟨by simpa [actions, nextState] using hValidCombined,
             ?_, ?_, ?_, ?_⟩

          · change
              WellFormed
                (runPlan
                  (actions ++ solveCars cs nextState g)
                  currentState)
            rw [runPlan_append]
            exact hWfRec

          · change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.empty_ferry_p = true
            rw [runPlan_append]
            exact hEmptyRec

          · intro x hx l hGoal
            change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.at_p x l = true
            rw [runPlan_append]
            rcases List.mem_cons.mp hx with hxHead | hxTail
            · subst x
              calc
                (runPlan
                    (solveCars cs nextState g)
                    nextState).dynamic.at_p c l =
                    nextState.dynamic.at_p c l :=
                      hOtherRec c hcNotMem l
                _ = true := by
                  have hl : l = goalLocation :=
                    hGoalUnique l hGoal
                  rw [hl]
                  exact hAtGoalMove
            · exact hGoalsRec x hxTail l hGoal

          · intro x hx l
            have hxHead : x ≠ c := by
              intro hxc
              apply hx
              rw [hxc]
              simp
            have hxTail : x ∉ cs := by
              intro hmem
              exact hx (List.mem_cons_of_mem c hmem)
            change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.at_p x l =
                currentState.dynamic.at_p x l
            rw [runPlan_append]
            calc
              (runPlan
                  (solveCars cs nextState g)
                  nextState).dynamic.at_p x l =
                  nextState.dynamic.at_p x l :=
                    hOtherRec x hxTail l
              _ = currentState.dynamic.at_p x l :=
                hOtherMove x hxHead l

        · simp only [if_neg hFerryCurrent]

          let actions : List PlanAction :=
            [.sail ferryLocation currentLocation,
             .board c currentLocation,
             .sail currentLocation goalLocation,
             .debark c goalLocation]

          have hmove :=
            moveCar4_correct
              c ferryLocation currentLocation goalLocation
              currentState hwf hcar hFerryLoc hCurrentLoc
              hGoalLoc hAtCurrent hAtFerry hempty
              hFerryCurrent hCurrentGoal

          rcases hmove with
            ⟨hValidMove, hWfMove, hEmptyMove,
              hAtGoalMove, hOtherMove⟩

          let nextState := runPlan actions currentState

          have hStatics :
              nextState.statics = currentState.statics := by
            exact runPlan_statics actions currentState

          have hcarsTail :
              ∀ x, x ∈ cs →
                nextState.statics.car_t x = true := by
            intro x hx
            rw [hStatics]
            exact hcars x (List.mem_cons_of_mem c hx)

          have htargetNext :
              ∀ x, nextState.statics.car_t x = true →
                ∃! l,
                  nextState.statics.location_t l = true ∧
                  g.dynamic.at_p x l = some true := by
            rw [hStatics]
            exact htarget

          have hgoalValidNext :
              ValidAtParam nextState.statics g.dynamic := by
            rw [hStatics]
            exact hgoalValid

          have hrec :=
            ih nextState hnodupTail hcarsTail
              hWfMove hEmptyMove htargetNext hgoalValidNext

          rcases hrec with
            ⟨hValidRec, hWfRec, hEmptyRec,
              hGoalsRec, hOtherRec⟩

          have hValidCombined :
              ValidPlan
                (actions ++ solveCars cs nextState g)
                currentState :=
            (validPlan_append
              actions (solveCars cs nextState g)
              currentState).2
              ⟨hValidMove, hValidRec⟩

          refine
            ⟨by simpa [actions, nextState] using hValidCombined,
             ?_, ?_, ?_, ?_⟩

          · change
              WellFormed
                (runPlan
                  (actions ++ solveCars cs nextState g)
                  currentState)
            rw [runPlan_append]
            exact hWfRec

          · change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.empty_ferry_p = true
            rw [runPlan_append]
            exact hEmptyRec

          · intro x hx l hGoal
            change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.at_p x l = true
            rw [runPlan_append]
            rcases List.mem_cons.mp hx with hxHead | hxTail
            · subst x
              calc
                (runPlan
                    (solveCars cs nextState g)
                    nextState).dynamic.at_p c l =
                    nextState.dynamic.at_p c l :=
                      hOtherRec c hcNotMem l
                _ = true := by
                  have hl : l = goalLocation :=
                    hGoalUnique l hGoal
                  rw [hl]
                  exact hAtGoalMove
            · exact hGoalsRec x hxTail l hGoal

          · intro x hx l
            have hxHead : x ≠ c := by
              intro hxc
              apply hx
              rw [hxc]
              simp
            have hxTail : x ∉ cs := by
              intro hmem
              exact hx (List.mem_cons_of_mem c hmem)
            change
              (runPlan
                (actions ++ solveCars cs nextState g)
                currentState).dynamic.at_p x l =
                currentState.dynamic.at_p x l
            rw [runPlan_append]
            calc
              (runPlan
                  (solveCars cs nextState g)
                  nextState).dynamic.at_p x l =
                  nextState.dynamic.at_p x l :=
                    hOtherRec x hxTail l
              _ = currentState.dynamic.at_p x l :=
                hOtherMove x hxHead l

-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  rcases hinit with ⟨hwf, hempty⟩
  rcases hgoal with
    ⟨_, _, hGoalValidAt, _, _, _, _, _, _,
      hMoveAll, hIgnoreFerry, hNoCarOn,
      hIgnoreEmpty, hOnlyPositive⟩

  let cars :=
    s.statics.objects.filter
      (fun o => s.statics.car_t o)

  have hCarsNodup : cars.Nodup := by
    exact hstatic.1.filter _

  have hCarsTyped :
      ∀ c, c ∈ cars → s.statics.car_t c = true := by
    intro c hc
    exact (List.mem_filter.mp hc).2

  have hTargets :
      ∀ c, s.statics.car_t c = true →
        ∃! l,
          s.statics.location_t l = true ∧
          g.dynamic.at_p c l = some true := by
    intro c hc
    simpa using hMoveAll.1 c hc

  have hAux :=
    solveCars_correct_aux
      cars s g hCarsNodup hCarsTyped hwf hempty
      hTargets hGoalValidAt

  rcases hAux with
    ⟨hValid, _, _, hGoalsReached, _⟩

  have hGoalEmptyNone :
      g.dynamic.empty_ferry_p = none := by
    cases he : g.dynamic.empty_ferry_p with
    | none =>
        rfl
    | some b =>
        have hf : False := by
          simpa [GoalIgnoreEmpty, he] using hIgnoreEmpty
        exact hf.elim

  change
    ValidPlan (solveCars cars s g) s ∧
    SatisfiesGoal
      (runPlan (solveCars cars s g) s) g

  refine ⟨hValid, ?_⟩
  unfold SatisfiesGoal
  refine ⟨?_, ?_, ?_, ?_⟩

  · intro l
    rw [hIgnoreFerry l]
    trivial

  · intro c l
    cases h : g.dynamic.at_p c l with
    | none =>
        trivial
    | some b =>
        cases b with
        | false =>
            exact (hOnlyPositive c l h).elim
        | true =>
            change
              (runPlan
                (solveCars cars s g) s).dynamic.at_p c l = true
            have hCar :
                s.statics.car_t c = true :=
              (hGoalValidAt c l h).1
            have hObj :
                c ∈ s.statics.objects :=
              hstatic.2.1.1 c hCar
            have hMemCars : c ∈ cars := by
              unfold cars
              exact List.mem_filter.mpr ⟨hObj, hCar⟩
            exact hGoalsReached c hMemCars l h

  · rw [hGoalEmptyNone]
    trivial

  · intro c
    rw [hNoCarOn c]
    trivial

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)
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
  heavier_p : Obj → Obj → Bool

structure DynamicStateGen (α : Type) where
  packed_p : Obj → α
  unpacked_p : Obj → α
  nothing_above_p : Obj → α
  box_empty_p : α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidHeavierParam (s : StaticState) : Prop :=
  ∀ var_item1 var_item2, s.heavier_p var_item1 var_item2 = true → var_item1 ∈ s.objects ∧ var_item2 ∈ s.objects

def HeavierIrreflexive (s : StaticState) : Prop :=
  ∀ x, s.heavier_p x x = false

def HeavierAsymmetric (s : StaticState) : Prop :=
  ∀ x y, s.heavier_p x y = true → s.heavier_p y x = false

def HeavierTransitive (s : StaticState) : Prop :=
  ∀ x y z, s.heavier_p x y = true → s.heavier_p y z = true → s.heavier_p x z = true

def HeavierTotal (s : StaticState) : Prop :=
  ∀ x y, x ∈ s.objects → y ∈ s.objects → x ≠ y →
    (s.heavier_p x y = true ∨ s.heavier_p y x = true)

def WellFormedStatic (s : StaticState) : Prop := 
  ObjectsUnique s ∧
  ValidHeavierParam s ∧
  HeavierIrreflexive s ∧
  HeavierAsymmetric s ∧
  HeavierTransitive s ∧
  HeavierTotal s

def ValidPackedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_item, Truthy.isTrue (d.packed_p var_item) → var_item ∈ s.objects

def ValidUnpackedParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_item, Truthy.isTrue (d.unpacked_p var_item) → var_item ∈ s.objects

def ValidNothingAboveParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_item, Truthy.isTrue (d.nothing_above_p var_item) → var_item ∈ s.objects

def PackedUnpackedExclusive {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects → ¬ (Truthy.isTrue (d.packed_p x) ∧ Truthy.isTrue (d.unpacked_p x))

def BoxEmptyImpliesNothingPacked {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  Truthy.isTrue d.box_empty_p → ∀ x, x ∈ s.objects → ¬ Truthy.isTrue (d.packed_p x)

def PackedImpliesNotBoxEmpty {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects → Truthy.isTrue (d.packed_p x) → ¬ Truthy.isTrue d.box_empty_p

def NothingAboveImpliesPacked {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x, x ∈ s.objects → Truthy.isTrue (d.nothing_above_p x) → Truthy.isTrue (d.packed_p x)

def NothingAboveAtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y, Truthy.isTrue (d.nothing_above_p x) → Truthy.isTrue (d.nothing_above_p y) → x = y

def PackedOrUnpacked (s : State) : Prop :=
  ∀ x, x ∈ s.statics.objects → s.dynamic.packed_p x = true ∨ s.dynamic.unpacked_p x = true

def NotBoxEmptyImpliesNothingAboveExists (s : State) : Prop :=
  s.dynamic.box_empty_p = false → ∃ x, x ∈ s.statics.objects ∧ s.dynamic.nothing_above_p x = true

def WellFormed (s : State) : Prop := 
  WellFormedStatic s.statics ∧
  ValidPackedParam s.statics s.dynamic ∧
  ValidUnpackedParam s.statics s.dynamic ∧
  ValidNothingAboveParam s.statics s.dynamic ∧
  PackedUnpackedExclusive s.statics s.dynamic ∧
  BoxEmptyImpliesNothingPacked s.statics s.dynamic ∧
  PackedImpliesNotBoxEmpty s.statics s.dynamic ∧
  NothingAboveImpliesPacked s.statics s.dynamic ∧
  NothingAboveAtMostOne s.statics s.dynamic ∧
  PackedOrUnpacked s ∧
  NotBoxEmptyImpliesNothingAboveExists s

def InitBoxEmpty (s : State) : Prop :=
  s.dynamic.box_empty_p = true

def InitAllItemsUnpacked (s : State) : Prop :=
  ∀ x, x ∈ s.statics.objects → s.dynamic.unpacked_p x = true

def WellFormedInit (s : State) : Prop := 
  WellFormed s ∧
  InitBoxEmpty s ∧
  InitAllItemsUnpacked s

def GoalIgnoreUnpacked (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.unpacked_p x = none

def GoalIgnoreNothingAbove (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.nothing_above_p x = none

def GoalIgnoreBoxEmpty (initial : State) (g : Goal) : Prop :=
  g.dynamic.box_empty_p = none

def GoalPackedOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.packed_p x ≠ some false

def GoalEveryObjectPacked (initial : State) (g : Goal) : Prop :=
  ∀ x, x ∈ initial.statics.objects → g.dynamic.packed_p x = some true

def WellFormedGoal (initial : State) (g : Goal) : Prop := 
  WellFormedStatic initial.statics ∧
  ValidPackedParam initial.statics g.dynamic ∧
  ValidUnpackedParam initial.statics g.dynamic ∧
  ValidNothingAboveParam initial.statics g.dynamic ∧
  PackedUnpackedExclusive initial.statics g.dynamic ∧
  BoxEmptyImpliesNothingPacked initial.statics g.dynamic ∧
  PackedImpliesNotBoxEmpty initial.statics g.dynamic ∧
  NothingAboveImpliesPacked initial.statics g.dynamic ∧
  NothingAboveAtMostOne initial.statics g.dynamic ∧
  GoalIgnoreUnpacked initial g ∧
  GoalIgnoreNothingAbove initial g ∧
  GoalIgnoreBoxEmpty initial g ∧
  GoalPackedOnlyPositive initial g ∧
  GoalEveryObjectPacked initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_item,
    match g.dynamic.packed_p var_item with
    | none => True
    | some b => s.dynamic.packed_p var_item = b) ∧
  (∀ var_item,
    match g.dynamic.unpacked_p var_item with
    | none => True
    | some b => s.dynamic.unpacked_p var_item = b) ∧
  (∀ var_item,
    match g.dynamic.nothing_above_p var_item with
    | none => True
    | some b => s.dynamic.nothing_above_p var_item = b) ∧
  (match g.dynamic.box_empty_p with
  | none => True
  | some b => s.dynamic.box_empty_p = b)

def pack_firstPre (var_item : Obj) (s : State) : Prop :=
  var_item ∈ s.statics.objects ∧
  s.dynamic.box_empty_p = true

def stackPre (var_bottom : Obj) (var_top : Obj) (s : State) : Prop :=
  var_bottom ∈ s.statics.objects ∧
  var_top ∈ s.statics.objects ∧
  s.dynamic.packed_p var_bottom = true ∧
  s.dynamic.nothing_above_p var_bottom = true ∧
  s.statics.heavier_p var_bottom var_top = true ∧
  s.dynamic.unpacked_p var_top = true

def pack_first (var_item : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    packed_p :=
      fun var_item' =>
        if var_item' = var_item then
          true
        else
          s.dynamic.packed_p var_item',
    unpacked_p :=
      fun var_item' =>
        if var_item' = var_item then
          false
        else
          s.dynamic.unpacked_p var_item',
    nothing_above_p :=
      fun var_item' =>
        if var_item' = var_item then
          true
        else
          s.dynamic.nothing_above_p var_item',
    box_empty_p := false
  }
}

def stack (var_bottom : Obj) (var_top : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    packed_p :=
      fun var_top' =>
        if var_top' = var_top then
          true
        else
          s.dynamic.packed_p var_top',
    unpacked_p :=
      fun var_top' =>
        if var_top' = var_top then
          false
        else
          s.dynamic.unpacked_p var_top',
    nothing_above_p :=
      fun var_top' =>
        if var_top' = var_top then
          true
        else if var_top' = var_bottom then
          false
        else
          s.dynamic.nothing_above_p var_top'
  }
}

inductive PlanAction where
  | pack_first (var_item : Obj)
  | stack      (var_bottom : Obj) (var_top : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .pack_first var_item          , s => pack_firstPre var_item s
  | .stack      var_bottom var_top, s => stackPre var_bottom var_top s

def actionApply : PlanAction → State → State
  | .pack_first var_item          , s => pack_first var_item s
  | .stack      var_bottom var_top, s => stack var_bottom var_top s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def insertByHeavier
    (heavier : Obj → Obj → Bool) (item : Obj) : List Obj → List Obj
  | [] => [item]
  | current :: rest =>
      if heavier item current then
        item :: current :: rest
      else
        current :: insertByHeavier heavier item rest

def sortByHeavier
    (heavier : Obj → Obj → Bool) : List Obj → List Obj
  | [] => []
  | item :: rest =>
      insertByHeavier heavier item (sortByHeavier heavier rest)

def buildStackActions : Obj → List Obj → List PlanAction
  | _, [] => []
  | bottom, top :: rest =>
      PlanAction.stack bottom top :: buildStackActions top rest

def solve (s : State) (g : Goal) : List PlanAction :=
  let sortedItems :=
    sortByHeavier s.statics.heavier_p s.statics.objects
  match sortedItems with
  | [] => []
  | first :: rest =>
      PlanAction.pack_first first :: buildStackActions first rest

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

lemma pack_first_statics (var_item : Obj) (s : State) :
    (pack_first var_item s).statics = s.statics := rfl

lemma stack_statics (var_bottom var_top : Obj) (s : State) :
    (stack var_bottom var_top s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | pack_first var_item      => exact pack_first_statics var_item s
      | stack var_bottom var_top => exact stack_statics var_bottom var_top s

-- pack_first only touches packed_p, nothing_above_p, unpacked_p
lemma pack_first_packed_p_ne (var_item : Obj) (s : State) {var_item' : Obj} (h1 : var_item' ≠ var_item) :
    (pack_first var_item s).dynamic.packed_p var_item' = s.dynamic.packed_p var_item' := by
  unfold pack_first
  simp [h1]

lemma pack_first_unpacked_p_ne (var_item : Obj) (s : State) {var_item' : Obj} (h1 : var_item' ≠ var_item) :
    (pack_first var_item s).dynamic.unpacked_p var_item' = s.dynamic.unpacked_p var_item' := by
  unfold pack_first
  simp [h1]

lemma pack_first_nothing_above_p_ne (var_item : Obj) (s : State) {var_item' : Obj} (h1 : var_item' ≠ var_item) :
    (pack_first var_item s).dynamic.nothing_above_p var_item' = s.dynamic.nothing_above_p var_item' := by
  unfold pack_first
  simp [h1]

-- stack only touches packed_p, nothing_above_p, unpacked_p
lemma stack_packed_p_ne (var_bottom var_top : Obj) (s : State) {var_top' : Obj} (h1 : var_top' ≠ var_top) :
    (stack var_bottom var_top s).dynamic.packed_p var_top' = s.dynamic.packed_p var_top' := by
  unfold stack
  simp [h1]

lemma stack_unpacked_p_ne (var_bottom var_top : Obj) (s : State) {var_top' : Obj} (h1 : var_top' ≠ var_top) :
    (stack var_bottom var_top s).dynamic.unpacked_p var_top' = s.dynamic.unpacked_p var_top' := by
  unfold stack
  simp [h1]

lemma stack_nothing_above_p_ne (var_bottom var_top : Obj) (s : State) {var_top' : Obj} (h1 : var_top' ≠ var_top) (h2 : var_top' ≠ var_bottom) :
    (stack var_bottom var_top s).dynamic.nothing_above_p var_top' = s.dynamic.nothing_above_p var_top' := by
  unfold stack
  simp [h1, h2]

-- stack never touches box_empty_p
lemma stack_box_empty_p (var_bottom var_top : Obj) (s : State) :
    (stack var_bottom var_top s).dynamic.box_empty_p = s.dynamic.box_empty_p := rfl

lemma pack_first_packed_p_eq1 (var_item : Obj) (s : State) :
    (pack_first var_item s).dynamic.packed_p var_item = true := by
  unfold pack_first
  simp

lemma pack_first_unpacked_p_eq1 (var_item : Obj) (s : State) :
    (pack_first var_item s).dynamic.unpacked_p var_item = false := by
  unfold pack_first
  simp

lemma pack_first_nothing_above_p_eq1 (var_item : Obj) (s : State) :
    (pack_first var_item s).dynamic.nothing_above_p var_item = true := by
  unfold pack_first
  simp

lemma pack_first_box_empty_p (var_item : Obj) (s : State) :
    (pack_first var_item s).dynamic.box_empty_p = false := by
  unfold pack_first
  simp

lemma stack_packed_p_eq1 (var_bottom var_top : Obj) (s : State) :
    (stack var_bottom var_top s).dynamic.packed_p var_top = true := by
  unfold stack
  simp

lemma stack_unpacked_p_eq1 (var_bottom var_top : Obj) (s : State) :
    (stack var_bottom var_top s).dynamic.unpacked_p var_top = false := by
  unfold stack
  simp

lemma stack_nothing_above_p_eq1 (var_bottom var_top : Obj) (s : State) :
    (stack var_bottom var_top s).dynamic.nothing_above_p var_top = true := by
  unfold stack
  simp

lemma stack_nothing_above_p_eq2 (var_bottom var_top : Obj) (s : State) (h1 : var_bottom ≠ var_top) :
    (stack var_bottom var_top s).dynamic.nothing_above_p var_bottom = false := by
  unfold stack
  simp [h1]

lemma pack_first_preserves_wf
    (var_item)
    (s : State)
    (hwf : WellFormed s)
    (hpre : pack_firstPre var_item s) :
    WellFormed (pack_first var_item s) := by
  rcases hwf with
    ⟨hstatic, hPackedValid, hUnpackedValid, hNothingValid,
     hExclusive, hBoxEmpty, hPackedNotBoxEmpty, hNothingPacked,
     hAtMostOne, hPackedOrUnpacked, hNothingExists⟩
  rcases hpre with ⟨hitem, hbox⟩

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro x hx
    rw [pack_first_statics var_item s]
    by_cases h : x = var_item
    · subst x
      exact hitem
    · apply hPackedValid x
      change (pack_first var_item s).dynamic.packed_p x = true at hx
      rw [pack_first_packed_p_ne var_item s h] at hx
      exact hx

  · intro x hx
    rw [pack_first_statics var_item s]
    by_cases h : x = var_item
    · subst x
      change (pack_first var_item s).dynamic.unpacked_p var_item = true at hx
      rw [pack_first_unpacked_p_eq1] at hx
      cases hx
    · apply hUnpackedValid x
      change (pack_first var_item s).dynamic.unpacked_p x = true at hx
      rw [pack_first_unpacked_p_ne var_item s h] at hx
      exact hx

  · intro x hx
    rw [pack_first_statics var_item s]
    by_cases h : x = var_item
    · subst x
      exact hitem
    · apply hNothingValid x
      change (pack_first var_item s).dynamic.nothing_above_p x = true at hx
      rw [pack_first_nothing_above_p_ne var_item s h] at hx
      exact hx

  · intro x hxmem hboth
    rw [pack_first_statics var_item s] at hxmem
    rcases hboth with ⟨hp, hu⟩
    by_cases h : x = var_item
    · subst x
      change (pack_first var_item s).dynamic.unpacked_p var_item = true at hu
      rw [pack_first_unpacked_p_eq1] at hu
      cases hu
    · apply hExclusive x hxmem
      constructor
      · change (pack_first var_item s).dynamic.packed_p x = true at hp
        rw [pack_first_packed_p_ne var_item s h] at hp
        exact hp
      · change (pack_first var_item s).dynamic.unpacked_p x = true at hu
        rw [pack_first_unpacked_p_ne var_item s h] at hu
        exact hu

  · intro hempty
    change (pack_first var_item s).dynamic.box_empty_p = true at hempty
    rw [pack_first_box_empty_p] at hempty
    cases hempty

  · intro x hxmem hpacked hempty
    change (pack_first var_item s).dynamic.box_empty_p = true at hempty
    rw [pack_first_box_empty_p] at hempty
    cases hempty

  · intro x hxmem hnothing
    rw [pack_first_statics var_item s] at hxmem
    by_cases h : x = var_item
    · subst x
      change (pack_first var_item s).dynamic.packed_p var_item = true
      exact pack_first_packed_p_eq1 var_item s
    ·
      change (pack_first var_item s).dynamic.nothing_above_p x = true at hnothing
      rw [pack_first_nothing_above_p_ne var_item s h] at hnothing
      have hp : s.dynamic.packed_p x = true :=
        hNothingPacked x hxmem hnothing
      change (pack_first var_item s).dynamic.packed_p x = true
      rw [pack_first_packed_p_ne var_item s h]
      exact hp

  ·
    have only_item :
        ∀ x,
          (pack_first var_item s).dynamic.nothing_above_p x = true →
          x = var_item := by
      intro x hx
      by_contra hne
      have hold : s.dynamic.nothing_above_p x = true := by
        rw [pack_first_nothing_above_p_ne var_item s hne] at hx
        exact hx
      have hxmem : x ∈ s.statics.objects :=
        hNothingValid x hold
      have hp : s.dynamic.packed_p x = true :=
        hNothingPacked x hxmem hold
      exact (hBoxEmpty hbox x hxmem) hp

    intro x y hx hy
    calc
      x = var_item := only_item x hx
      _ = y := (only_item y hy).symm

  · intro x hxmem
    rw [pack_first_statics var_item s] at hxmem
    by_cases h : x = var_item
    · subst x
      left
      exact pack_first_packed_p_eq1 var_item s
    · rcases hPackedOrUnpacked x hxmem with hp | hu
      · left
        change (pack_first var_item s).dynamic.packed_p x = true
        rw [pack_first_packed_p_ne var_item s h]
        exact hp
      · right
        change (pack_first var_item s).dynamic.unpacked_p x = true
        rw [pack_first_unpacked_p_ne var_item s h]
        exact hu

  · intro _
    refine ⟨var_item, ?_, pack_first_nothing_above_p_eq1 var_item s⟩
    rw [pack_first_statics var_item s]
    exact hitem


lemma stack_preserves_wf
    (var_bottom var_top)
    (s : State)
    (hwf : WellFormed s)
    (hpre : stackPre var_bottom var_top s) :
    WellFormed (stack var_bottom var_top s) := by
  rcases hwf with
    ⟨hstatic, hPackedValid, hUnpackedValid, hNothingValid,
     hExclusive, hBoxEmpty, hPackedNotBoxEmpty, hNothingPacked,
     hAtMostOne, hPackedOrUnpacked, hNothingExists⟩
  rcases hpre with
    ⟨hbottommem, htopmem, hbottompacked, hbottomnothing,
     hheavy, htopunpacked⟩

  have hstatic_copy := hstatic
  rcases hstatic_copy with ⟨_, _, hirr, _, _, _⟩

  have hne : var_bottom ≠ var_top := by
    intro heq
    subst var_top
    rw [hirr var_bottom] at hheavy
    cases hheavy

  refine ⟨hstatic, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · intro x hx
    by_cases ht : x = var_top
    · subst x
      exact htopmem
    · apply hPackedValid x
      change (stack var_bottom var_top s).dynamic.packed_p x = true at hx
      rw [stack_packed_p_ne var_bottom var_top s ht] at hx
      exact hx

  · intro x hx
    by_cases ht : x = var_top
    · subst x
      change
        (stack var_bottom var_top s).dynamic.unpacked_p var_top = true
        at hx
      rw [stack_unpacked_p_eq1] at hx
      cases hx
    · apply hUnpackedValid x
      change (stack var_bottom var_top s).dynamic.unpacked_p x = true at hx
      rw [stack_unpacked_p_ne var_bottom var_top s ht] at hx
      exact hx

  · intro x hx
    by_cases ht : x = var_top
    · subst x
      exact htopmem
    · by_cases hb : x = var_bottom
      · subst x
        change
          (stack var_bottom var_top s).dynamic.nothing_above_p var_bottom = true
          at hx
        rw [stack_nothing_above_p_eq2 var_bottom var_top s hne] at hx
        cases hx
      · apply hNothingValid x
        change
          (stack var_bottom var_top s).dynamic.nothing_above_p x = true
          at hx
        rw [stack_nothing_above_p_ne var_bottom var_top s ht hb] at hx
        exact hx

  · intro x hxmem hboth
    rcases hboth with ⟨hp, hu⟩
    by_cases ht : x = var_top
    · subst x
      change
        (stack var_bottom var_top s).dynamic.unpacked_p var_top = true
        at hu
      rw [stack_unpacked_p_eq1] at hu
      cases hu
    · apply hExclusive x hxmem
      constructor
      · change (stack var_bottom var_top s).dynamic.packed_p x = true at hp
        rw [stack_packed_p_ne var_bottom var_top s ht] at hp
        exact hp
      · change (stack var_bottom var_top s).dynamic.unpacked_p x = true at hu
        rw [stack_unpacked_p_ne var_bottom var_top s ht] at hu
        exact hu

  · intro hempty x hxmem hpacked
    change (stack var_bottom var_top s).dynamic.box_empty_p = true at hempty
    rw [stack_box_empty_p var_bottom var_top s] at hempty
    exact
      (hPackedNotBoxEmpty var_bottom hbottommem hbottompacked) hempty

  · intro x hxmem hpacked hempty
    change (stack var_bottom var_top s).dynamic.box_empty_p = true at hempty
    rw [stack_box_empty_p var_bottom var_top s] at hempty
    exact
      (hPackedNotBoxEmpty var_bottom hbottommem hbottompacked) hempty

  · intro x hxmem hnothing
    by_cases ht : x = var_top
    · subst x
      change (stack var_bottom var_top s).dynamic.packed_p var_top = true
      exact stack_packed_p_eq1 var_bottom var_top s
    · by_cases hb : x = var_bottom
      · subst x
        change
          (stack var_bottom var_top s).dynamic.nothing_above_p var_bottom = true
          at hnothing
        rw [stack_nothing_above_p_eq2 var_bottom var_top s hne] at hnothing
        cases hnothing
      · have hold : s.dynamic.nothing_above_p x = true := by
          change
            (stack var_bottom var_top s).dynamic.nothing_above_p x = true
            at hnothing
          rw [stack_nothing_above_p_ne var_bottom var_top s ht hb] at hnothing
          exact hnothing
        have hp : s.dynamic.packed_p x = true :=
          hNothingPacked x hxmem hold
        change (stack var_bottom var_top s).dynamic.packed_p x = true
        rw [stack_packed_p_ne var_bottom var_top s ht]
        exact hp

  ·
    have only_top :
        ∀ x,
          (stack var_bottom var_top s).dynamic.nothing_above_p x = true →
          x = var_top := by
      intro x hx
      by_cases ht : x = var_top
      · exact ht
      · by_cases hb : x = var_bottom
        · subst x
          rw [stack_nothing_above_p_eq2 var_bottom var_top s hne] at hx
          cases hx
        · have hold : s.dynamic.nothing_above_p x = true := by
            rw [stack_nothing_above_p_ne var_bottom var_top s ht hb] at hx
            exact hx
          have heq : x = var_bottom :=
            hAtMostOne x var_bottom hold hbottomnothing
          exact (hb heq).elim

    intro x y hx hy
    calc
      x = var_top := only_top x hx
      _ = y := (only_top y hy).symm

  · intro x hxmem
    by_cases ht : x = var_top
    · subst x
      left
      exact stack_packed_p_eq1 var_bottom var_top s
    · rcases hPackedOrUnpacked x hxmem with hp | hu
      · left
        change (stack var_bottom var_top s).dynamic.packed_p x = true
        rw [stack_packed_p_ne var_bottom var_top s ht]
        exact hp
      · right
        change (stack var_bottom var_top s).dynamic.unpacked_p x = true
        rw [stack_unpacked_p_ne var_bottom var_top s ht]
        exact hu

  · intro _
    exact
      ⟨var_top, htopmem,
       stack_nothing_above_p_eq1 var_bottom var_top s⟩

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | pack_first var_item =>
      exact pack_first_preserves_wf var_item s hwf hpre
  | stack var_bottom var_top =>
      exact stack_preserves_wf var_bottom var_top s hwf hpre

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

def HeavierSorted (heavier : Obj → Obj → Bool) : List Obj → Prop
  | [] => True
  | x :: xs =>
      (∀ y, y ∈ xs → heavier x y = true) ∧
      HeavierSorted heavier xs

lemma mem_insertByHeavier
    (heavier : Obj → Obj → Bool)
    (item x : Obj)
    (xs : List Obj) :
    x ∈ insertByHeavier heavier item xs ↔ x = item ∨ x ∈ xs := by
  induction xs with
  | nil =>
      simp [insertByHeavier]
  | cons current rest ih =>
      simp only [insertByHeavier]
      split <;>
        simp [ih, or_assoc, or_left_comm, or_comm]

lemma mem_sortByHeavier
    (heavier : Obj → Obj → Bool)
    (x : Obj)
    (xs : List Obj) :
    x ∈ sortByHeavier heavier xs ↔ x ∈ xs := by
  induction xs with
  | nil =>
      simp [sortByHeavier]
  | cons item rest ih =>
      simp [sortByHeavier, mem_insertByHeavier, ih,
        or_assoc, or_left_comm, or_comm]

lemma insertByHeavier_nodup
    (heavier : Obj → Obj → Bool)
    (item : Obj)
    (xs : List Obj)
    (hnodup : xs.Nodup)
    (hnotmem : item ∉ xs) :
    (insertByHeavier heavier item xs).Nodup := by
  induction xs with
  | nil =>
      simp [insertByHeavier]
  | cons current rest ih =>
      have hcurrentNotRest : current ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hitemNeCurrent : item ≠ current := by
        intro heq
        apply hnotmem
        simp [heq]
      have hitemNotRest : item ∉ rest := by
        intro hm
        apply hnotmem
        simp [hm]
      simp only [insertByHeavier]
      split
      · exact List.nodup_cons.mpr ⟨hnotmem, hnodup⟩
      · apply List.nodup_cons.mpr
        constructor
        · intro hm
          rcases
              (mem_insertByHeavier heavier item current rest).mp hm with
            heq | hmrest
          · exact hitemNeCurrent heq.symm
          · exact hcurrentNotRest hmrest
        · exact ih hrestNodup hitemNotRest

lemma sortByHeavier_nodup
    (heavier : Obj → Obj → Bool)
    (xs : List Obj)
    (hnodup : xs.Nodup) :
    (sortByHeavier heavier xs).Nodup := by
  induction xs with
  | nil =>
      simp [sortByHeavier]
  | cons item rest ih =>
      have hitemNotRest : item ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      apply insertByHeavier_nodup
      · exact ih hrestNodup
      · intro hm
        apply hitemNotRest
        exact
          (mem_sortByHeavier heavier item rest).mp hm

lemma insertByHeavier_sorted
    (st : StaticState)
    (htrans : HeavierTransitive st)
    (htotal : HeavierTotal st)
    (item : Obj)
    (xs : List Obj)
    (hitem : item ∈ st.objects)
    (hxs : ∀ x, x ∈ xs → x ∈ st.objects)
    (hnotmem : item ∉ xs)
    (hsorted : HeavierSorted st.heavier_p xs) :
    HeavierSorted st.heavier_p
      (insertByHeavier st.heavier_p item xs) := by
  induction xs generalizing item with
  | nil =>
      simp [insertByHeavier, HeavierSorted]
  | cons current rest ih =>
      have hcurrentMem : current ∈ st.objects :=
        hxs current (by simp)
      have hrestMem : ∀ x, x ∈ rest → x ∈ st.objects := by
        intro x hx
        exact hxs x (by simp [hx])
      have hitemNeCurrent : item ≠ current := by
        intro heq
        apply hnotmem
        simp [heq]
      have hitemNotRest : item ∉ rest := by
        intro hm
        apply hnotmem
        simp [hm]

      change
        (∀ y, y ∈ rest → st.heavier_p current y = true) ∧
          HeavierSorted st.heavier_p rest
        at hsorted
      rcases hsorted with ⟨hcurrentHeavy, hrestSorted⟩

      simp only [insertByHeavier]
      split
      next hitemCurrent =>
        constructor
        · intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hitemCurrent
          · exact
              htrans _ _ _ hitemCurrent
                (hcurrentHeavy y hy)
        · exact ⟨hcurrentHeavy, hrestSorted⟩
      next hnotItemCurrent =>
        constructor
        · intro y hy
          rcases
              (mem_insertByHeavier st.heavier_p item y rest).mp hy with
            rfl | hy
          · rcases
                htotal current y hcurrentMem hitem
                  hitemNeCurrent.symm with
              hcurrentItem | hitemCurrent
            · exact hcurrentItem
            · exact (hnotItemCurrent hitemCurrent).elim
          · exact hcurrentHeavy y hy
        · exact
            ih (item := item)
              (hitem := hitem)
              (hxs := hrestMem)
              (hnotmem := hitemNotRest)
              (hsorted := hrestSorted)

lemma sortByHeavier_sorted
    (st : StaticState)
    (hstatic : WellFormedStatic st)
    (xs : List Obj)
    (hnodup : xs.Nodup)
    (hxs : ∀ x, x ∈ xs → x ∈ st.objects) :
    HeavierSorted st.heavier_p
      (sortByHeavier st.heavier_p xs) := by
  rcases hstatic with
    ⟨_, _, _, _, htrans, htotal⟩
  induction xs with
  | nil =>
      simp [sortByHeavier, HeavierSorted]
  | cons item rest ih =>
      have hitemNotRest : item ∉ rest :=
        (List.nodup_cons.mp hnodup).1
      have hrestNodup : rest.Nodup :=
        (List.nodup_cons.mp hnodup).2
      have hitemMem : item ∈ st.objects :=
        hxs item (by simp)
      have hrestMem : ∀ x, x ∈ rest → x ∈ st.objects := by
        intro x hx
        exact hxs x (by simp [hx])
      apply insertByHeavier_sorted
          st htrans htotal item
          (sortByHeavier st.heavier_p rest)
      · exact hitemMem
      · intro x hx
        exact hrestMem x
          ((mem_sortByHeavier st.heavier_p x rest).mp hx)
      · intro hx
        exact hitemNotRest
          ((mem_sortByHeavier st.heavier_p item rest).mp hx)
      · exact ih hrestNodup hrestMem

lemma run_buildStackActions_packed_ne
    (bottom : Obj)
    (items : List Obj)
    (s : State)
    {x : Obj}
    (hx : x ∉ items) :
    (runPlan (buildStackActions bottom items) s).dynamic.packed_p x =
      s.dynamic.packed_p x := by
  induction items generalizing bottom s with
  | nil =>
      simp [buildStackActions, runPlan]
  | cons top rest ih =>
      have hxNeTop : x ≠ top := by
        intro heq
        apply hx
        simp [heq]
      have hxNotRest : x ∉ rest := by
        intro hm
        apply hx
        simp [hm]
      change
        (runPlan
          (buildStackActions top rest)
          (stack bottom top s)).dynamic.packed_p x =
          s.dynamic.packed_p x
      calc
        (runPlan
          (buildStackActions top rest)
          (stack bottom top s)).dynamic.packed_p x =
            (stack bottom top s).dynamic.packed_p x :=
              ih (bottom := top) (s := stack bottom top s) hxNotRest
        _ = s.dynamic.packed_p x :=
              stack_packed_p_ne bottom top s hxNeTop

lemma buildStackActions_correct
    (s : State)
    (bottom : Obj)
    (items : List Obj)
    (hnodup : (bottom :: items).Nodup)
    (hmem :
      ∀ x, x ∈ bottom :: items → x ∈ s.statics.objects)
    (hsorted :
      HeavierSorted s.statics.heavier_p (bottom :: items))
    (hpacked : s.dynamic.packed_p bottom = true)
    (hnothing : s.dynamic.nothing_above_p bottom = true)
    (hunpacked :
      ∀ x, x ∈ items → s.dynamic.unpacked_p x = true) :
    ValidPlan (buildStackActions bottom items) s ∧
    (∀ x, x ∈ bottom :: items →
      (runPlan (buildStackActions bottom items) s).dynamic.packed_p x =
        true) := by
  induction items generalizing bottom s with
  | nil =>
      constructor
      · simp [buildStackActions, ValidPlan]
      · intro x hx
        simp only [List.mem_singleton] at hx
        subst x
        simpa [buildStackActions, runPlan] using hpacked
  | cons top rest ih =>
      have hbottomNotTail : bottom ∉ top :: rest :=
        (List.nodup_cons.mp hnodup).1
      have htailNodup : (top :: rest).Nodup :=
        (List.nodup_cons.mp hnodup).2
      have htopNotRest : top ∉ rest :=
        (List.nodup_cons.mp htailNodup).1

      change
        (∀ y, y ∈ top :: rest →
          s.statics.heavier_p bottom y = true) ∧
        HeavierSorted s.statics.heavier_p (top :: rest)
        at hsorted
      rcases hsorted with ⟨hbottomHeavy, htailSorted⟩

      have hbottomMem : bottom ∈ s.statics.objects :=
        hmem bottom (by simp)
      have htopMem : top ∈ s.statics.objects :=
        hmem top (by simp)

      have hpre : stackPre bottom top s := by
        exact
          ⟨hbottomMem, htopMem, hpacked, hnothing,
           hbottomHeavy top (by simp),
           hunpacked top (by simp)⟩

      have htailMem :
          ∀ x, x ∈ top :: rest →
            x ∈ (stack bottom top s).statics.objects := by
        intro x hx
        change x ∈ s.statics.objects
        exact hmem x (List.mem_cons_of_mem bottom hx)

      have hrestUnpacked :
          ∀ x, x ∈ rest →
            (stack bottom top s).dynamic.unpacked_p x = true := by
        intro x hx
        have hxNeTop : x ≠ top := by
          intro heq
          subst x
          exact htopNotRest hx
        rw [stack_unpacked_p_ne bottom top s hxNeTop]
        exact hunpacked x (by simp [hx])

      have hrec :
          ValidPlan
              (buildStackActions top rest)
              (stack bottom top s) ∧
          (∀ x, x ∈ top :: rest →
            (runPlan
              (buildStackActions top rest)
              (stack bottom top s)).dynamic.packed_p x = true) := by
        apply ih
            (s := stack bottom top s)
            (bottom := top)
        · exact htailNodup
        · exact htailMem
        · exact htailSorted
        · exact stack_packed_p_eq1 bottom top s
        · exact stack_nothing_above_p_eq1 bottom top s
        · exact hrestUnpacked

      constructor
      · change
          stackPre bottom top s ∧
          ValidPlan
            (buildStackActions top rest)
            (stack bottom top s)
        exact ⟨hpre, hrec.1⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with hxbottom | hxtail
        · subst x
          have hbottomNeTop : bottom ≠ top := by
            intro heq
            apply hbottomNotTail
            simp [heq]
          have hbottomNotRest : bottom ∉ rest := by
            intro hm
            apply hbottomNotTail
            simp [hm]
          change
            (runPlan
              (buildStackActions top rest)
              (stack bottom top s)).dynamic.packed_p bottom = true
          calc
            (runPlan
              (buildStackActions top rest)
              (stack bottom top s)).dynamic.packed_p bottom =
                (stack bottom top s).dynamic.packed_p bottom :=
                  run_buildStackActions_packed_ne
                    top rest (stack bottom top s) hbottomNotRest
            _ = s.dynamic.packed_p bottom :=
                  stack_packed_p_ne bottom top s hbottomNeTop
            _ = true := hpacked
        · change
            (runPlan
              (buildStackActions top rest)
              (stack bottom top s)).dynamic.packed_p x = true
          apply hrec.2 x
          simpa only [List.mem_cons] using hxtail

lemma satisfiesGoal_of_all_objects_packed
    (initial final : State)
    (g : Goal)
    (hallPacked :
      ∀ x, x ∈ initial.statics.objects →
        final.dynamic.packed_p x = true)
    (hgoal : WellFormedGoal initial g) :
    SatisfiesGoal final g := by
  rcases hgoal with
    ⟨_, hPackedValid, _, _, _, _, _, _, _,
     hIgnoreUnpacked, hIgnoreNothingAbove, hIgnoreBoxEmpty,
     hPackedPositive, _⟩

  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    cases h : g.dynamic.packed_p x with
    | none =>
        exact True.intro
    | some b =>
        cases b with
        | false =>
            exact (hPackedPositive x h).elim
        | true =>
            have hxmem : x ∈ initial.statics.objects := by
              apply hPackedValid x
              change g.dynamic.packed_p x = some true
              exact h
            exact hallPacked x hxmem
  · intro x
    rw [hIgnoreUnpacked x]
    trivial
  · intro x
    rw [hIgnoreNothingAbove x]
    trivial
  · rw [hIgnoreBoxEmpty]
    trivial

-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  rcases hinit with ⟨_, hboxEmpty, hinitUnpacked⟩

  have hobjectsNodup : s.statics.objects.Nodup :=
    hstatic.1

  cases hitems :
      sortByHeavier s.statics.heavier_p s.statics.objects with
  | nil =>
      have hnoObjects : ∀ x, x ∉ s.statics.objects := by
        intro x hx
        have hm :
            x ∈ sortByHeavier
              s.statics.heavier_p s.statics.objects :=
          (mem_sortByHeavier
            s.statics.heavier_p x s.statics.objects).2 hx
        rw [hitems] at hm
        simpa using hm

      have hallPacked :
          ∀ x, x ∈ s.statics.objects →
            s.dynamic.packed_p x = true := by
        intro x hx
        exact (hnoObjects x hx).elim

      have hsat : SatisfiesGoal s g :=
        satisfiesGoal_of_all_objects_packed
          s s g hallPacked hgoal

      constructor
      · simp [solve, hitems, ValidPlan]
      · simpa [solve, hitems, runPlan] using hsat

  | cons first rest =>
      have hsortedNodup : (first :: rest).Nodup := by
        rw [← hitems]
        exact sortByHeavier_nodup
          s.statics.heavier_p
          s.statics.objects
          hobjectsNodup

      have hsortedMem :
          ∀ x, x ∈ first :: rest →
            x ∈ s.statics.objects := by
        intro x hx
        apply
          (mem_sortByHeavier
            s.statics.heavier_p x s.statics.objects).mp
        rw [hitems]
        exact hx

      have hsortedOrder :
          HeavierSorted
            s.statics.heavier_p
            (first :: rest) := by
        rw [← hitems]
        exact
          sortByHeavier_sorted
            s.statics hstatic s.statics.objects
            hobjectsNodup
            (by
              intro x hx
              exact hx)

      have hfirstMem : first ∈ s.statics.objects :=
        hsortedMem first (by simp)

      have hfirstPre : pack_firstPre first s :=
        ⟨hfirstMem, hboxEmpty⟩

      have hfirstNotRest : first ∉ rest :=
        (List.nodup_cons.mp hsortedNodup).1

      have hrestUnpacked :
          ∀ x, x ∈ rest →
            (pack_first first s).dynamic.unpacked_p x = true := by
        intro x hx
        have hxNeFirst : x ≠ first := by
          intro heq
          subst x
          exact hfirstNotRest hx
        rw [pack_first_unpacked_p_ne first s hxNeFirst]
        exact hinitUnpacked x
          (hsortedMem x (by simp [hx]))

      have hstackCorrect :
          ValidPlan
              (buildStackActions first rest)
              (pack_first first s) ∧
          (∀ x, x ∈ first :: rest →
            (runPlan
              (buildStackActions first rest)
              (pack_first first s)).dynamic.packed_p x = true) := by
        apply buildStackActions_correct
            (s := pack_first first s)
            (bottom := first)
            (items := rest)
        · exact hsortedNodup
        · intro x hx
          change x ∈ s.statics.objects
          exact hsortedMem x hx
        · exact hsortedOrder
        · exact pack_first_packed_p_eq1 first s
        · exact pack_first_nothing_above_p_eq1 first s
        · exact hrestUnpacked

      have hvalid : ValidPlan (solve s g) s := by
        simpa only
            [solve, hitems, ValidPlan, actionPre, actionApply]
          using And.intro hfirstPre hstackCorrect.1

      have hallPacked :
          ∀ x, x ∈ s.statics.objects →
            (runPlan (solve s g) s).dynamic.packed_p x = true := by
        intro x hx
        have hxsorted : x ∈ first :: rest := by
          have hm :
              x ∈ sortByHeavier
                s.statics.heavier_p s.statics.objects :=
            (mem_sortByHeavier
              s.statics.heavier_p x s.statics.objects).2 hx
          rw [hitems] at hm
          exact hm
        have hp := hstackCorrect.2 x hxsorted
        simpa only
            [solve, hitems, runPlan, actionApply]
          using hp

      exact
        ⟨hvalid,
         satisfiesGoal_of_all_objects_packed
           s (runPlan (solve s g) s) g hallPacked hgoal⟩

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)
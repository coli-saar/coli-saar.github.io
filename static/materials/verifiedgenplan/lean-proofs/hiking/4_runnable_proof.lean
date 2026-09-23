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
  iswater_p : Obj → Bool
  ishill_p : Obj → Bool
  adjacent_p : Obj → Obj → Bool
  ontrail_p : Obj → Obj → Bool
  loc_t : Obj → Bool

structure DynamicStateGen (α : Type) where
  at_p : Obj → α

abbrev DynamicState := DynamicStateGen Bool
abbrev GoalDynamic := DynamicStateGen (Option Bool)

structure Goal where
  dynamic : GoalDynamic

structure State where
  statics : StaticState
  dynamic : DynamicState

def ObjectsUnique (s : StaticState) : Prop :=
    s.objects.Nodup

def ValidIswaterParam (s : StaticState) : Prop :=
  ∀ var_loc, s.iswater_p var_loc = true → s.loc_t var_loc = true

def ValidIshillParam (s : StaticState) : Prop :=
  ∀ var_loc, s.ishill_p var_loc = true → s.loc_t var_loc = true

def ValidAdjacentParam (s : StaticState) : Prop :=
  ∀ var_loc1 var_loc2, s.adjacent_p var_loc1 var_loc2 = true → s.loc_t var_loc1 = true ∧ s.loc_t var_loc2 = true

def ValidOntrailParam (s : StaticState) : Prop :=
  ∀ var_from var_to, s.ontrail_p var_from var_to = true → s.loc_t var_from = true ∧ s.loc_t var_to = true

def ValidTypeHierarchy (s : StaticState) : Prop :=
  (∀ x, s.loc_t x = true → x ∈ s.objects)

def TypeCoverage (s : StaticState) : Prop :=
  ∀ x, x ∈ s.objects → s.loc_t x = true

def AdjacentSymmetric (s : StaticState) : Prop :=
  ∀ x y, s.adjacent_p x y = true → s.adjacent_p y x = true

def AdjacentConnected (s : StaticState) : Prop :=
  ∀ x y, s.loc_t x = true → s.loc_t y = true →
    Relation.ReflTransGen (fun a b => s.adjacent_p a b = true) x y

def MinLoc (s : StaticState) : Prop :=
  ∃ x y, s.loc_t x = true ∧ s.loc_t y = true ∧ x ≠ y

def OntrailImpliesAdjacent (s : StaticState) : Prop :=
  ∀ a b, s.ontrail_p a b = true → s.adjacent_p a b = true

def OntrailFromNotWater (s : StaticState) : Prop :=
  ∀ a b, s.ontrail_p a b = true → s.iswater_p a = false

def OntrailFunctional (s : StaticState) : Prop :=
  ∀ a b1 b2, s.ontrail_p a b1 = true → s.ontrail_p a b2 = true → b1 = b2

def OntrailInjective (s : StaticState) : Prop :=
  ∀ a1 a2 b, s.ontrail_p a1 b = true → s.ontrail_p a2 b = true → a1 = a2

def OntrailAcyclic (s : StaticState) : Prop :=
  ∀ x, ¬ Relation.TransGen (fun a b => s.ontrail_p a b = true) x x

def WellFormedStatic (s : StaticState) : Prop := 
  ObjectsUnique s ∧
  ValidIswaterParam s ∧
  ValidIshillParam s ∧
  ValidAdjacentParam s ∧
  ValidOntrailParam s ∧
  ValidTypeHierarchy s ∧
  TypeCoverage s ∧
  AdjacentSymmetric s ∧
  AdjacentConnected s ∧
  MinLoc s ∧
  OntrailImpliesAdjacent s ∧
  OntrailFromNotWater s ∧
  OntrailFunctional s ∧
  OntrailInjective s ∧
  OntrailAcyclic s

def ValidAtParam {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ var_loc, Truthy.isTrue (d.at_p var_loc) → s.loc_t var_loc = true

def AtMostOne {α : Type} [Truthy α] (s : StaticState) (d : DynamicStateGen α) : Prop :=
  ∀ x y, Truthy.isTrue (d.at_p x) → Truthy.isTrue (d.at_p y) → x = y

def AtExists (s : State) : Prop :=
  ∃ x, s.dynamic.at_p x = true

def WellFormed (s : State) : Prop := 
  WellFormedStatic s.statics ∧
  ValidAtParam s.statics s.dynamic ∧
  AtMostOne s.statics s.dynamic ∧
  AtExists s

def WellFormedInit (s : State) : Prop := 
    WellFormed s

def GoalAtOnlyPositive (initial : State) (g : Goal) : Prop :=
  ∀ x, g.dynamic.at_p x ≠ some false

def GoalHasAtTarget (initial : State) (g : Goal) : Prop :=
  ∃ x, g.dynamic.at_p x = some true

def GoalReachableViaTrail (initial : State) (g : Goal) : Prop :=
  ∀ a b, initial.dynamic.at_p a = true → g.dynamic.at_p b = some true →
    Relation.ReflTransGen (fun x y => initial.statics.ontrail_p x y = true) a b

def WellFormedGoal (initial : State) (g : Goal) : Prop := 
  WellFormedStatic initial.statics ∧
  ValidAtParam initial.statics g.dynamic ∧
  AtMostOne initial.statics g.dynamic ∧
  GoalAtOnlyPositive initial g ∧
  GoalHasAtTarget initial g ∧
  GoalReachableViaTrail initial g

def SatisfiesGoal (s : State) (g : Goal) : Prop :=
  (∀ var_loc,
    match g.dynamic.at_p var_loc with
    | none => True
    | some b => s.dynamic.at_p var_loc = b)

def walkPre (var_from : Obj) (var_to : Obj) (s : State) : Prop :=
  s.statics.loc_t var_from = true ∧
  s.statics.loc_t var_to = true ∧
  s.dynamic.at_p var_from = true ∧
  s.statics.adjacent_p var_from var_to = true ∧
  s.statics.ishill_p var_to = false ∧
  s.statics.iswater_p var_from = false

def climbPre (var_from : Obj) (var_to : Obj) (s : State) : Prop :=
  s.statics.loc_t var_from = true ∧
  s.statics.loc_t var_to = true ∧
  s.statics.ishill_p var_to = true ∧
  s.dynamic.at_p var_from = true ∧
  s.statics.adjacent_p var_from var_to = true ∧
  s.statics.iswater_p var_from = false

def walk (var_from : Obj) (var_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_to' =>
        if var_to' = var_to then
          true
        else if var_to' = var_from then
          false
        else
          s.dynamic.at_p var_to'
  }
}

def climb (var_from : Obj) (var_to : Obj) (s : State) : State :=
{
  s with dynamic := {
    s.dynamic with
    at_p :=
      fun var_to' =>
        if var_to' = var_to then
          true
        else if var_to' = var_from then
          false
        else
          s.dynamic.at_p var_to'
  }
}

inductive PlanAction where
  | walk  (var_from : Obj) (var_to : Obj)
  | climb (var_from : Obj) (var_to : Obj)
deriving Repr

def actionPre : PlanAction → State → Prop
  | .walk  var_from var_to, s => walkPre var_from var_to s
  | .climb var_from var_to, s => climbPre var_from var_to s

def actionApply : PlanAction → State → State
  | .walk  var_from var_to, s => walk var_from var_to s
  | .climb var_from var_to, s => climb var_from var_to s

def ValidPlan : List PlanAction → State → Prop
  | [], _ => True
  | a :: as, s => actionPre a s ∧ ValidPlan as (actionApply a s)

def runPlan : List PlanAction → State → State
  | [], s => s
  | a :: as, s => runPlan as (actionApply a s)



-- Part 2) Generated Solve

def gpFindObj? (p : Obj → Bool) : List Obj → Option Obj
  | [] => none
  | x :: xs =>
      if p x = true then
        some x
      else
        gpFindObj? p xs

def gpBuildTrailPlan
    (st : StaticState) (g : Goal) : Nat → Obj → List PlanAction
  | 0, _ => []
  | fuel + 1, current =>
      if g.dynamic.at_p current = some true then
        []
      else
        match gpFindObj?
            (fun nxt => st.ontrail_p current nxt)
            st.objects with
        | none => []
        | some nxt =>
            let action :=
              if st.ishill_p nxt = true then
                PlanAction.climb current nxt
              else
                PlanAction.walk current nxt
            action :: gpBuildTrailPlan st g fuel nxt

def solve (s : State) (g : Goal) : List PlanAction :=
  match gpFindObj?
      (fun loc => s.dynamic.at_p loc)
      s.statics.objects with
  | none => []
  | some start =>
      gpBuildTrailPlan s.statics g s.statics.objects.length start

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

lemma walk_statics (var_from var_to : Obj) (s : State) :
    (walk var_from var_to s).statics = s.statics := rfl

lemma climb_statics (var_from var_to : Obj) (s : State) :
    (climb var_from var_to s).statics = s.statics := rfl

lemma runPlan_statics (plan : List PlanAction) (s : State) :
    (runPlan plan s).statics = s.statics := by
  induction plan generalizing s with
  | nil => simp [runPlan]
  | cons a as ih =>
      simp only [runPlan]
      rw [ih]
      cases a with
      | walk var_from var_to  => exact walk_statics var_from var_to s
      | climb var_from var_to => exact climb_statics var_from var_to s

-- walk only touches at_p
lemma walk_at_p_ne (var_from var_to : Obj) (s : State) {var_to' : Obj} (h1 : var_to' ≠ var_to) (h2 : var_to' ≠ var_from) :
    (walk var_from var_to s).dynamic.at_p var_to' = s.dynamic.at_p var_to' := by
  unfold walk
  simp [h1, h2]

-- climb only touches at_p
lemma climb_at_p_ne (var_from var_to : Obj) (s : State) {var_to' : Obj} (h1 : var_to' ≠ var_to) (h2 : var_to' ≠ var_from) :
    (climb var_from var_to s).dynamic.at_p var_to' = s.dynamic.at_p var_to' := by
  unfold climb
  simp [h1, h2]

lemma walk_at_p_eq1 (var_from var_to : Obj) (s : State) :
    (walk var_from var_to s).dynamic.at_p var_to = true := by
  unfold walk
  simp

lemma walk_at_p_eq2 (var_from var_to : Obj) (s : State) (h1 : var_from ≠ var_to) :
    (walk var_from var_to s).dynamic.at_p var_from = false := by
  unfold walk
  simp [h1]

lemma climb_at_p_eq1 (var_from var_to : Obj) (s : State) :
    (climb var_from var_to s).dynamic.at_p var_to = true := by
  unfold climb
  simp

lemma climb_at_p_eq2 (var_from var_to : Obj) (s : State) (h1 : var_from ≠ var_to) :
    (climb var_from var_to s).dynamic.at_p var_from = false := by
  unfold climb
  simp [h1]

lemma walk_preserves_wf
    (var_from var_to)
    (s : State)
    (hwf : WellFormed s)
    (hpre : walkPre var_from var_to s) :
    WellFormed (walk var_from var_to s) := by
  unfold WellFormed at hwf ⊢
  unfold walkPre at hpre
  rcases hwf with ⟨hStatic, hValidAt, hAtMost, hAtExists⟩
  rcases hpre with
    ⟨hLocFrom, hLocTo, hAtFrom, hAdjacent, hNotHill, hNotWater⟩

  have hOnlyTarget :
      ∀ x, (walk var_from var_to s).dynamic.at_p x = true →
        x = var_to := by
    intro x hx
    by_cases hxt : x = var_to
    · exact hxt
    · by_cases hxf : x = var_from
      · subst x
        have hzero :
            (walk var_from var_to s).dynamic.at_p var_from = false :=
          walk_at_p_eq2 var_from var_to s hxt
        rw [hzero] at hx
        simp at hx
      · have hxOld : s.dynamic.at_p x = true := by
          rw [walk_at_p_ne var_from var_to s hxt hxf] at hx
          exact hx
        have heq : x = var_from :=
          hAtMost x var_from hxOld hAtFrom
        exact (hxf heq).elim

  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [walk_statics]
    exact hStatic
  · unfold ValidAtParam
    intro x hx
    change (walk var_from var_to s).dynamic.at_p x = true at hx
    have hxt : x = var_to := hOnlyTarget x hx
    subst x
    rw [walk_statics]
    exact hLocTo
  · unfold AtMostOne
    intro x y hx hy
    change (walk var_from var_to s).dynamic.at_p x = true at hx
    change (walk var_from var_to s).dynamic.at_p y = true at hy
    have hxt : x = var_to := hOnlyTarget x hx
    have hyt : y = var_to := hOnlyTarget y hy
    exact hxt.trans hyt.symm
  · unfold AtExists
    exact ⟨var_to, walk_at_p_eq1 var_from var_to s⟩

lemma climb_preserves_wf
    (var_from var_to)
    (s : State)
    (hwf : WellFormed s)
    (hpre : climbPre var_from var_to s) :
    WellFormed (climb var_from var_to s) := by
  unfold WellFormed at hwf ⊢
  unfold climbPre at hpre
  rcases hwf with ⟨hStatic, hValidAt, hAtMost, hAtExists⟩
  rcases hpre with
    ⟨hLocFrom, hLocTo, hHill, hAtFrom, hAdjacent, hNotWater⟩

  have hOnlyTarget :
      ∀ x, (climb var_from var_to s).dynamic.at_p x = true →
        x = var_to := by
    intro x hx
    by_cases hxt : x = var_to
    · exact hxt
    · by_cases hxf : x = var_from
      · subst x
        have hzero :
            (climb var_from var_to s).dynamic.at_p var_from = false :=
          climb_at_p_eq2 var_from var_to s hxt
        rw [hzero] at hx
        simp at hx
      · have hxOld : s.dynamic.at_p x = true := by
          rw [climb_at_p_ne var_from var_to s hxt hxf] at hx
          exact hx
        have heq : x = var_from :=
          hAtMost x var_from hxOld hAtFrom
        exact (hxf heq).elim

  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [climb_statics]
    exact hStatic
  · unfold ValidAtParam
    intro x hx
    change (climb var_from var_to s).dynamic.at_p x = true at hx
    have hxt : x = var_to := hOnlyTarget x hx
    subst x
    rw [climb_statics]
    exact hLocTo
  · unfold AtMostOne
    intro x y hx hy
    change (climb var_from var_to s).dynamic.at_p x = true at hx
    change (climb var_from var_to s).dynamic.at_p y = true at hy
    have hxt : x = var_to := hOnlyTarget x hx
    have hyt : y = var_to := hOnlyTarget y hy
    exact hxt.trans hyt.symm
  · unfold AtExists
    exact ⟨var_to, climb_at_p_eq1 var_from var_to s⟩

lemma action_preserves_wf
    {a : PlanAction}
    {s : State}
    (hwf : WellFormed s)
    (hpre : actionPre a s) :
    WellFormed (actionApply a s) := by
  cases a with
  | walk var_from var_to =>
      exact walk_preserves_wf var_from var_to s hwf hpre
  | climb var_from var_to =>
      exact climb_preserves_wf var_from var_to s hwf hpre

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

/-- A trail path stores the vertices visited after the initial vertex. -/
def TrailPath
    (st : StaticState) (src target : Obj) : List Obj → Prop
  | [] => src = target
  | next :: rest =>
      st.ontrail_p src next = true ∧
      TrailPath st next target rest

lemma trailPath_append_single
    {st : StaticState} {a b c : Obj} {xs : List Obj}
    (hpath : TrailPath st a b xs)
    (hedge : st.ontrail_p b c = true) :
    TrailPath st a c (xs ++ [c]) := by
  induction xs generalizing a with
  | nil =>
      change a = b at hpath
      subst b
      change st.ontrail_p a c = true ∧ c = c
      exact ⟨hedge, rfl⟩
  | cons x xs ih =>
      change
        st.ontrail_p a x = true ∧ TrailPath st x b xs
        at hpath
      change
        st.ontrail_p a x = true ∧
          TrailPath st x c (xs ++ [c])
      exact ⟨hpath.1, ih hpath.2⟩

lemma reflTransGen_to_trailPath
    {st : StaticState} {a b : Obj}
    (hreach :
      Relation.ReflTransGen
        (fun x y => st.ontrail_p x y = true) a b) :
    ∃ xs, TrailPath st a b xs := by
  induction hreach with
  | refl =>
      exact ⟨[], rfl⟩
  | tail hreach hedge ih =>
      rcases ih with ⟨xs, hpath⟩
      exact ⟨xs ++ [_], trailPath_append_single hpath hedge⟩

lemma transGen_head
    {α : Type} {r : α → α → Prop} {a b c : α}
    (hab : r a b)
    (hbc : Relation.TransGen r b c) :
    Relation.TransGen r a c := by
  induction hbc with
  | single h =>
      exact Relation.TransGen.tail
        (Relation.TransGen.single hab) h
  | tail h hlast ih =>
      exact Relation.TransGen.tail ih hlast

lemma trailPath_mem_transGen
    {st : StaticState} {a b x : Obj} {xs : List Obj}
    (hpath : TrailPath st a b xs)
    (hmem : x ∈ xs) :
    Relation.TransGen
      (fun u v => st.ontrail_p u v = true) a x := by
  induction xs generalizing a with
  | nil =>
      simp at hmem
  | cons next rest ih =>
      change
        st.ontrail_p a next = true ∧
          TrailPath st next b rest
        at hpath
      simp only [List.mem_cons] at hmem
      rcases hmem with hmem | hmem
      · subst x
        exact Relation.TransGen.single hpath.1
      · exact transGen_head hpath.1 (ih hpath.2 hmem)

lemma trailPath_target_mem
    {st : StaticState} {a b next : Obj} {rest : List Obj}
    (hpath : TrailPath st a b (next :: rest)) :
    b ∈ next :: rest := by
  induction rest generalizing next a with
  | nil =>
      change
        st.ontrail_p a next = true ∧ next = b
        at hpath
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hpath.2.symm
  | cons x xs ih =>
      change
        st.ontrail_p a next = true ∧
          TrailPath st next b (x :: xs)
        at hpath
      exact List.mem_cons_of_mem next (ih hpath.2)

lemma trailPath_nodup
    {st : StaticState} {a b : Obj} {xs : List Obj}
    (hacyclic : OntrailAcyclic st)
    (hpath : TrailPath st a b xs) :
    (a :: xs).Nodup := by
  induction xs generalizing a with
  | nil =>
      simp
  | cons next rest ih =>
      change
        st.ontrail_p a next = true ∧
          TrailPath st next b rest
        at hpath
      have hnotmem : a ∉ next :: rest := by
        intro hmem
        have hcycle :
            Relation.TransGen
              (fun u v => st.ontrail_p u v = true) a a :=
          trailPath_mem_transGen
            (st := st)
            (a := a)
            (b := b)
            (x := a)
            (xs := next :: rest)
            hpath hmem
        exact hacyclic a hcycle
      exact List.nodup_cons.mpr
        ⟨hnotmem, ih hpath.2⟩

lemma trailPath_all_mem_objects
    {st : StaticState} {a b : Obj} {xs : List Obj}
    (hvalid : ValidOntrailParam st)
    (hhierarchy : ValidTypeHierarchy st)
    (hloc : st.loc_t a = true)
    (hpath : TrailPath st a b xs) :
    ∀ x, x ∈ a :: xs → x ∈ st.objects := by
  induction xs generalizing a with
  | nil =>
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst x
      exact hhierarchy a hloc
  | cons next rest ih =>
      change
        st.ontrail_p a next = true ∧
          TrailPath st next b rest
        at hpath
      have hparams := hvalid a next hpath.1
      intro x hx
      rcases List.mem_cons.mp hx with hxa | htail
      · subst x
        exact hhierarchy a hloc
      · exact ih hparams.2 hpath.2 x htail

lemma trailPath_length_lt_objects
    {st : StaticState} {a b : Obj} {xs : List Obj}
    (hobjects : ObjectsUnique st)
    (hvalid : ValidOntrailParam st)
    (hhierarchy : ValidTypeHierarchy st)
    (hacyclic : OntrailAcyclic st)
    (hloc : st.loc_t a = true)
    (hpath : TrailPath st a b xs) :
    xs.length < st.objects.length := by
  have hnodup : (a :: xs).Nodup :=
    trailPath_nodup hacyclic hpath
  have hall :
      ∀ x, x ∈ a :: xs → x ∈ st.objects :=
    trailPath_all_mem_objects
      hvalid hhierarchy hloc hpath
  have hsubset :
      (a :: xs).toFinset ⊆ st.objects.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at hx ⊢
    exact hall x hx
  have hobjectsNodup : st.objects.Nodup := hobjects
  have hlength :
      (a :: xs).length ≤ st.objects.length := by
    calc
      (a :: xs).length =
          (a :: xs).toFinset.card :=
        (List.toFinset_card_of_nodup hnodup).symm
      _ ≤ st.objects.toFinset.card :=
        Finset.card_le_card hsubset
      _ = st.objects.length :=
        List.toFinset_card_of_nodup hobjectsNodup
  exact Nat.lt_of_succ_le (by simpa using hlength)

lemma gpFindObj?_eq_some_of_unique
    (p : Obj → Bool) {xs : List Obj} {x : Obj}
    (hmem : x ∈ xs)
    (hpx : p x = true)
    (hunique : ∀ y, p y = true → y = x) :
    gpFindObj? p xs = some x := by
  induction xs with
  | nil =>
      simp at hmem
  | cons y ys ih =>
      unfold gpFindObj?
      by_cases hy : p y = true
      · rw [if_pos hy]
        rw [hunique y hy]
      · rw [if_neg hy]
        have htail : x ∈ ys := by
          simp only [List.mem_cons] at hmem
          rcases hmem with hxy | hmem
          · subst y
            exact (hy hpx).elim
          · exact hmem
        exact ih htail

lemma gpBuildTrailPlan_correct
    (st : StaticState)
    (g : Goal)
    (target : Obj)
    (hvalid : ValidOntrailParam st)
    (hhierarchy : ValidTypeHierarchy st)
    (hadjacent : OntrailImpliesAdjacent st)
    (hnotwater : OntrailFromNotWater st)
    (hfunctional : OntrailFunctional st)
    (hacyclic : OntrailAcyclic st)
    (hgoalMost : AtMostOne st g.dynamic)
    (hgoalTarget : g.dynamic.at_p target = some true)
    {current : Obj}
    {s : State}
    {xs : List Obj}
    {fuel : Nat}
    (hAt : s.dynamic.at_p current = true)
    (hstat : s.statics = st)
    (hpath : TrailPath st current target xs)
    (hfuel : xs.length ≤ fuel) :
    ValidPlan (gpBuildTrailPlan st g fuel current) s ∧
    (runPlan (gpBuildTrailPlan st g fuel current) s).dynamic.at_p
      target = true := by
  induction xs generalizing current s fuel with
  | nil =>
      change current = target at hpath
      subst target
      cases fuel with
      | zero =>
          constructor
          · simp [gpBuildTrailPlan, ValidPlan]
          · simpa [gpBuildTrailPlan, runPlan] using hAt
      | succ fuel =>
          constructor
          · simp [gpBuildTrailPlan, hgoalTarget, ValidPlan]
          · simpa [gpBuildTrailPlan, hgoalTarget, runPlan] using hAt

  | cons next rest ih =>
      change
        st.ontrail_p current next = true ∧
          TrailPath st next target rest
        at hpath
      rcases hpath with ⟨hedge, hrest⟩

      cases fuel with
      | zero =>
          simp at hfuel
      | succ fuel =>
          have hrestFuel : rest.length ≤ fuel := by
            simpa using hfuel

          have hcurrentNeTarget : current ≠ target := by
            intro heq
            have hfullPath :
                TrailPath st current target (next :: rest) :=
              ⟨hedge, hrest⟩
            have htargetMem : target ∈ next :: rest :=
              trailPath_target_mem hfullPath
            have hcycle :
                Relation.TransGen
                  (fun u v => st.ontrail_p u v = true)
                  current target :=
              trailPath_mem_transGen hfullPath htargetMem
            subst target
            exact hacyclic current hcycle

          have hnotGoal :
              g.dynamic.at_p current ≠ some true := by
            intro hcurrentGoal
            have heq : current = target := by
              apply hgoalMost current target
              · change g.dynamic.at_p current = some true
                exact hcurrentGoal
              · change g.dynamic.at_p target = some true
                exact hgoalTarget
            exact hcurrentNeTarget heq

          have hparams := hvalid current next hedge

          have hnextMem : next ∈ st.objects :=
            hhierarchy next hparams.2

          have hfind :
              gpFindObj?
                  (fun nxt => st.ontrail_p current nxt)
                  st.objects =
                some next := by
            apply gpFindObj?_eq_some_of_unique
            · exact hnextMem
            · exact hedge
            · intro y hy
              exact hfunctional current y next hy hedge

          cases hhill : st.ishill_p next with
          | false =>
              have hpre : walkPre current next s := by
                unfold walkPre
                rw [hstat]
                exact
                  ⟨hparams.1,
                   hparams.2,
                   hAt,
                   hadjacent current next hedge,
                   hhill,
                   hnotwater current next hedge⟩

              have hstat' :
                  (walk current next s).statics = st := by
                calc
                  (walk current next s).statics = s.statics :=
                    walk_statics current next s
                  _ = st := hstat

              have hrec :=
                ih
                  (current := next)
                  (s := walk current next s)
                  (fuel := fuel)
                  (hAt := walk_at_p_eq1 current next s)
                  (hstat := hstat')
                  (hpath := hrest)
                  (hfuel := hrestFuel)

              constructor
              · simpa
                  [gpBuildTrailPlan, hnotGoal, hfind, hhill,
                   ValidPlan, actionPre, actionApply]
                  using And.intro hpre hrec.1
              · simpa
                  [gpBuildTrailPlan, hnotGoal, hfind, hhill,
                   runPlan, actionApply]
                  using hrec.2

          | true =>
              have hpre : climbPre current next s := by
                unfold climbPre
                rw [hstat]
                exact
                  ⟨hparams.1,
                   hparams.2,
                   hhill,
                   hAt,
                   hadjacent current next hedge,
                   hnotwater current next hedge⟩

              have hstat' :
                  (climb current next s).statics = st := by
                calc
                  (climb current next s).statics = s.statics :=
                    climb_statics current next s
                  _ = st := hstat

              have hrec :=
                ih
                  (current := next)
                  (s := climb current next s)
                  (fuel := fuel)
                  (hAt := climb_at_p_eq1 current next s)
                  (hstat := hstat')
                  (hpath := hrest)
                  (hfuel := hrestFuel)

              constructor
              · simpa
                  [gpBuildTrailPlan, hnotGoal, hfind, hhill,
                   ValidPlan, actionPre, actionApply]
                  using And.intro hpre hrec.1
              · simpa
                  [gpBuildTrailPlan, hnotGoal, hfind, hhill,
                   runPlan, actionApply]
                  using hrec.2

lemma satisfiesGoal_of_target
    (final : State)
    (g : Goal)
    (target : Obj)
    (hpositive : ∀ x, g.dynamic.at_p x ≠ some false)
    (hgoalMost : AtMostOne final.statics g.dynamic)
    (hgoalTarget : g.dynamic.at_p target = some true)
    (hfinalTarget : final.dynamic.at_p target = true) :
    SatisfiesGoal final g := by
  unfold SatisfiesGoal
  intro x
  cases hx : g.dynamic.at_p x with
  | none =>
      simp [hx]
  | some b =>
      cases b with
      | false =>
          exact (hpositive x hx).elim
      | true =>
          have heq : x = target := by
            apply hgoalMost x target
            · change g.dynamic.at_p x = some true
              exact hx
            · change g.dynamic.at_p target = some true
              exact hgoalTarget
          subst x
          simpa [hx] using hfinalTarget

-- Main correctness proof
theorem solve_correct
    (s : State)
    (g : Goal)
    (hstatic : WellFormedStatic s.statics)
    (hinit : WellFormedInit s)
    (hgoal : WellFormedGoal s g) :
    ValidPlan (solve s g) s ∧
    SatisfiesGoal (runPlan (solve s g) s) g := by
  have hs := hstatic
  rcases hs with
    ⟨hobjects,
     _hvalidWater,
     _hvalidHill,
     _hvalidAdjacent,
     hvalidTrail,
     hhierarchy,
     _htypeCoverage,
     _hadjacentSymmetric,
     _hadjacentConnected,
     _hminLoc,
     htrailAdjacent,
     htrailNotWater,
     htrailFunctional,
     _htrailInjective,
     htrailAcyclic⟩

  have hinit' : WellFormed s := hinit
  unfold WellFormed at hinit'
  rcases hinit' with
    ⟨_hinitStatic, hvalidAtInit, hatMostInit, hatExists⟩

  have hgoal' := hgoal
  unfold WellFormedGoal at hgoal'
  rcases hgoal' with
    ⟨_hgoalStatic,
     _hvalidAtGoal,
     hatMostGoal,
     hpositive,
     htargetExists,
     hreachable⟩

  rcases hatExists with ⟨start, hstartAt⟩

  have hstartLoc : s.statics.loc_t start = true := by
    apply hvalidAtInit start
    change s.dynamic.at_p start = true
    exact hstartAt

  have hstartMem : start ∈ s.statics.objects :=
    hhierarchy start hstartLoc

  have hfindStart :
      gpFindObj?
          (fun loc => s.dynamic.at_p loc)
          s.statics.objects =
        some start := by
    apply gpFindObj?_eq_some_of_unique
    · exact hstartMem
    · exact hstartAt
    · intro y hy
      apply hatMostInit y start
      · change s.dynamic.at_p y = true
        exact hy
      · change s.dynamic.at_p start = true
        exact hstartAt

  rcases htargetExists with ⟨target, hgoalTarget⟩

  have hreach :
      Relation.ReflTransGen
        (fun x y => s.statics.ontrail_p x y = true)
        start target :=
    hreachable start target hstartAt hgoalTarget

  rcases reflTransGen_to_trailPath hreach with
    ⟨path, hpath⟩

  have hpathLength :
      path.length < s.statics.objects.length :=
    trailPath_length_lt_objects
      hobjects
      hvalidTrail
      hhierarchy
      htrailAcyclic
      hstartLoc
      hpath

  have hbuild :=
    gpBuildTrailPlan_correct
      s.statics
      g
      target
      hvalidTrail
      hhierarchy
      htrailAdjacent
      htrailNotWater
      htrailFunctional
      htrailAcyclic
      hatMostGoal
      hgoalTarget
      (current := start)
      (s := s)
      (xs := path)
      (fuel := s.statics.objects.length)
      hstartAt
      rfl
      hpath
      (Nat.le_of_lt hpathLength)

  have hsolve :
      solve s g =
        gpBuildTrailPlan
          s.statics g s.statics.objects.length start := by
    simp [solve, hfindStart]

  rw [hsolve]

  constructor
  · exact hbuild.1
  · have hfinalStatics :
        (runPlan
          (gpBuildTrailPlan
            s.statics g s.statics.objects.length start)
          s).statics =
        s.statics :=
      runPlan_statics
        (gpBuildTrailPlan
          s.statics g s.statics.objects.length start)
        s

    apply satisfiesGoal_of_target
      (final :=
        runPlan
          (gpBuildTrailPlan
            s.statics g s.statics.objects.length start)
          s)
      (g := g)
      (target := target)
      hpositive
    · rw [hfinalStatics]
      exact hatMostGoal
    · exact hgoalTarget
    · exact hbuild.2

-- Part 5) Prevent cheating

#check (solve_correct : ∀ (s : State) (g : Goal), WellFormedStatic s.statics → WellFormedInit s → WellFormedGoal s g → ValidPlan (solve s g) s ∧ SatisfiesGoal (runPlan (solve s g) s) g)
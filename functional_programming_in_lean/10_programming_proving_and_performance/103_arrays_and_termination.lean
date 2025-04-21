-- # Examples

-- ## Inequality

class LE2 (α : Type u) where
  le : α → α → Prop

class LT2 (α : Type u) where
  lt : α → α → Prop

instance : LE2 Nat where
  le := Nat.le

-- ### Inductively-defined propositions, predicates, and relations

inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve

theorem fairly_easy : EasyToProve := by
  constructor

theorem fairly_easy2 : EasyToProve := EasyToProve.heresTheProof

inductive True2 : Prop where
  | intro : True2

inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by
  constructor

inductive IsFive : Nat → Prop where
  | isFive : IsFive 5

theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor

-- Direct evidence is more concise
theorem three_plus_two_five2 : IsThree n → IsFive (n + 2)
  -- `IsFive (3 + 2)` is definitionally equal to `IsFive 5`.
  | .isThree => .isFive

theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h

theorem four_is_not_three2 : ¬ IsThree 4 :=
  Not.intro (fun h => nomatch h)

theorem four_is_not_three3 : ¬ IsThree 4 :=
  Not.intro nofun

-- ### Inequality of natural numbers

inductive Nat.le2 (n : Nat) : Nat → Prop
  | refl : Nat.le2 n n
  | step : Nat.le2 n m → Nat.le2 n (m + 1)

theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))

theorem four_le_seven2 : 4 ≤ 7 := by
  repeat constructor

def Nat.lt2 (n m : Nat) : Prop :=
  Nat.le2 (n + 1) m

instance : LT2 Nat where
  lt := Nat.lt2

-- A value of type `5 ≤ 7` is evidence of `4 < 7`
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)

-- ## Proving termination

def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else
    soFar

def arrayMapHelper2 (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper2 f arr (soFar.push (f arr[i])) (i + 1)
  else
    soFar
termination_by arr.size - i

def Array.map2 (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else
      findHelper arr p (i + 1)
  else
    none
termination_by arr.size - i

def Array.find2 (arr : Array α) (p : α → Bool) : Option (Nat × α) :=
  findHelper arr p 0

-- # Practice

-- ## Proving that `IsThree n` is equivalent to `n = 3`

-- ### By direct evidence

theorem is_three_to_eq_three {x : Nat} (h : IsThree x) : x = 3 :=
  match x with
  | 3 => rfl

theorem eq_three_to_is_three {x : Nat} (h : x = 3) : IsThree x :=
  match x with
  | 3 => IsThree.isThree

theorem is_three_equiv_eq_three {x : Nat} : (IsThree x) ↔ (x = 3) :=
  Iff.intro is_three_to_eq_three eq_three_to_is_three

theorem is_three_eq_eq_three {x : Nat} : (IsThree x) = (x = 3) :=
  Eq.propIntro is_three_to_eq_three eq_three_to_is_three

-- ### By tactics

theorem is_three_to_eq_three2 {x : Nat} (h : IsThree x) : x = 3 := by
  cases h
  rfl -- `constructor` also works

theorem eq_three_to_is_three2 {x : Nat} (h : x = 3) : IsThree x := by
  cases h
  constructor

theorem is_three_equiv_eq_three2 {x : Nat} : (IsThree x) ↔ (x = 3) := by
  constructor
  case mp => exact is_three_to_eq_three2
  case mpr => exact eq_three_to_is_three2

theorem is_three_eq_eq_three2 {x : Nat} : (IsThree x) = (x = 3) := by
  simp
  exact is_three_equiv_eq_three2

-- ## Using a proposition to find in an array

#eval #[1, 2, 3, 4].find2 ( · > 2 ) -- Parameter type is `α → Bool`
#check ( · > 2 ) -- Type `Nat → Prop`

def pred1 {α : Type u} (_a : α) : Prop :=
  EasyToProve
#check (pred1) -- Type `?m.29248 → Prop`
-- #eval #[1, 2, 3, 4].find2 pred1 -- Type mismatch. Why did `( · > 2 )` work?

instance instDecidableEasyToProve : Decidable EasyToProve :=
  Decidable.isTrue EasyToProve.heresTheProof

instance instDecidablePredPred1 {α : Type u} : DecidablePred (α := α) (pred1 (α := α)) :=
  fun _ => instDecidableEasyToProve

def findWithPredHelper (arr : Array α) (p : α → Prop) [DecidablePred p] (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else
      findWithPredHelper arr p (i + 1)
  else
    none
termination_by arr.size - i

def Array.findWithPred (arr : Array α) (p : α → Prop) [DecidablePred p] : Option (Nat × α) :=
  findWithPredHelper arr p 0

#eval #[1, 2, 3, 4].findWithPred ( · > 2 )

#eval #[1, 2, 3, 4].findWithPred pred1

-- Explicitly passing typeclass instances
#eval @Array.findWithPred Nat #[1, 2, 3, 4] pred1 instDecidablePredPred1

-- # Exercises

-- ## ForM instance for arrays

def arrayForMHelper [Monad m] (arr : Array α) (action : α → m PUnit) (i : Nat) : m PUnit :=
  if h : i < arr.size then do
    let x := arr[i]
    action x
    arrayForMHelper arr action (i + 1)
  else
    pure ()
termination_by arr.size - i -- The `termination_by` clause is optional

def Array.forM2 [Monad m] (arr : Array α) (action : α → m PUnit) : m PUnit :=
  arrayForMHelper arr action 0

instance : ForM m (Array α) α where
  forM := Array.forM2

#eval forM #[1, 2, 3, 4] IO.println
#eval OptionT.run (forM #[1, 2, 3, 4] (fun x =>
  if x < 4 then
    OptionT.lift (do
      IO.println x)
  else failure
))

-- ## Reversing arrays

-- This function is structurally recursive on `i`
def arrayReverseHelper(arr soFar : Array α) (i : Nat) (hi : i ≤ arr.size) : Array α :=
  match i with
  | 0 => soFar
  | j + 1 =>
    let x := arr[j]
    let hj : j ≤ arr.size := by
      rw [Nat.le_iff_lt_or_eq]
      constructor
      exact hi
    arrayReverseHelper arr (soFar.push x) j hj

def Array.reverse2 (arr : Array α): Array α :=
  arrayReverseHelper arr Array.empty arr.size (Nat.le_of_eq rfl)

#eval #[1, 2, 3, 4].reverse2
#eval #[4].reverse2
#eval (#[].reverse2 : Array Nat)

-- ## Using for-in with arrays

def Array.map3 (f : α → β) (arr : Array α) : Array β := Id.run do
  let mut result := Array.empty
  for x in arr do
    result := result.push (f x)
  pure result

#eval #[1, 2, 3, 4].map3 (· * 2)

def Array.find3 (arr : Array α) (p : α → Bool) : Option (Nat × α) := Id.run do
  let mut i := 0
  for x in arr do
    if p x then return some ⟨i, x⟩
    i := i + 1
  pure none

#eval #[1, 2, 3, 4].find3 (· == 3)
#eval #[1, 2, 3, 4].find3 (· == 5)

def Array.forM3 [Monad m] (arr : Array α) (action : α → m PUnit) : m PUnit := do
  for x in arr do
    action x
  pure ()

instance : ForM m (Array α) α where
  forM := Array.forM3

#eval forM #[1, 2, 3, 4] IO.println

-- An inefficient version of `reverse`, but there is no need
-- for explicit indexing
def Array.reverse3 (arr : Array α): Array α := Id.run do
  let mut result := Array.empty
  for x in arr do
    result := #[x] ++ result
  pure result

#eval #[1, 2, 3, 4].reverse3
#eval #[4].reverse3
#eval (#[].reverse3 : Array Nat)

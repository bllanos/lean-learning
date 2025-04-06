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

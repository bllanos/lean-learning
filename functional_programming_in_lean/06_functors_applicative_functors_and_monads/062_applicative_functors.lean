-- # Examples

#check Applicative

instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()
--  | some g => Functor.map g (x ())

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .ok g => g <$> x ()
    | .error e => .error e

-- `E1 <*> E2`
-- =
-- `Seq.seq E1 (fun () => E2)`

def optionPlus : Option (Nat → Nat → Nat) := some (Add.add (α := Nat))
def optionPlus2 : Option (Nat → Nat) := optionPlus <*> some 4
def optionPlus3 : Option Nat := optionPlus2 <*> some 5
#eval optionPlus3 -- `some 9`

structure Pair (α β : Type) : Type where
  first : α
  second : β

instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩

-- id <$> Pair.mk x y = Pair.mk x y
-- f <$> g <$> Pair.mk x y = (f ∘ g) <$> Pair.mk x y

-- Pair is not Applicative
-- def Pair.pure (x : β) : Pair α β := Pair.mk _ x

-- ## A non-monadic applicative

-- ### User input

structure RawInput where
  name : String
  birthYear : String

-- ### Subtypes

structure Subtype2 {α : Type} (p : α → Prop) where
  val : α
  property : p val

def FastPos : Type := { x : Nat // x > 0 }
def FastPos2 : Type := Subtype (α := Nat) (fun x => x > 0)

def one : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp_arith⟩

def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else
    none

-- ### Validated Input

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys : (NonEmptyList α) :=
    { head := xs.head, tail := xs.tail ++ (List.cons ys.head ys.tail) }

structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkBirthYear (thisYear year : Nat) : Validate (Field × String) {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [h, h']⟩
    else reportError "birth year" s!"Must be no later than {thisYear}"
  else reportError "birth year" s!"Must be after 1900"

#check CheckedInput.mk

def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  -- <*> is left-associative
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "invalid"}

-- # Examples

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def NatPoint : Type := PPoint Nat

def natOrigin2 : NatPoint :=
  { x := Nat.zero, y := Nat.zero }

#check natOrigin
#check natOrigin2

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

structure PPoint2 (α : Type) (β : Type) where
  x : α
  y : β
deriving Repr

def replaceX2 (α : Type) (β : Type) (γ : Type) (point : PPoint2 α β) (newX : γ) : PPoint2 γ β :=
  { point with x := newX }

#check (replaceX2)

#check replaceX2 Nat
#check replaceX2 Nat Nat Nat { x := 0, y := 0}
#check replaceX2 Nat Nat Float { x := 0, y := 0} 5.0
#eval replaceX2 Nat Nat Float { x := 0, y := 0} 5.0

inductive Sign where
  | pos
  | neg

def signAsNumber (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
    | Sign.pos => 1
    | Sign.neg => -1

#eval signAsNumber Sign.pos
#eval signAsNumber Sign.neg
#check signAsNumber Sign.pos
#check (signAsNumber Sign.pos : Nat)
#check (signAsNumber Sign.pos : Int)
-- #check (signAsNumber Sign.neg : Nat)

-- A function that returns a type!?
def signAsNumberReturnType (s : Sign) : Type :=
  match s with | Sign.pos => Nat | Sign.neg => Int
def signAsNumber2 (s : Sign) : signAsNumberReturnType s :=
  match s with
    | Sign.pos => (1 : Nat)
    | Sign.neg => (-1 : Int)

abbrev signAsNumberReturnType2 (s : Sign) : Type :=
  match s with | Sign.pos => Nat | Sign.neg => Int
-- The type annotations above were necessary as the following does not type check.
-- It does type check if `signAsNumberReturnType2` is used instead of `signAsNumberReturnType`.
-- def signAsNumber3 (s : Sign) : signAsNumberReturnType s :=
--   match s with
--     | Sign.pos => 1
--     | Sign.neg => -1

-- ## Linked lists

def primesUnder10 : List Nat := [2, 3, 5, 7]

inductive List2 (α : Type) where
  | nil : List2 α
  | cons : α → List2 α → List2 α
deriving Repr

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
#eval explicitPrimesUnder10

#check (List.cons)
#check (List2.cons)

def List2.length1 (α : Type) (list : List2 α) : Nat :=
  match list with
    | nil => Nat.zero
    | cons _ tail => Nat.succ tail.length1

#eval List2.length1 Nat List2.nil
#eval List2.length1 Nat (List2.cons 2 (List2.cons 1 List2.nil))
-- Is type inference used for the first parameter?
#eval (List2.cons 2 (List2.cons 1 List2.nil)).length1

#eval List.length ["Sourdough", "bread"]
#check List.length

def length2 (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length2 α ys)

def length3 (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length3 α ys)

-- ## Implicit arguments

def replaceX3 {α : Type} (point : PPoint α) (newX: α) : PPoint α :=
  { point with x := newX }

#eval replaceX3 natOrigin 5

def length4 {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length4 ys)

#eval length3 Nat primesUnder10
#eval length4 primesUnder10
-- Passing arguments by name
#eval length4 (α := Nat) primesUnder10
#eval length4 (α := Nat) (xs := primesUnder10)
-- Arguments passed by name can be reordered
#eval length4 (xs := primesUnder10) (α := Nat)
#eval primesUnder10.length

-- "point wise" definition
def natListLength (xs : List Nat) : Nat := length4 xs
-- "point free" definition
def natListLength2 := length4 (α := Nat)
#eval natListLength [1, 2, 3]
#eval natListLength2 [1, 2, 3]
-- #eval natListLength2 [-1, 2, 3]

-- ## More built-in datatypes

inductive Option2 (α : Type) : Type where
  | none : Option2 α
  | some (val : α) : Option2 α

-- Explicit type annotations were optional
inductive Option3 {α : Type} where
  | none
  | some (val : α)
deriving Repr

def head2? {α : Type} (xs : List α) : Option2 α :=
  match xs with
  | [] => Option2.none
  | y :: _ => Option2.some y

def head3? {α : Type} (xs : List α) : Option3 (α := α):=
  match xs with
  | [] => Option3.none
  | y :: _ => Option3.some y

#eval head3? (α := Nat) []
#eval head3? [4, 1]

#eval primesUnder10.head?
#eval primesUnder10.headD 1
#eval primesUnder10.head!
#check [1].head
-- #eval [].head?
#eval [].head? (α := Nat)
#eval (List.nil (α := Nat)).head?
#eval ([] : List Nat).head?
-- Panics
-- #eval ([] : List Nat).head!

structure Prod2 (α : Type) (β : Type) : Type where
  fst: α
  snd: β

#check Nat × Int
#check Prod Nat Int

def fives : String × Int := { fst := "five", snd := 5 }
def fives2 : String × Int := ("five", 5)
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
-- Amounts to a nested pair (right-associative nesting)
def sevens2 : String × (Int × Nat) := ("VII", (7, 4 + 3))

inductive Sum2 {α : Type} {β : Type} : Type where
  | inl : α → Sum2
  | inr : β → Sum2

#check Nat ⊕ Int
#check Sum Nat Int

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex"]

def countDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | pet :: remainingPets => (match pet with
    | Sum.inl _ => 1
    | Sum.inr _ => 0
  ) + countDogs remainingPets

#eval countDogs animals

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

inductive Unit2 : Type where
  | unit : Unit2
#check (Unit2.unit)
def aUnit : Unit2 := Unit2.unit

inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann

#check (ArithExpr.int)
#check (ArithExpr Unit)
#check (ArithExpr.int ())

def HalfSum (α : Type) : Type := Sum Empty α
def halfSum5 : (HalfSum Nat) := Sum.inr 5
-- Cannot do anything here
-- def halfSumEmpty : (HalfSum Nat) := Sum.inl

def one : Bool ⊕ Unit := Sum.inl false
def two : Bool ⊕ Unit := Sum.inl true
def three : Bool ⊕ Unit := Sum.inr ()

inductive MyType {α : Type} : Type where
  | ctor : α → MyType
def ofFive := MyType.ctor 5
#check ofFive
inductive MyType2 (α : Type) : Type where
  | ctor : α → MyType2 α
#check (MyType2.ctor)
-- set_option diagnostics true
def ofSix := MyType2.ctor (-6: Int)
#check ofSix

-- # Exercises

def lastEntry {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: ys => match ys with
    | [] => y
    | _ => lastEntry ys
#eval lastEntry [3, 4, 5]
#eval lastEntry (α := Nat) []
#eval lastEntry [3]

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys => match (predicate y) with
    | true => y
    | false => ys.findFirst? predicate
#eval [3, 4, 5].findFirst? (fun a => a == 4)
#eval [3, 4, 5].findFirst? (fun a => a == 6)
#eval [].findFirst? (fun a => a == 4)

def Prod.swap2 {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)
#eval (3, "hello").swap

inductive PetName2 : Type where
  | Dog (a : String)
  | Cat (a : String)
  | Bird : (a : String) → PetName2 -- Full form of the function declaration
#check (PetName2.Cat)

def animals2 : List PetName2 :=
  [PetName2.Dog "Spot", PetName2.Cat "Tiger", PetName2.Bird "Fifi", PetName2.Dog "Rex", PetName2.Cat "Floof"]

def howManyDogs2 (pets : List PetName2) : Nat :=
  match pets with
  | [] => 0
  -- Function calls have higher priority than infix operators
  | PetName2.Dog _ :: morePets => howManyDogs2 morePets + 1
  | _ :: morePets => howManyDogs2 morePets
#eval howManyDogs2 animals2

def List.zip2 {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs => match ys with
    | [] => []
    | y :: ys => (x, y) :: xs.zip2 ys
    -- | y :: ys => List.cons (x, y) (xs.zip2 ys)
#eval [2, 3, 4].zip2 [5, 6, 7, 8]

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match xs with
  | [] => []
  | y :: ys => match n with
    | Nat.zero => []
    | Nat.succ nMinusOne => y :: take nMinusOne ys
#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]

def distribute {α β γ : Type} (pair : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match pair.snd with
  | Sum.inl b => Sum.inl (pair.fst, b)
  | Sum.inr c => Sum.inr (pair.fst, c)
#eval distribute ((5, Sum.inl true) : (Nat × (Bool ⊕ String)))

def timesTwo {α : Type} (b : Bool × α) : α ⊕ α :=
  match b.fst with
  | true => Sum.inl b.snd
  | false => Sum.inr b.snd

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
-- The type annotations above were necessary as the following does not type check
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

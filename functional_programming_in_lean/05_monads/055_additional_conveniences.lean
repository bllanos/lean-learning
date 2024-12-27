-- # Examples

-- ## Shared argument types

def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none

def equal2? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none

-- ## Leading dot notation

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)

def BinTree.mirror2 : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf

#check (.empty : BinTree Nat)

-- ## Or-patterns

inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr

def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false

def Weekday.isWeekend2 (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false

def Weekday.isWeekend3 (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false

def Weekday.isweekend4 : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

def condense : α ⊕ α → α
  | .inl x | .inr x => x

def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"

def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, _x) | .inr (n, _y) => n

def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (_n, str) | .inr (_n, _y) => str

#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
#eval getTheString (.inr (20, "twenty"))

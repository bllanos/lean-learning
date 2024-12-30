-- # Examples

#check Prop
#check Type
#check Type 1

theorem additiveUnit (n : Nat) : n = n + 0 :=
  rfl

#check (additiveUnit)

-- ## User defined types

inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α

#check (MyList)

-- def myListOfNat : MyList Type :=
--   .cons Nat .nil

-- inductive MyList2 (α : Type 1) : Type where
--   | nil : MyList2 α
--   | cons : α → MyList2 α → MyList2 α

inductive MyList2 (α : Type 1) : Type 1 where
  | nil : MyList2 α
  | cons : α → MyList2 α → MyList2 α

#check (MyList2)

def myListOfNat : MyList2 Type :=
  .cons Nat .nil

-- ## Universe polymorphism

inductive MyList3 (α : Type u) : Type u where
  | nil : MyList3 α
  | cons : α → MyList3 α → MyList3 α

#check (MyList3)
#check MyList3

def myListOfNumbers : MyList3 Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat2 : MyList3.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList3 (Type → Type) :=
  .cons MyList3 .nil

def myListOfList2 : MyList3.{1} (Type → Type) :=
  .cons MyList3.{0} .nil

inductive Sum2 (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum2 α β
  | inr : β → Sum2 α β

def stringOrNat : Sum2 String Nat := .inl "hello"
def typeOrType : Sum2 Type Type := .inr Nat
-- def stringOrType : Sum2 String Type := .inr Nat

#check max
inductive Sum3 (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum3 α β
  | inr : β → Sum3 α β

def stringOrType : Sum3 String Type := .inr Nat

-- ### Prop and polymorphism

def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]

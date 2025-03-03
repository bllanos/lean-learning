-- # Examples

#check Type 0
#check (Type → Type)
#check (Nat → Nat : Type 0)
#check (Nat → Type : Type 1)

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

inductive WithParameter (α : Type u) : Type u where
  | test : α → WithParameter α

inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β

inductive WithParameterAfterColon : Type u → Type u where
  | test : α → WithParameterAfterColon α

inductive WithParameterAfterColon2 : Type u → Type u where
  | test1 : α → WithParameterAfterColon2 α
  | test2 : WithParameterAfterColon2 α

inductive WithParameterAfterColonDifferentNames : Type u → Type u where
  | test1 : α → WithParameterAfterColonDifferentNames α
  | test2 : β → WithParameterAfterColonDifferentNames β

-- "inductive datatype parameter mismatch β expected α"
-- inductive WithParameterBeforeColonDifferentNames (α : Type u) : Type u where
--   | test1 : α → WithParameterBeforeColonDifferentNames α
--   | test2 : β → WithParameterBeforeColonDifferentNames β

-- Either α is an index, not a parameter, or α should have been written
-- instead of α × α.
-- inductive WithNamedIndex (α : Type u) : Type (u + 1) where
--   | test1 : WithNamedIndex α
--   | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)

-- Using α as an index
inductive WithIndex : Type u → Type (u + 1) where
  | test1 : WithIndex α
  | test2 : WithIndex α → WithIndex α → WithIndex (α × α)

-- Universe mismatch because a parameter is mistaken as an index
-- inductive ParamAfterIndex : Nat → Type u → Type u where
--   | test1 : ParamAfterIndex 0 γ
--   | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ

-- This is accepted, but is a mistake. The parameter should be
-- listed before the index so that the compiler will allow
-- the type to be in the same universe as the parameter.
inductive ParamAfterIndex : Nat → Type u → Type (u + 1) where
  | test1 : ParamAfterIndex 0 γ
  | test2 : ParamAfterIndex n γ → ParamAfterIndex k γ → ParamAfterIndex (n + k) γ

inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5

-- Output the number of parameters in a type
#print NatParam
#print Vect

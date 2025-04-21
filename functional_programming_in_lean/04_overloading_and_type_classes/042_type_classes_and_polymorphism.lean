-- # Examples

#check (IO.println)
-- Ask for the full signature of the function
#check @IO.println
#check (@IO.println) -- Same output

-- ## Defining polymorphic functions with instance implicits

def sumList {α: Type u} [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + sumList xs

def fourNats : List Nat := [1, 2, 3, 4]

#eval sumList fourNats

-- '@' makes typeclass instance and other parameters explicit
#eval @sumList Nat instAddNat _ fourNats

structure PPoint {α : Type} where
  x : α
  y : α
deriving Repr

instance [Add α] : Add (PPoint (α := α)) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }

-- ## Methods and implicit arguments

#check OfNat
#check @OfNat
#check @OfNat.ofNat

-- # Exercises

-- ## Even number literals

inductive Even : Type where
  | zero : Even
  | succ : Even → Even

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.succ n => n.toNat + 2

instance : ToString Even where
  toString := toString ∘ Even.toNat

instance [OfNat Even n]: OfNat Even (n + 2) where
  ofNat := Even.succ (OfNat.ofNat n)

instance : OfNat Even 0 where
  ofNat := Even.zero

def eight : Even := 8
#eval eight
def zero : Even := 0
#eval zero

-- def one : Even := 1

-- ## Recursive instance search depth

-- The recursive instance search must be limited to depth 128?
#eval (254 : Even)
#eval 254 / 2

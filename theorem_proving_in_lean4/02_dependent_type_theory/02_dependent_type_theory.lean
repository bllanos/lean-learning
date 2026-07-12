-- # Examples

-- ## 2.1 Simple type theory

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

-- #check: reports types
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat × Nat → Nat
-- Equivalent to
#check (Nat × Nat) → Nat
#check (Nat → Nat) → Nat
-- Not equivalent to
#check Nat → Nat → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add

#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
-- .n is a notation for .fst, .snd, etc.
#check (5, 9).1

#eval Nat.succ 2
#eval Nat.add 5 2
-- #eval Nat.add 3 -- Cannot synthesize `Repr` for type `Nat → Nat`
#eval (5, 9).1
#eval (5, 9).2

-- ## Types as objects

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat
#check Nat → Nat → Bool

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat

#check List α
#check List Nat

#check Type -- Abbreviation for `Type 0`
#check Type 0
#check Type 1
#check Type 2
#check Type 3
#check Type 4

def t1 : Type 1 := Type 0
-- It seems that objects in a universe are not in higher universes.
-- def t2 : Type 2 := Type 0
def t2 : Sort 1 := Nat
def t3 : Sort 0 := True
#check Prop -- Type
def t4 : Type := Prop

-- Polymorphism over universes of types
#check List
-- List.{u} (α : Type u) : Type u
#check Prod
-- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

universe u
def F' (α : Type u) : Type u := Prod α α
#check F'
-- Leaving the universe level implicit
def F'' (α : Type v) : Type v := Prod α α
#check F''
def F'''.{w} (α : Type w) : Type w := Prod α α
#check F'''

-- ## 2.3 Function abstraction and evaluation

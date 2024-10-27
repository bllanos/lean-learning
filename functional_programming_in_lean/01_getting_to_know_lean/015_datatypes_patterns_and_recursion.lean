-- # Examples

inductive Bool2 where
  | false2 : Bool2
  | true2 : Bool2
deriving Repr
-- These constructors do not take any arguments
#check (Bool2.false2)
def b2 : Bool2 := Bool2.true2
#eval b2
#eval Bool2.toCtorIdx b2
#eval Bool2.false2.toCtorIdx
-- What is this?
#check Bool2.noConfusionType

def false2 := Bool2.false2
def b22 : Bool2 := false2
#check (false2)
#check b22
#eval b22
#eval false2

inductive Nat2 where
  | zero : Nat2
  | succ (n : Nat2) : Nat2
deriving Repr

#eval Nat2.succ Nat2.zero

#check Nat2.succ (Nat2.zero)

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero Nat.zero
#eval isZero (Nat.succ Nat.zero)
#eval isZero 3

def negate (n : Nat) : Int :=
  match n with
  | Nat.zero => (0 : Int)
  | Nat.succ nMinusOne => Int.sub (negate nMinusOne) (1 : Int)

#eval negate 9
-- Large exponents produce a stack overflow
#eval negate (2 ^ 4)

def pred (n: Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 0
#eval pred 4

structure Point3D where
  x : Float
  y : Float
  z : Float

def depth (p: Point3D) : Float :=
  match p with
  | { x := _, y := _, z := d } => d

#eval depth {x := 1.0, y := 2.0, z := 3.0 }
#eval {x := 1.0, y := 2.0, z := 3.0 : Point3D }.z

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 4
#eval even 1

-- Non-terminating recursion is ill-formed
-- def evenLoops (n : Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)

def plus (a b : Nat) : Nat :=
  match a with
  | Nat.zero => b
  | Nat.succ a' => Nat.succ (plus a' b)

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => match n with
    | Nat.zero => Nat.zero
    | Nat.succ n' => minus n' k'

#eval minus 7 3
#eval minus 7 0
#eval minus 7 7
#eval minus 1 8

-- Not structurally recursive
-- Requires a manual proof of termination
-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then
--     0
--   else Nat.succ (div (n - k) k)

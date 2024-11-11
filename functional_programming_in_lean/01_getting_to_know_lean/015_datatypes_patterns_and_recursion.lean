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

-- # Practice

-- Version of `negate` that does not overflow the stack
-- because it uses tail recursion
def negate2Inner (n : Nat) (accumulator : Int): Int :=
  match n with
  | Nat.zero => accumulator
  | Nat.succ nMinusOne => negate2Inner nMinusOne (Int.sub accumulator (1 : Int))
def negate2 (n: Nat): Int :=
  negate2Inner n 0

#eval negate2 9
#eval negate2 (2 ^ 15)

-- Evaluation of Fibonacci numbers
--
-- Based on an example from:
--   Category Theory for Programmers, by Bartosz Milewski,
--   compiled and edited by Igal Tabachnik
--   (https://github.com/hmemcpy/milewski-ctfp-pdf/releases)
inductive NatF (α : Type) where
  | ZeroF
  | SuccF (a : α)
-- Imitating `newtype Fix f = Fix (f (Fix f))`
-- The following fails to show termination
-- def NatFixedPoint : Type := NatF (NatFixedPoint)
inductive NatFixedPoint where
  | ZeroNatFixedPoint
  | SuccFixedPoint (n : NatFixedPoint)
def unFixNat (n : NatFixedPoint) : (NatF NatFixedPoint) :=
  match n with
  | NatFixedPoint.ZeroNatFixedPoint => NatF.ZeroF
  | NatFixedPoint.SuccFixedPoint nMinusOne => NatF.SuccF nMinusOne
def fmapNatF {α : Type} {β : Type} (f : α → β) (n : NatF α) : NatF β :=
  match n with
  | NatF.ZeroF => NatF.ZeroF
  | NatF.SuccF nMinusOne => NatF.SuccF (f nMinusOne)

def fmapNatFixedPoint {β : Type} (zero: β) (f : β → β) (n : NatFixedPoint) : β :=
  match n with
  | NatFixedPoint.ZeroNatFixedPoint => zero
  | NatFixedPoint.SuccFixedPoint nMinusOne => f (fmapNatFixedPoint zero f nMinusOne)

-- The following fails to show termination
-- def catamorphism {α : Type} (eval : (NatF α) → α) (n : NatFixedPoint) : α :=
--   match n with
--   | NatFixedPoint.ZeroNatFixedPoint => eval NatF.ZeroF
--   | NatFixedPoint.SuccFixedPoint nMinusOne => eval (fmapNatF (catamorphism eval) (unFixNat nMinusOne))

def evalAdapter {β : Type} (eval : NatF β → β) (x: β) : β :=
  eval (NatF.SuccF x)
def catamorphism {β : Type} (eval : NatF β → β) (n : NatFixedPoint) : β :=
  fmapNatFixedPoint (eval NatF.ZeroF) (evalAdapter eval) n

def fib (n : NatF (Nat × Nat)) : (Nat × Nat) :=
  match n with
  | NatF.ZeroF => (1, 1)
  | NatF.SuccF (m, n) => (n, m + n)

def natFixedPointEval (n : NatFixedPoint) : (Nat × Nat) :=
  catamorphism fib n

#eval natFixedPointEval NatFixedPoint.ZeroNatFixedPoint
#eval natFixedPointEval (NatFixedPoint.SuccFixedPoint (NatFixedPoint.ZeroNatFixedPoint))
#eval natFixedPointEval (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.ZeroNatFixedPoint)))
#eval natFixedPointEval (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.ZeroNatFixedPoint))))
#eval natFixedPointEval (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.SuccFixedPoint (NatFixedPoint.ZeroNatFixedPoint)))))

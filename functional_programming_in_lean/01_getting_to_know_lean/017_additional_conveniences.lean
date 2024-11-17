-- # Examples

-- ## Automatic implicit arguments

def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

def length2 (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length2 ys)

-- ## Pattern-matching definitions

def length3 : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length3 ys)

def drop : Nat → List α → List α
  | _, [] => []
  | Nat.zero, xs => xs
  | Nat.succ n, _ :: xs => (drop n xs)

def Option.getD2 (default : α) : Option α → α
  | none => default
  | some x => x
#eval (some "salmonberry").getD2 ""
#eval none.getD2 ""

-- ## Local definitions

def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: abs => ((a :: (unzip abs).fst), (b :: (unzip abs).snd))

def unzip2 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip2 xys
    (x :: unzipped.fst, y :: unzipped.snd)

-- Single line `let` constructs use a semicolon between the definition
-- and the body
def double5 : Nat × Nat :=
  let x := 5; (x, x)
#eval double5

def unzip3 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip3 xys
    (x :: xs, y :: ys)

-- `let` requires explicit recursion with `let rec`
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

-- ## Type inference

def unzip4 : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip4 xys
    (x :: unzipped.fst, y :: unzipped.snd)

def unzip5 (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) := unzip xys
    (x :: xs, y :: ys)

def id2 (x : α) : α := x

-- ## Simultaneous matching

def drop2 (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n, _ :: ys => drop2 n ys

-- ## Natural number patterns

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

def even2 : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)

def halve : Nat → Nat
  | 0 => 0
  | n + 1 => match n with
    | 0 => 0
    | m + 1 => 1 + halve m
#eval halve 101

def halve2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  -- The literal must be the argument on the right in the natural number pattern
  --| 2 + n => halve2 n + 1
  | n + 2 => halve2 n + 1

-- ## Anonymous functions

#check (fun x => x + 1)
#check fun (x : Int) => x + 1
#check fun {α : Type} (x : α) => x

#check fun
  | 0 => none
  | n + 1 => some n

def double : Nat → Nat := fun
  | 0 => 0
  | n + 1 => double n + 2

#check (. + 1)
#check (. + 5, 3)
#check ((. + 5), 3)
#check (., .) 1 2
#eval (., .) 1 2

#eval (fun x => x + x) 5
#eval (. * 2) 5

-- ## Namespaces

def Nat.double (x : Nat) : Nat := x + x
#eval (4 : Nat).double

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
namespace Inner
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end Inner
end NewNamespace

#check NewNamespace.triple
#check NewNamespace.Inner.quadruple

def timesTwelve (x : Nat) :=
  open NewNamespace in
  Inner.quadruple (triple x)

def timesTwelve2 (x : Nat) :=
  open NewNamespace.Inner in
  -- Opening a namespace does not open its parent namespace
  quadruple (NewNamespace.triple x)

def timesTwelve3 (x : Nat) :=
  open NewNamespace in
  open Inner in
  quadruple (triple x)

open NewNamespace in
#check triple
-- The `open ... in` command does not affect more than one command
-- #check triple

-- Open a namespace for the rest of the file
open NewNamespace
#check triple
#check triple

-- ## if let

inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph (a: Inline) : Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none

def Inline.string?2 (inline : Inline) : Option String :=
  open Inline in
  if let string s := inline then
    some s
  else none

-- ## Positional structure arguments

#eval (⟨1, 2⟩ : Nat × Nat)

structure Point where
  mkPoint ::
  x : Nat
  y : Nat
deriving Repr
#eval (⟨3, 4⟩ : Point)
#eval (Point.mkPoint 3 2)

-- Can pattern matching be used on structures?
def productOfPoint : Point → Nat
  | { x, y } => x * y
#eval productOfPoint (Point.mkPoint 3 4)

-- ## String interpolation

#eval s!"three fives is {NewNamespace.triple 5}"
#eval s!"My point: {Repr.reprPrec (⟨5, 3⟩ : Point) 0}"

-- # Examples

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

#eval NonTail.sum [1, 2, 3]

def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

#eval Tail.sum [1, 2, 3]

-- ## Reversing lists

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs

-- ## Multiple recursive calls

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
deriving Repr

instance [Repr α] : ToString (BinTree α) where
  toString x := s!"{Repr.reprPrec x 0}"

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

-- # Practice

-- ## Trying continuation passing style

-- This is probably not true continuation passing style because the continuation
-- is only passed the base case result, and remains the same across all
-- recursive calls.

def Cps.reverseHelper (c : List α → β) (soFar : List α) : List α → β
  | [] => (c soFar)
  | x :: xs => reverseHelper c (x :: soFar) xs

def Cps.reverse (c : List α → β) (xs : List α) : β :=
  reverseHelper c [] xs

def printResult [ToString α] (f : (α → (IO PUnit)) → α → (IO PUnit)) (x : α) : IO PUnit :=
  f (fun result => do
    (← IO.getStdout).putStrLn (ToString.toString result))
    x

#eval printResult Cps.reverse [1, 2, 3]

-- Genuine continuation-passing style
-- Reference: https://sites.ualberta.ca/~jhoover/325/CourseNotes/section/Continuations.htm

def Cps.reverse2 (c : List α → β) (x : List α) : β :=
  match x with
  | [] => c []
  | y :: ys => reverse2 (fun (result : List α) =>
    c (result ++ [y]))
    ys
-- Technically, this is tail-recursive, but it still uses memory proportional to
-- the length of the list. It accumulates state in Lambda function bindings on
-- the heap instead of accumulating state on the stack. It might be better than
-- normal recursion if the heap has more space than the stack.

#eval printResult Cps.reverse2 [1, 2, 3]

def Cps.mirror (c : BinTree α → β) (x : BinTree α) : β :=
  match x with
  | .leaf => c .leaf
  | .branch l x r => mirror (fun (lResult : BinTree α) =>
      mirror (fun (rResult : BinTree α) =>
        c (.branch rResult x lResult)
      )
      r
    )
    l

#eval printResult Cps.mirror (.leaf : BinTree Nat)
#eval printResult Cps.mirror (.branch .leaf 0 .leaf)
#eval printResult Cps.mirror (.branch (.branch .leaf 1 .leaf) 0 .leaf)
#eval printResult Cps.mirror (.branch (.branch .leaf 1 .leaf) 0 (.branch .leaf 2 .leaf))
#eval printResult Cps.mirror (.branch (.branch (.branch .leaf 3 .leaf) 1 .leaf) 0 (.branch .leaf 2 .leaf))

-- # Exercises

def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1

def Tail.lengthHelper (soFar : Nat) : List α → Nat
  | [] => soFar
  | _ :: xs => lengthHelper (soFar + 1) xs

def Tail.length (x : List α) : Nat :=
  lengthHelper 0 x

#eval Tail.length [1, 2, 3, 4]

def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)

def Tail.factorialHelper (soFar : Nat) : Nat → Nat
  | 0 => soFar
  | n + 1 => factorialHelper (soFar * (n + 1)) n

def Tail.factorial (x : Nat) : Nat :=
  factorialHelper 1 x

#eval [0, 1, 2, 3, 4].map Tail.factorial

def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs

def Tail.filterHelper (soFar : List α) (p : α → Bool) : List α → List α
  | [] => soFar
  | x :: xs =>
    if p x then
      filterHelper (x :: soFar) p xs
    else
      filterHelper soFar p xs

def Tail.filter (p : α → Bool) (xs : List α) : List α :=
  Tail.reverse (filterHelper [] p xs)

#eval Tail.filter (· % 2 == 0) [0, 1, 2, 3, 4]

def Cps.filter (c : List α → β) (p : α → Bool) : List α → β
  | [] => c []
  | x :: xs => filter (fun result =>
      if p x then
        c (x :: result)
      else
        c result) p xs

#eval printResult
  (fun c xs => Cps.filter c (· % 2 == 0) xs)
  [0, 1, 2, 3, 4]

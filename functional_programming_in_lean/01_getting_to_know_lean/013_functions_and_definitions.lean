-- # Examples

def hello := "Hello"

-- Type annotations
def lean: String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else
    n

#eval maximum (5 + 8) (2 * 7)
#eval maximum 13 14
def curry_maximum_with_7 : Nat → Nat := maximum 7
#eval curry_maximum_with_7 8
#eval curry_maximum_with_7 6

#check add1
#check (add1)
#check maximum
#check (maximum)
#check curry_maximum_with_7
#check maximum 4

def Str : Type := String
def aStr : Str := "This is a string"

def NaturalNumber : Type := Nat
-- set_option diagnostics true
-- def thirtyEight : NaturalNumber := 38
def thirtyEight : NaturalNumber := (38 : Nat)
-- NaturalNumber is missing an overloading for number literals.
abbrev N : Type := Nat
-- abbrev allows N to be replaced with its definition before overload resolution
def thirtyNine : N := 39

-- # Exercises

def joinStringsWith (s1 s2 s3 : String) : String :=
  String.append s2 (String.append s1 s3)
#check joinStringsWith
#check (joinStringsWith)
#eval joinStringsWith ", " "one" "and another"
-- joinStringsWith ": " has type String -> String -> String
#check joinStringsWith ": "

def volume (w h d : Nat) : Nat :=
  w * h * d
#eval volume 2 3 4

-- # Practice

-- abbrev works for functions, too
abbrev subtract1 (x : Int) : Int :=
  x - 1

#check subtract1
#eval subtract1 0

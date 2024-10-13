-- # Examples

#eval (1 + 2 : Nat)

-- Natural numbers have arbitrary precision so underflow is not possible.
-- Situations where underflow would occur in C produce zero in Lean.
#eval 1 - 2
#eval (1 - 2: Int)

-- Check the type of an expression without evaluating it
#check 1 - 2
#check (1 - 2: Int)

-- A program that cannot be given a type
-- #check String.append "hello" [" ", "world"]

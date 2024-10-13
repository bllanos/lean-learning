-- # Examples

#eval 1 + 2

#eval 1 + 2 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

-- #eval String.append "it is "
-- The result of this expression is not of the Repr type,
-- so it cannot be displayed.
-- The result of the expression is a function, because of currying.

-- # Exercises

-- 42 + 19 = 61
#eval 42 + 19

-- String.append "A" (String.append "B", "C") = "ABC"
#eval String.append "A" (String.append "B" "C")

-- String.append (String.append "A" "B") "C" = "ABC"
-- String concatenation is associative
#eval String.append (String.append "A" "B") "C"

-- if 3 == 3 then 5 else 7 = 5
#eval if 3 == 3 then 5 else 7

-- if 3 == 4 then "equal" else "not equal" = "not equal"
#eval if 3 == 4 then "equal" else "not equal"

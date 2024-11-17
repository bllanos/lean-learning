def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval (twice (IO.println "shy"))

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure () -- empty action
  | n + 1 => do
    action
    nTimes action n

#eval nTimes (IO.println "fish") 3
#check (nTimes (IO.println "fish") 3)

def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n
#check (countdown 4)
def from5 : List (IO Unit) := countdown 5
#eval from5.length

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

def main2 : IO Unit := runActions from5
#eval main2

-- # Practice

-- Pure.pure.{u, v} {f : Type u → Type v} [self : Pure f] {α : Type u} : α → f α
#check pure ()
def f {_α : Type 0} : Type 0 :=
  Int
-- #check (pure {u := 0} {v := 0} {f := f} {α := Bool} true)

-- # Exercises

def main : IO Unit := do
  -- Evaluates to an IO action value
  let englishGreeting := IO.println "Hello!"
  -- IO action whose result is not bound to any variable
  IO.println "Bonjour!"
  -- IO action whose result is not bound to any variable
  englishGreeting

-- Evaluate expression:
-- do
--   let englishGreeting := IO.println "Hello!"
--   IO.println "Bonjour!"
--   englishGreeting

-- Evaluate expression:
-- do
--   IO.println "Bonjour!"
--   IO.println "Hello!"

-- Execute action
--   Bonjour!
--   IO.println "Hello!"

-- Execute action
--   Bonjour!
--   Hello!

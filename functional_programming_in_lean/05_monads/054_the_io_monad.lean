-- # Examples

#print Nat
#print "test"
def x := 0
#print x

#print Char.isAlpha

#print List.isEmpty

#print IO
#print IO.Error
#print EIO
#print IO.RealWorld
#print EStateM
#print EStateM.Result
#print EStateM.pure
#print EStateM.bind

-- # Practice

def printTest : IO Unit := do
  (← IO.getStdout).putStrLn "Testing"

#eval printTest

def printTest2 : IO Unit :=
  IO.getStdout >>= fun stdout =>
  stdout.putStrLn "Testing"

#eval printTest2

def printTest3 : IO Unit :=
  bind IO.getStdout fun stdout =>
    stdout.putStrLn "Testing"

#eval printTest3

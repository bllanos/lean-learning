-- ## Nested actions

def bufsize : USize := 20 * 1024 -- 20 KiB

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    -- Nested action
    (← IO.getStdout).write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

def test : IO Unit := do
  let a : Nat ← do if (← getNumA) == 5 then pure (0 : Nat) else getNumB
  (← IO.getStdout).putStrLn s!"The answer is {a}"

#eval test

-- ## Flexible layouts for `do`

-- This version uses only whitespace sensitive layout
def doSomething : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}!"

-- This version is as explicit as possible
def doSomething2 : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;

  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trim;
  stdout.putStrLn s!"Hello, {name}!"
}

-- This version uses a semicolon to put two actions on the same line
def doSomething3 : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trim
  stdout.putStrLn s!"Hello, {name}"

-- ## Running IO Actions with `#eval`

def makeFile : IO Unit := do
  -- The current working directory is the directory containing the Lakefile
  let handle ← IO.FS.Handle.mk "test.txt" IO.FS.Mode.write
  handle.putStrLn "created file"
  pure ()

-- Executes side effects
-- #eval (makeFile)

def printTest : IO Unit := do
  (← IO.getStdout).putStrLn "Testing"

#eval printTest

import doug.config

namespace Doug

structure ParsedArgs where
  startingDirectory : Option String := none
  config: Config := {}

structure FoundArgs where
  showHiddenFiles : Bool := false
  useASCII : Bool := false
  startingDirectory: Bool := false

def usage : String :=
  "Usage : doug [--ascii -a DIRECTORY]
Options:
\t--ascii\tUse ASCII characters to display the directory structure
\t-a\tShow hidden files
\tDIRECTORY\tStart of the filesystem hierarchy to output"

def matchArg (str: String) : StateT (FoundArgs × ParsedArgs) (Except String) Unit := do
  -- I think `modify` would be simpler than using a local mutable variable with `get` and `set`
  let mut (foundArgs, parsedArgs) ← get
  match str with
  | "--ascii" =>
    if foundArgs.useASCII then
      throw s!"duplicate argument \"--ascii\""
    else
      (foundArgs, parsedArgs) := ({foundArgs with useASCII := true }, { parsedArgs with config := { parsedArgs.config with useASCII := true } })
  | "-a" =>
    if foundArgs.showHiddenFiles then
      throw s!"duplicate argument \"-a\""
    else
      (foundArgs, parsedArgs) := ({foundArgs with showHiddenFiles := true }, { parsedArgs with config := { parsedArgs.config with showHiddenFiles := true } })
  | arg =>
    if foundArgs.startingDirectory then
      throw s!"expected at most one non-named (i.e. positional) argument, providing the starting directory"
    else
      (foundArgs, parsedArgs) := ({foundArgs with startingDirectory := true }, { parsedArgs with startingDirectory := arg })
  set (foundArgs, parsedArgs)

-- This function will stop validation at the first invalid argument
def parseArgs (args : List String) : Except String ParsedArgs := do
  let mut parserState := ({}, {})
  for arg in args do
    parserState := (← (matchArg arg parserState)).snd
  return parserState.snd

end Doug

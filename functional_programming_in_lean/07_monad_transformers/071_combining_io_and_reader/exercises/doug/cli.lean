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

def matchArg : (FoundArgs × ParsedArgs) → String → Except String (FoundArgs × ParsedArgs)
      | (foundArgs, parsedArgs), "--ascii" =>
        if foundArgs.useASCII then
          Except.error s!"duplicate argument \"--ascii\""
        else
          Except.ok ({foundArgs with useASCII := true }, { parsedArgs with config := { parsedArgs.config with useASCII := true } })
      | (foundArgs, parsedArgs), "-a" =>
        if foundArgs.showHiddenFiles then
          Except.error s!"duplicate argument \"-a\""
        else
          Except.ok ({foundArgs with showHiddenFiles := true }, { parsedArgs with config := { parsedArgs.config with showHiddenFiles := true } })
      | (foundArgs, parsedArgs), arg =>
        if foundArgs.startingDirectory then
          Except.error s!"expected at most one non-named (i.e. positional) argument, providing the starting directory"
        else
          Except.ok ({foundArgs with startingDirectory := true }, { parsedArgs with startingDirectory := arg })

-- This function will stop validation at the first invalid argument
def parseArgs (args : List String) : Except String ParsedArgs :=
  Prod.snd <$> (args.foldlM matchArg ({}, {}))

end Doug

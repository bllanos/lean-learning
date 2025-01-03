import doug.config

namespace Doug

def usage : String :=
  "Usage : doug [--ascii -a]
Options:
\t--ascii\tUse ASCII characters to display the directory structure
\t-a\tShow hidden files"

def matchArg (cfg : Config) : String → Except String Config
    | "--ascii" => Except.ok { cfg with useASCII := true }
    | "-a" => Except.ok { cfg with showHiddenFiles := true }
    | arg => Except.error s!"unrecognized argument \"{arg}\""

-- This function does not detect duplicate valid arguments
-- and will stop validation at the first invalid argument
def configFromArgs (args : List String) : Except String Config :=
  args.foldlM matchArg {}

end Doug

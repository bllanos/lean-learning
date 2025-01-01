import doug.config

namespace Doug

def usage : String :=
  "Usage : doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs : List String → Option Config
  | [] => some {} -- both fields default
  | ["--ascii"] => some { useASCII := true }
  | _ => none

end Doug

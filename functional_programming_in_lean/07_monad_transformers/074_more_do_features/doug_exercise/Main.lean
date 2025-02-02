import doug

def getStartingDirectory (parsedArgs : Doug.ParsedArgs): IO System.FilePath :=
  match parsedArgs.startingDirectory with
  | some directory => pure directory
  | none => IO.currentDir

def main (args : List String) : IO UInt32 := do
  match Doug.parseArgs args with
  | Except.ok parsedArgs =>
    let startingDirectory ← getStartingDirectory parsedArgs
    if (← startingDirectory.pathExists) then
      Doug.runDirTreeWithConfig startingDirectory parsedArgs.config
      return 0
    else
      IO.eprintln s!"The starting path argument \"{startingDirectory}\" does not exist."
      return 1
  | Except.error err =>
    IO.eprintln err
    IO.eprintln Doug.usage
    return 1

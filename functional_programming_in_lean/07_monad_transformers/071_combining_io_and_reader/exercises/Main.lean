import doug

def main (args : List String) : IO UInt32 := do
  match Doug.parseArgs args with
  | Except.ok parsedArgs =>
    let startingDirectory := (Coe.coe <$> parsedArgs.startingDirectory).getD (← IO.currentDir)
    if (← startingDirectory.pathExists) then
      (Doug.dirTree startingDirectory).run parsedArgs.config
      pure 0
    else
      IO.eprintln s!"The starting path argument \"{startingDirectory}\" does not exist."
      pure 1
  | Except.error err =>
    IO.eprintln err
    IO.eprintln Doug.usage
    pure 1

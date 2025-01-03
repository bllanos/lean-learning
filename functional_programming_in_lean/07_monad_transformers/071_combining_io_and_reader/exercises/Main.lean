import doug

def main (args : List String) : IO UInt32 := do
  match Doug.configFromArgs args with
  | Except.ok config =>
    (Doug.dirTree (← IO.currentDir)).run config
    pure 0
  | Except.error err =>
    IO.eprintln err
    IO.eprintln Doug.usage
    pure 1

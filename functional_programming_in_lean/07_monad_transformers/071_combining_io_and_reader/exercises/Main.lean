import doug

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

def main (args : List String) : IO UInt32 := do
  match Doug.configFromArgs args with
  | some config =>
    (Doug.dirTree (← IO.currentDir)).run config
    pure 0
  | none =>
    IO.eprintln s!"Didn't understand argument(s) {" ".separate args}"
    IO.eprintln Doug.usage
    pure 1

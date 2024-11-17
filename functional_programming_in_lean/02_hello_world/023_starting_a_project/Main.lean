import Greeting
import Greeting.Smile

open Expression (expression expression2)

def main : IO Unit := do
  IO.println s!"Hello, {hello}, with {expression}!"
  IO.println s!"Hello, {hello}, with {expression2}!"

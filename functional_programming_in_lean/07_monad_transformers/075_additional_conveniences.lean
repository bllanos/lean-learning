-- # Examples

-- ## Pipe operators

-- `E1 |> E2` is `E2 E1`
-- `E1 <| E2` is `E1 E2`

#eval some 5 |> toString

def times3 (n : Nat) : Nat := n * 3

#eval 5 |> times3 |> toString |> ("It is " ++ ·)
#eval 5 |> times3 |> toString |> (s!"It is {·}")

#eval (s!"It is {·}") <| toString <| times3 <| 5

#eval ([1, 2, 3].reverse.drop 1).reverse
#eval [1, 2, 3] |> List.reverse |> List.drop 1 |> List.reverse
#eval List.reverse <| List.drop 1 <| List.reverse <| [1, 2, 3]
#eval List.reverse <| (List.drop <| 1) <| List.reverse <| [1, 2, 3]

-- Pipeline dot operator
#eval [1, 2, 3] |>.reverse |>.drop 1 |>.reverse
#eval List.reverse <| .drop 1 <| .reverse <| [1, 2, 3]

-- ## Infinite loops

def spam : IO Unit := do
  repeat IO.println "Spam!"

def bufsize : USize := 20 * 1024
partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

partial def dump2 (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  repeat do
    let buf ← stream.read bufsize
    -- This version would loop indefinitely even if the stream is empty:
    --   unless buf.isEmpty do
    --     stdout.write buf
    if buf.isEmpty then break
    stdout.write buf

-- ## While loops

def dump3 (stream : IO.FS.Stream) : IO Unit := do
  let stdout ← IO.getStdout
  let mut buf ← stream.read bufsize
  while not buf.isEmpty do
    stdout.write buf
    buf ← stream.read bufsize

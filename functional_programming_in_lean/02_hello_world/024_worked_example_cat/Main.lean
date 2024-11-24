def bufsize : USize := 20 * 1024 -- 20 KiB

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  -- Without the file existence check, the program will terminate
  -- with an uncaught exception:
  -- """
  -- uncaught exception: no such file or directory (error code: 2)
  --   file: $FILENAME
  -- """
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def help (outStream : IO.FS.Stream) : IO Unit := do
  outStream.putStrLn "\
    Usage: feline [FILE]...
  Concatenate FILE(s) to standard output.
  With no FILE, or when FILE is -, read standard input.\
"

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "--help" :: args =>
    let stdout ← IO.getStdout
    help stdout
    process exitCode args
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  -- This would only support `--help` as the only argument
  -- | ["--help"] => do
  | _ => process 0 args

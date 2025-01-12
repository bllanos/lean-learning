import doug.config

namespace Doug

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : ConfigIO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))
  | some "." | some ".." => pure none
  | some name =>
    if (← read).shouldShowName name then
      pure (some (if (← path.isDir) then .dir name else .file name))
    else
      pure none

def showFileName (file : String) : ConfigIO Unit := do
  let cfg ← read
  IO.println (cfg.fileName file)

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println ((← read).dirName dir)

def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action

partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    withReader Config.inDirectory (doList contents.toList fun d =>
      dirTree d.path)

end Doug

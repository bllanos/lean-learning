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

structure EntryCounts where
  files: Nat := 0
  directories: Nat := 0

def EntryCounts.report (counts: EntryCounts) : String :=
  s!"{counts.files} files, {counts.directories} directories"

def countEntry (entry: Option Entry) (counts : EntryCounts) : EntryCounts :=
  match entry with
  | none => counts
  | some (.file _) => { counts with files := counts.files + 1 }
  | some (.dir _) => { counts with directories := counts.directories + 1 }

partial def dirTree (path : System.FilePath) : StateT EntryCounts ConfigIO Unit := do
  let entry ← toEntry path
  modify (countEntry entry)
  match entry with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    withReader Config.inDirectory (
        for d in contents do
          dirTree d.path
      )

partial def runDirTreeWithConfig (path : System.FilePath) (config : Config) : IO Unit := do
  let results ← (dirTree path).run {} config
  IO.println s!"Viewed {results.snd.report}"

end Doug

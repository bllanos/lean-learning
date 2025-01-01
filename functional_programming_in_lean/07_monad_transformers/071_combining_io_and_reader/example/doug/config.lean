namespace Doug

structure Config where
  useASCII : Bool := false
  currentPrefix : String := ""

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preDir} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix }

abbrev ConfigIO (α : Type) : Type :=
  ReaderT Config IO α

-- def read [Monad m] : ReaderT ρ m ρ :=
--   fun env => pure env

-- class MonadReader (ρ : outParam (Type u)) (m : Type u → Type v) : Type (max (u+1) v) where
--   read : m ρ

-- instance [Monad m] : MonadReader ρ (ReaderT ρ m) where
--   read := fun env => pure env

-- export MonadReader (read)

-- instance [Monad m] : Monad (ReaderT ρ m) where
--   pure x := fun _ => pure x
--   bind result next := fun env => do
--     let v ← result env
--     next v env

-- class MonadLift (m : Type u → Type v) (n : Type u → Type w) where
--   monadLift : {α : Type u} → m α → n α

-- instance : MonadLift m (ReaderT ρ m) where
--   monadLift action := fun _ => action

-- class MonadWithReader (ρ : outParam (Type u)) (m : Type u → Type v) where
--   withReader {α : Type u} : (ρ → ρ) → m α → m α

-- export MonadWithReader (withReader)

-- instance : MonadWithReader ρ (ReaderT ρ m) where
--   withReader change action :=
--     fun cfg => action (change cfg)

end Doug

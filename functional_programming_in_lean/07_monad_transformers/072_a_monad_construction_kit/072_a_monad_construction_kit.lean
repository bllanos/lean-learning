-- # Examples

#check MonadLift

-- ## Failure with OptionT

def OptionT2 (m : Type u → Type v) (α : Type u) : Type v :=
  m (Option α)

def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    failure
  else pure trimmed

def getSomeInput2 : IO (Option String) := do
  let input : String ← (← IO.getStdin).getLine
  let trimmed := input.trim
  if trimmed == "" then
    pure none
  else pure trimmed

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favourite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favourite beetle is {beetle}."

-- ### The Monad instance

-- instance [Monad m] : Monad (OptionT2 m) where
--   pure x := pure (some x)
--   bind action next := do
--     match (← action) with
--     | none => pure none
--     | some v => next v

-- instance [Monad m] : Monad (OptionT2 m) where
--   pure x := (pure (some x) : m (Option _))
--   bind action next := (do
--     match (← action) with
--     | none => pure none
--     | some v => next v : m (Option _))

structure OptionT3 (m : Type u → Type v) (α : Type u) : Type v where
  run : m (Option α)

instance [Monad m] : Monad (OptionT3 m) where
  pure x := { run := pure (some x) }
  bind action next :=
    { run := do
      match (← action.run) with
      | none => pure none
      | some v => (next v).run }

def OptionT2.mk (x : m (Option α)) : OptionT m α := x
def OptionT2.run (x : OptionT2 m α) : m (Option α) := x

instance [Monad m] : Monad (OptionT2 m) where
  pure x := OptionT2.mk (pure (some x))
  bind action next := OptionT2.mk (do
    match (← action) with
    | none => pure none
    | some v => next v)

-- ### An Alternative instance

instance [Monad m] : Alternative (OptionT2 m) where
  failure := OptionT2.mk (pure none)
  orElse x y := OptionT2.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()

-- ### Lifting

instance [Monad m] : MonadLift m (OptionT2 m) where
  monadLift action := OptionT2.mk do
    pure (some (← action))

-- ## Exceptions

def ExceptT2 (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Except ε α)

def ExceptT2.mk {ε α : Type u} (x : m (Except ε α)) : ExceptT2 ε m α := x

def ExceptT2.run {ε α : Type u} (x : ExceptT2 ε m α) : m (Except ε α) := x

instance {ε : Type u} {m : Type u → Type v} [Monad m] : Monad (ExceptT2 ε m) where
  pure x := ExceptT2.mk (pure (Except.ok x))
  bind result next := ExceptT2.mk do
    match ← result with
    | .error e => pure (.error e)
    | .ok x => next x

instance [Monad m] : MonadLift (Except ε) (ExceptT2 ε m) where
  monadLift action := ExceptT2.mk (pure action)

instance [Monad m] : MonadLift m (ExceptT2 ε m) where
  monadLift action := ExceptT2.mk (.ok <$> action)

-- ### Type classes for exceptions

class MonadExcept2 (ε : outParam (Type u)) (m : Type v → Type w) where
  throw : ε → m α
  tryCatch : m α → (ε → m α) → m α

inductive Err where
  | divByZero
  | notANumber : String → Err

def divBackend [Monad m] [MonadExcept Err m] (n k : Int) : m Int :=
  if k == 0 then
    throw .divByZero
  else pure (n / k)

def asNumber [Monad m] [MonadExcept Err m] (s : String) : m Int :=
  match s.toInt? with
  | none => throw (.notANumber s)
  | some i => pure i

def divFrontend [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  tryCatch (do pure (toString (← divBackend (← asNumber n) (← asNumber k))))
    fun
      | .divByZero => pure "Division by zero!"
      | .notANumber s => pure s!"Not a number : \"{s}\""

def divFrontend2 [Monad m] [MonadExcept Err m] (n k : String) : m String :=
  try
    pure (toString (← divBackend (← asNumber n) (← asNumber k)))
  catch
    | .divByZero => pure "Division by zero!"
    | .notANumber s => pure s!"Not a number: \"{s}\""

-- ## State

def StateT2 (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
  σ → m (α × σ)

instance [Monad m] : Monad (StateT2 σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (x, s') ← (result s)
    next x s'

structure LetterCounts where
  vowels : Nat := 0
  consonants : Nat := 0
deriving Repr

inductive Err2 where
  | notALetter : Char → Err2
deriving Repr

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList

-- With type annotations
def countLetters2 (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) : StateT LetterCounts (Except Err2) Unit := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        ((if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else -- modified or non-English letter
            pure st
        else throw (.notALetter c)) : Except Err2 LetterCounts)
      -- I think if `Except Err2 LetterCounts` is an error,
      -- then the function lifts it to `StateT LetterCounts (Except Err2) Unit`,
      -- otherwise `set st'` below serves the same purpose as a monad lift?
      set st'
      loop cs
  loop str.toList

#eval countLetters "abc" {}
#eval countLetters "a1c" {}

def countLetters3 (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

-- With type annotations
def countLetters4 (str : String) : StateT LetterCounts (Except Err2) Unit :=
  let rec loop (chars : List Char) : StateT LetterCounts (Except Err2) Unit := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        ((if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else -- modified or non-English letter
          pure ()) : StateT LetterCounts (Except Err2) Unit)
      else throw (.notALetter c)
      loop cs
  loop str.toList

def modify2 [MonadState σ m] (f : σ → σ) : m Unit :=
  -- MonadState.modifyGet
  modifyGet fun s => ((), f s)

#check MonadState.modifyGet

class MonadState2 (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u+1) v) where
  get : m σ
  set : σ → m PUnit
  modifyGet : (σ → α × σ) → m α

-- ## Of classes and The functions

#check MonadState.get

-- # Exercises

-- ## Monad contract

-- ### OptionT

-- (pure v) >>= f = f v
-- Proof:
-- pure (some x) >>= f
-- match (some x) with
-- | none => pure none
-- | some v => f v
-- f x

-- v >>= pure = v
-- Proof:
-- match (← v) with
-- | none => pure none
-- | some x => pure x
-- match (← v) with
-- | none => v
-- | some x => pure (some x)
-- match (← v) with
-- | none => v
-- | some x => v
-- v

-- (v >>= f) >>= g = v >>= fun x => (f x >>= g)
-- Proof:
-- (v >>= f) >>= g is
-- match (← match (← v) with
-- | none => pure none
-- | some x => f x) with
--   | none => pure none
--   | some y => g y

-- v >>= fun x => (f x >>= g) is
-- match (← v) with
-- | none => pure none
-- | some x => (match (← f x) with
--   | none => pure none
--   | some y => g y)

-- An analysis of the possible execution paths shows that the
-- two expressions are equivalent.

-- monadLift (pure x) = pure x
-- Proof:
-- pure (some (← pure x)) = pure x
-- pure (some x) = pure x -- By definition of pure

-- monadLift (x >>= f) = (monadLift x) >>= fun y => monadLift (f y)
-- Proof:
-- pure (some (← (x >>= f))) = pure (some (← x)) >>= fun y => pure (some (← f y))
-- pure (some (← (x >>= f))) = pure (some (← x)) >>= fun y => pure (some (← f y))
-- pure (some (← (x >>= f))) = (fun y => pure (some (← f y))) (← x)
-- pure (some (← (x >>= f))) = pure (some (← f (← x)))
-- (← (x >>= f)) = (← f (← x))
-- (← (x >>= f)) = (← (x >>= fun y => f y))
-- (← (x >>= f)) = (← (x >>= f))

-- ## Logging transformer

--- ### Logging monad

structure WithLog (logged : Type u) (α : Type v) : Type (max u v) where
  log : List logged
  val : α

instance : Monad (WithLog logged) where
  pure x := { log := [], val := x }
  bind result next :=
    let { log := resultLog, val := resultVal } := result
    let { log := nextLog, val := nextVal } := next resultVal
    { log := resultLog ++ nextLog, val := nextVal }

def WithLog.save (data : α) : WithLog α PUnit :=
  { log := [data], val := () }

def WithLog.get (x : WithLog logged α) : WithLog logged (List logged) :=
  { log := x.log, val := x.log }

instance [ToString logged] [ToString α] : ToString (WithLog logged α) where
  toString x := s!"Result: {x.val}\nLog: {x.log}"

--- ### Logging monad transformer

-- This version is incorrect because it cannot accumulate logs in `bind`.
-- It would seem like putting the log around the monad instead of inside
-- would prevent the log from being short-circuited by the monad, but I don't
-- think this is the case.
--
-- def WithLogT (logged : Type w) (m : Type u → Type v) (α : Type u) : Type (max w v) :=
--   WithLog logged (m α)

-- instance (logged : Type u) [Monad m] : Monad (WithLogT logged m) where
--   pure x := { log := [], val := pure x }
--   bind result next :=
--     let { log := resultLog, val := resultVal } := result
--     let nextVal := bind resultVal fun x =>
--       let { log := nextLog, val := nextVal } := next x
--       nextVal
--     { log := resultLog, val := nextVal }

def WithLogT (logged : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (WithLog logged α)

-- Version with type annotations
-- instance {logged : Type u} {m : Type u → Type v} [Monad m] : Monad (WithLogT logged m) where
--   pure x := (pure { log := [], val := x } : m (WithLog _ _))
--   bind {α β : Type u} (result : m (WithLog logged α)) (next : α → (m (WithLog logged β))) := ((bind result fun inner =>
--     let { log := resultLog, val := resultVal } := inner
--     (fun nextInner =>
--       let { log := nextLog, val := nextVal } := nextInner
--       { log := resultLog ++ nextLog, val := nextVal }
--     ) <$> (next resultVal)) : m (WithLog logged β))

def WithLogT.mk {logged : Type u} (x : m (WithLog logged α)) : WithLogT logged m α := x
def WithLogT.run {logged : Type u} (x : WithLogT logged m α) : m (WithLog logged α) := x

instance {logged : Type u} {m : Type u → Type v} [Monad m] : Monad (WithLogT logged m) where
  pure x := WithLogT.mk (pure { log := [], val := x })
  bind result next := WithLogT.mk ((bind result fun inner =>
    let { log := resultLog, val := resultVal } := inner
    (fun nextInner =>
      let { log := nextLog, val := nextVal } := nextInner
      { log := resultLog ++ nextLog, val := nextVal }
    ) <$> (next resultVal)))

instance {logged : Type u} [Monad m] : MonadLift (WithLog logged) (WithLogT logged m) where
  monadLift action := WithLogT.mk (pure action)

-- instance [Monad m] : MonadLift m (WithLogT logged m) where
--   monadLift action := WithLogT.mk (bind action fun x =>
--     pure (pure x))

instance [Monad m] : MonadLift m (WithLogT logged m) where
  monadLift action := WithLogT.mk (pure <$> action)

instance {logged : Type} {m : Type → Type}
  [Monad m] [ToString logged] [ToString (m String)] [ToString α] :
  ToString (WithLogT logged m α) where
    toString x := toString (toString <$> (WithLogT.run x))

-- ### Checking the monad transformer contract

-- (pure v) >>= f = f v
-- Proof:
-- (pure { log := [], val := v }) >>= f
-- (pure { log := [], val := v }) >>= (fun x => 'concat log in f x.val')
-- 'concat log in f v' -- By the monad contract for m
-- f v -- Concatenation does not change the log that f produced

-- v >>= pure = v
-- Proof:
-- v >>= (fun x => 'concat log in pure x.val')
-- v >>= id
-- v

-- (v >>= f) >>= g = v >>= fun x => (f x >>= g)
-- This should be true because concatenation is associative,
-- and because the monad parameter's bind operation is associative?

-- monadLift (pure x) = pure x
-- Proof:
-- pure <$> (pure x)
-- (fun x => { log := [], val := x }) <$> (pure x)
-- pure { log := [], val := x }
-- pure x

-- monadLift (x >>= f) = (monadLift x) >>= fun y => monadLift (f y)
-- Proof:
-- monadLift (x >>= f) is
-- (fun x => { log := [], val := x }) <$> (x >>= f)
-- bind ((fun x => { log := [], val := x }) <$> x) (fun y => ((fun x => { log := [], val := x }) <$> f y))
-- (monadLift x) >>= fun y => monadLift (f y)

-- ### A logging monad class

class MonadWithLog (logged : outParam (Type v)) (m : Type v → Type w) where
  save : logged → m PUnit
  get : m α → m (List logged)

instance : MonadWithLog logged (WithLog logged) where
  save := WithLog.save
  get := WithLog.get

instance [Monad m] : MonadWithLog logged (WithLogT logged m) where
  save data := WithLogT.mk (pure (WithLog.save data))
  get x := WithLogT.mk do
    pure (← x).get

class MonadWithLogOf (logged : Type v) (m : Type v → Type w) where
  save : logged → m PUnit
  get : m α → m (List logged)
  getThe : (logged : Type v) → m α → m (List logged)

-- The following fails to compile with the error:
--   """
--   cannot find synthesization order for instance @instMonadWithLogOfMonadWithLogOf with type
--     {logged : Type v} → {m : Type v → Type w} → [inst : MonadWithLogOf logged m] → MonadWithLog logged m
--   all remaining arguments have metavariables:
--     MonadWithLogOf ?logged m
--   """
-- instance {logged : Type v} {m : Type v → Type w} [MonadWithLogOf logged m] : MonadWithLog logged m where
--   save := MonadWithLogOf.save
--   get := MonadWithLogOf.get

-- ### A program that uses logging with exceptions

def find [Monad m] [MonadExcept String m] (x : Nat) : List Nat → WithLogT String m Unit
  | [] => do
    MonadWithLog.save s!"Reached empty list"
    (throw "Not found" : m Unit)
  | y :: ys => do
    MonadWithLog.save s!"Comparing {x} with {y}"
    if x == y then
      MonadWithLog.save s!"Found {x}"
    else
      find x ys

#eval (find 1 [5, 4, 3, 2, 1] : WithLogT String (Except String) Unit)
#eval (find 0 [5, 4, 3, 2, 1] : WithLogT String (Except String) Unit)

-- # Examples

-- ## Single-branched if

-- `else pure ()` is inserted automatically

structure LetterCounts where
  vowels : Nat := 0
  consonants : Nat := 0
deriving Repr

inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowels := "aeiouy"
  lowerVowels ++ lowerVowels.map (·.toUpper)

def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList

def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs

def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs

-- ## Early return

def List.find2? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find2? p xs

def List.find3? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find3? p xs

def runCatch [Monad m] (action: ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x

def List.find4? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find4? p xs)

def main2 (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  -- Notice the additional `do` keyword is just for `unless`,
  -- not for any different monadic context
  unless argv == [] do
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    return 1

  stdout.putStrLn "How would you like to be addressed?"
  stdout.flush

  let name := (← stdin.getLine).trim
  if name == "" then
    stderr.putStrLn s!"No name provided"
    return 1

  stdout.putStrLn s!"Hello, {name}!"

  return 0

def main3 (argv : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr

  if argv != [] then
    stderr.putStrLn s!"Expected no arguments, but got {argv.length}"
    pure 1
  else
    stdout.putStrLn "How would you like to be addressed?"
    stdout.flush

    let name := (← stdin.getLine).trim
    if name == "" then
      stderr.putStrLn s!"No name provided"
      pure 1
    else
      stdout.putStrLn s!"Hello, {name}!"
      pure 0

def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name

#eval greet "David"

-- ## Loops

-- ### Looping with ForM

-- γ : A collection
-- α : The type of element in the collection
class ForM2 (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
  forM [Monad m] : γ → (α → m PUnit) → m PUnit

def List.forM2 [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM2 xs action

instance : ForM2 m (List α) α where
  forM := List.forM2

def countLetters2 (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)

inductive Many (α : Type u) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do
    action first
    forM (rest ()) action

instance : ForM m (Many α) α where
  forM := Many.forM

structure AllLessThan where
  num : Nat

def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance : ForM m AllLessThan Nat where
  forM := AllLessThan.forM

#eval forM { num := 5 : AllLessThan } IO.println

structure LinesOf where
  stream : IO.FS.Stream

partial def LinesOf.forM (readFrom : LinesOf) (action : String → IO Unit) : IO Unit := do
  let line ← readFrom.stream.getLine
  if line == "" then return ()
  action line
  forM readFrom action

instance : ForM IO LinesOf String where
  forM := LinesOf.forM

def main4 (argv : List String) : IO UInt32 := do
  if argv != [] then
    IO.eprintln "Unexpected arguments"
    return 1

  forM (LinesOf.mk (← IO.getStdin)) fun line => do
    if line.any (·.isAlpha) then
      IO.print line

  return 0

-- ### Stopping iteration

def OptionT.exec2 [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()

def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec2 (forM nums fun i => do
    if i < 3 then failure else IO.println i)

#eval countToThree 7

instance : ForIn m AllLessThan Nat where
  forIn := ForM.forIn

def countToThree2 (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i

#eval countToThree2 7

def List.find5? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure

def List.find6? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure

-- Ranges

def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i

#eval fourToEight

def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4:8] do
    IO.println (x, y)

#eval parallelLoop

-- ## Mutable variables

def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x

#eval two

def two2 : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result

def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x

def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x

def List.count2 (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found

-- def List.count3 (p : α → Bool) (xs : List α) : Nat := Id.run do
--   let mut found := 0
--   let rec go : List α → Id Unit
--     | [] => pure ()
--     | y :: ys => do
--       if p y then found := found + 1
--       go ys
--   return found

-- I don't know how to explicitly qualify names from Init.Prelude without
-- Disabling the prelude import.
abbrev renameModify {σ : Type u} {m : Type u → Type v} [MonadState σ m] : (f : σ → σ) → m PUnit :=
  modify

def List.count3 (p : α → Bool) (xs : List α) : Nat := Id.run do
  let found := 0
  let rec go : List α → StateT Nat Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then
        renameModify (fun (found : Nat) => found + 1)
      go ys
  let (_, found) ← go xs found
  return found

#eval List.count3 (· % 2 == 0) [3, 5, 4, 6, 2, 1]

-- ## What counts as a do block?

example : Id Nat := do
  let mut x := 0
  x := x + 1
  return x

-- example : Id Unit := do
--   let mut x := 0
--   let other := do
--     x := x + 1
--   other

example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other

-- example : Id Unit := do
--   let mut x := 0
--   let addFour (y : Id Nat) := Id.run y + 4
--   addFour do
--     x := 5

example : Id Nat := do
  let mut x := 0
  do x := x + 1
  pure x

example : Id Nat := do
  let mut x := 0
  if x > 2 then
    x := x + 1
  return x

example : Id Nat := do
  let mut x := 0
  if x > 2 then do
    x := x + 1
  return x

example : Id Nat := do
  let mut x := 0
  match true with
  | true => x := x + 1
  | false => x := 17
  pure x

example : Id Nat := do
  let mut x := 0
  match true with
  | true => do
    x := x + 1
  | false => do
    x := 17
  pure x

example : Id Nat := do
  let mut x := 0
  for y in [1:5] do
    x := x + y
  return x

example : Id Nat := do
  let mut x := 0
  unless 1 < 5 do
    x := x + 1
  return x

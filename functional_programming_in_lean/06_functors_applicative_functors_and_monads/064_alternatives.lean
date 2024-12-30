-- # Examples

-- ## Recovery from failure

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
deriving Repr

instance : HAppend (NonEmptyList α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys : (NonEmptyList α) :=
    { head := xs.head, tail := xs.tail ++ (List.cons ys.head ys.tail) }

inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

instance : Applicative (Validate ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

abbrev NonEmptyString := {s : String // s ≠ ""}

inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String →
    LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString →
    LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

class OrElse2 (α : Type) where
  orElse : α → (Unit → α) → α

-- E1 <|> E2
-- is
-- OrElse.orElse E1 (fun () => E2)

instance : OrElse (Validate ε α) where
  orElse := Validate.orElse

def Field := String

def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }

def checkThat (condition : Bool) (field : Field) (msg : String) : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg

structure RawInput where
  name : String
  birthYear : String

def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def checkCompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  pure (fun () name => .company name) <*>
    checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" <*>
    checkName input.name

-- E1 *> E2
-- means
-- SeqRight.seqRight E1 (fun () => E2)

class SeqRight2 (f : Type → Type) extends Applicative f where
  seqRight {α β : Type} (a : f α) (b : Unit → f β) :=
    pure (fun _ x => x) <*> a <*> b ()

def checkCompany2 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  pure .company <*> checkName input.name

-- pure F <*> E = f <$> E

def checkCompany3 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε) : Validate ε {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors { head := err, tail := [] }

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trim.toNat? with
  | none => reportError "birth year" "Must be digits"
  | some n => pure n

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

-- Can I get validation errors from both fields?
def checkHumanAfter1970_2 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  .humanAfter1970 <$>
      ((checkYearIsNat input.birthYear).andThen fun y =>
        checkSubtype y (· > 1970) ("birth year", "greater than 1970")) <*>
      checkName input.name

#eval checkHumanAfter1970 ⟨"", "xs"⟩
#eval checkHumanAfter1970_2 ⟨"", "xs"⟩
#eval checkHumanAfter1970_2 ⟨"Test", "1971"⟩

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  .humanBefore1970 <$>
      ((checkYearIsNat input.birthYear).andThen fun y =>
        checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970")) <*>
      pure input.name

def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkCompany3 input <|> checkHumanBefore1970 input <|> checkHumanAfter1970_2 input

#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩

-- ## The Alternative class

class Alternative2 (f : Type → Type) extends Applicative f where
  failure : f α
  orElse : f α → (Unit → f α) → f α

-- instance [Alternative f] : OrElse (f α) where
--   orElse := Alternative.orElse

instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, y => y ()

inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α

def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)

def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.map (f : α → β) : Many α → Many β
    | .none => .none
    | .more y ys => Many.more (f y) (fun () => map f (ys ()))

instance : Functor Many where
  map := Many.map

-- It would be good to check if this is equivalent to the default
-- implementation provided by Monad.
def Many.seq (f : Many (α → β)) (x : Unit → Many α) : Many β :=
  match f with
  | .none => .none
  | .more g gs =>
    match x () with
    | .none => .none
    | .more y ys =>
      .union (g <$> .more y ys) (seq (gs ()) (fun () => .more y ys))

instance : Applicative Many where
  pure x := Many.more x (fun () => Many.none)
  seq := Many.seq

instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

def guard2 [Alternative f] (p : Prop) [Decidable p] : f Unit :=
  if p then
    pure ()
  else failure

def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)

def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ => Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)

instance : Monad Many where
  pure x := Many.more x (fun () => Many.none)
  bind := Many.bind

def evenDivisors (n : Nat) : Many Nat := do
  let k ← Many.countdown (n + 1)
  guard (k % 2 = 0)
  guard (n % k = 0)
  pure k

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

#eval (evenDivisors 20).takeAll

-- ## Exercises

-- ### Improve validation friendliness

-- Part 1

inductive Validate2 (ε α : Type) : Type where
  | ok : α → Validate2 ε α
  | errors : ε → Validate2 ε α
deriving Repr

instance : Functor (Validate2 ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs

instance {ε : Type} [Append ε] : Applicative (Validate2 ε) where
  pure := .ok
  seq f x :=
    match f with
    | .ok g => g <$> (x ())
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Validate2.orElse {ε : Type} [Append ε] (a : Validate2 ε α) (b : Unit → Validate2 ε α) : Validate2 ε α :=
  match a with
  | .ok x => .ok x
  | .errors errs1 =>
    match b () with
    | .ok x => .ok x
    | .errors errs2 => .errors (errs1 ++ errs2)

instance {ε : Type} [Append ε] : OrElse (Validate2 ε α) where
  orElse := Validate2.orElse

-- Part 2

def Validate2.mapErrors : Validate2 ε α → (ε → ε') → Validate2 ε' α
  | .ok x, _ => .ok x
  | .errors errs, f => .errors (f errs)

-- Part 3

inductive TreeError where
  | field : Field → String → TreeError
  | path : String → TreeError → TreeError
  | both : TreeError → TreeError → TreeError

instance : Append TreeError where
  append := .both

def reportError2 {α : Type} (field : Field) (msg : String) : Validate2 TreeError α :=
  .errors (TreeError.field field msg)

def checkThat2 (condition : Bool) (field : Field) (msg : String) : Validate2 TreeError Unit :=
  if condition then pure () else reportError2 field msg

def checkName2 (name : String) : Validate2 TreeError {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError2 (α := {n : String // n ≠ ""}) "name" "Required"
  else pure ⟨name, h⟩

def checkSubtype2 {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (field : Field) (msg : String) : Validate2 TreeError {x : α // p x} :=
  if h : p v then
    pure ⟨v, h⟩
  else
    .errors (TreeError.field field msg)

def Validate2.andThen (val : Validate2 ε α) (next : α → Validate2 ε β) : Validate2 ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x

def checkYearIsNat2 (year : String) : Validate2 TreeError Nat :=
  match year.trim.toNat? with
  | none => reportError2 (α := Nat) "birth year" "Must be digits"
  | some n => pure n

def addErrorPath (path : String) (err: TreeError) : TreeError :=
  TreeError.path path err

def checkCompany4 (input : RawInput) : Validate2 TreeError LegacyCheckedInput :=
  (checkThat2 (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName2 input.name).mapErrors (addErrorPath "company")

def checkHumanAfter1970_3 (input : RawInput) : Validate2 TreeError LegacyCheckedInput :=
  (.humanAfter1970 <$>
      ((checkYearIsNat2 input.birthYear).andThen fun y =>
        checkSubtype2 y (· > 1970) "birth year" "greater than 1970") <*>
      checkName2 input.name).mapErrors (addErrorPath "humanAfter1970")

def checkHumanBefore1970_2 (input : RawInput) : Validate2 TreeError LegacyCheckedInput :=
  (.humanBefore1970 <$>
      ((checkYearIsNat2 input.birthYear).andThen fun y =>
        checkSubtype2 y (fun x => x > 999 ∧ x < 1970) "birth year" "less than 1970") <*>
      pure input.name).mapErrors (addErrorPath "humanBefore1970")

def checkLegacyInput2 (input : RawInput) : Validate2 TreeError LegacyCheckedInput :=
  checkCompany4 input <|> checkHumanBefore1970_2 input <|> checkHumanAfter1970_3 input

-- Part 4

instance : ToString Field where
  toString field := field

def report : TreeError → String
  | TreeError.both l r =>
    s!"{(report l)}, {(report r)}"
  | TreeError.field field msg =>
    s!"(field {field}: {msg})"
  | TreeError.path path err =>
    s!"(trying {path}: {(report err)})"

def checkAndReportLegacyInput (input : RawInput) : Validate2 String LegacyCheckedInput :=
  (checkCompany4 input <|> checkHumanBefore1970_2 input <|> checkHumanAfter1970_3 input).mapErrors report

#eval checkAndReportLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkAndReportLegacyInput ⟨"Johnny", "1963"⟩
#eval checkAndReportLegacyInput ⟨"", "1963"⟩
#eval checkAndReportLegacyInput ⟨"", "1970"⟩

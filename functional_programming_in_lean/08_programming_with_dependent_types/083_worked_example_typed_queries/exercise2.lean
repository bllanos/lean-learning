-- # Examples

inductive DBType where
  | int | string | bool

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool

#eval ("Mount Hood" : DBType.string.asType)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int | .string | .bool => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
    | .int, .int | .string, .string | .bool, .bool => true
    | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int | .string | .bool => reprPrec

structure NDBType where
  underlying : DBType
  nullable : Bool
deriving BEq

abbrev NDBType.asType (t : NDBType) : Type :=
  if t.nullable then
    Option t.underlying.asType
  else
    t.underlying.asType

#check ({ underlying := DBType.int, nullable := false } : NDBType).asType
#check (some (1 : Int) : ({ underlying := DBType.int, nullable := true } : NDBType).asType)
#check ((1 : Int) : ({ underlying := DBType.int, nullable := false } : NDBType).asType)

def NDBType.beq (u : DBType) (n : Bool) (x y : ({ underlying := u, nullable := n } : NDBType).asType) : Bool :=
  match n with
  | true =>
    match u with
    | .int | .string | .bool => match x, y with
      | some x', some y' => x' == y'
      | none, none => true
      | _, _ => false
  | false =>
    let x' : u.asType := x
    let y' : u.asType := y
    x' == y'

instance {t : NDBType} : BEq t.asType where
  beq := NDBType.beq t.underlying t.nullable

-- Conforms to SQL null propagation rules
-- (https://www.postgresql.org/docs/current/functions-comparison.html)
def NDBType.nullableEq {u : DBType} {n1 : Bool} {n2 : Bool}
  (x : ({ underlying := u, nullable := n1 } : NDBType).asType) (y : ({ underlying := u, nullable := n2 } : NDBType).asType) :
  ({ underlying := .bool, nullable := n1 || n2 } : NDBType).asType :=
  match n1, n2 with
  | true, true =>
    match u with
    | .int | .string | .bool => match x, y with
      | some x', some y' => some (x' == y')
      | none, none => none
      | _, _ => none
  | true, false =>
    match u with
    | .int | .string | .bool => match x, y with
      | some x', y' => some (x' == y')
      | none, _ => none
  | false, true =>
    match u with
    | .int | .string | .bool => match x, y with
      | x', some y' => some (y' == x') -- For some reason, `x' == y'` does not type check
      | _, none => none
  | false, false =>
    let x' : u.asType := x
    let y' : u.asType := y
    x' == y'

def NDBType.nullableLessThan {n1 : Bool} {n2 : Bool}
  (x : ({ underlying := .int, nullable := n1 } : NDBType).asType) (y : ({ underlying := .int, nullable := n2 } : NDBType).asType) :
  ({ underlying := .bool, nullable := n1 || n2 } : NDBType).asType :=
  match n1, n2 with
  | true, true =>
    match x, y with
    | some x', some y' => some (x' < y')
    | none, none => none
    | _, _ => none
  | true, false =>
    match x, y with
      | some x', y' => some (x' < y')
      | none, _ => none
  | false, true =>
    match x, y with
      | x', some y' => some (y' > x') -- For some reason, `x' < y'` does not type check
      | _, none => none
  | false, false =>
    let x' : Int := x
    let y' : Int := y
    ((x' < y') : Bool)

def NDBType.nullableAnd {n1 : Bool} {n2 : Bool}
  (x : ({ underlying := .bool, nullable := n1 } : NDBType).asType) (y : ({ underlying := .bool, nullable := n2 } : NDBType).asType) :
  ({ underlying := .bool, nullable := n1 || n2 } : NDBType).asType :=
  match n1, n2 with
  | true, true =>
    match x, y with
    | some x', some y' => some (x' && y')
    | none, none => none
    | _, _ => none
  | true, false =>
    match x, y with
      | some x', y' => some (x' && y')
      | none, _ => none
  | false, true =>
    match x, y with
      | x', some y' => some (x' && y')
      | _, none => none
  | false, false =>
    let x' : Bool := x
    let y' : Bool := y
    x' && y'

def NDBType.nullableNot {n : Bool}
  (x : ({ underlying := .bool, nullable := n } : NDBType).asType) :
  ({ underlying := .bool, nullable := n } : NDBType).asType :=
  match n with
  | true =>
    match x with
    | some x' => some (not x')
    | none => none
  | false =>
    let x' : Bool := x
    not x'

def NDBType.reprPrecCustom (u : DBType) (n : Bool) (x : ({ underlying := u, nullable := n } : NDBType).asType) (prec : Nat) : Std.Format :=
  match n with
  | true =>
    match u with
    | .int | .string | .bool => match x with
      | some x' => reprPrec x' prec
      | none => reprPrec (none : Option u.asType) prec
  | false =>
    let x' : u.asType := x
    reprPrec x' prec

instance {t : NDBType} : Repr t.asType where
  reprPrec := NDBType.reprPrecCustom t.underlying t.nullable

instance : OfNat ({ underlying := DBType.int, nullable := false } : NDBType).asType n where
  ofNat := (n : Int)

instance : OfNat ({ underlying := DBType.int, nullable := true } : NDBType).asType n where
  ofNat := some (n : Int)

structure Column where
  name : String
  contains : NDBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema := [
  ⟨"name", ⟨DBType.string, false⟩⟩,
  ⟨"location", ⟨DBType.string, false⟩⟩,
  ⟨"elevation", ⟨DBType.int, false⟩⟩,
  ⟨"lastVisited", ⟨DBType.int, true⟩⟩
]

instance {s : String} : OfNat ({ name := s, contains := { underlying := DBType.int, nullable := false } } : Column).contains.asType n where
  ofNat := (n : Int)

instance {s : String} : OfNat ({ name := s, contains := { underlying := DBType.int, nullable := true } } : Column).contains.asType n where
  ofNat := some (n : Int)

def mountainDiary : Table peak := [
  ⟨"Mount Nebo", "USA", 3637, 2013⟩,
  ⟨"Moscow Mountain", "USA", 1519, 2015⟩,
  ⟨"Himmelbjerget", "Denmark", 147, 2004⟩,
  ⟨"Mount St. Helens", "USA", 2549, 2010⟩,
  ⟨"Fantasy Mountain", "USA", 3000, none⟩
]

abbrev waterfall : Schema := [
  ⟨"name", ⟨DBType.string, false⟩⟩,
  ⟨"location", ⟨DBType.string, false⟩⟩,
  ⟨"lastVisited", ⟨DBType.int, true⟩⟩
]

def waterfallDiary : Table waterfall := [
  ⟨"Multnomah Falls", "USA", 2018⟩,
  ⟨"Shoshone Falls", "USA", 2014⟩,
  ⟨"Fantasy Waterfall", "USA", none⟩
]

def Row.beq (r1 r2 : Row s) : Bool :=
  match s with
  | [] => true
  | [_] => r1 == r2
  | _::_::_ =>
    match r1, r2 with
    | (v1, r1'), (v2, r2') =>
      v1 == v2 && beq r1' r2'

instance : BEq (Row s) where
  beq := Row.beq

inductive HasCol : Schema → String → NDBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

example : HasCol peak "elevation" ⟨.int, false⟩ :=
  .there (.there .here)

example : HasCol peak "lastVisited" ⟨.int, true⟩ :=
  .there (.there (.there .here))

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

#eval mountainDiary[1].get (.there (.there .here) : HasCol peak "elevation" ⟨.int, false⟩)
#eval mountainDiary[3].get (.there (.there (.there .here)) : HasCol peak "lastVisited" ⟨.int, true⟩)

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
    HasCol bigger n t →
    Subschema smaller bigger →
    Subschema (⟨n, t⟩ :: smaller) bigger

abbrev travelDiary : Schema :=
  [⟨"name", ⟨.string, false⟩⟩, ⟨"location", ⟨.string, false⟩⟩, ⟨"lastVisited", ⟨.int, true⟩⟩]
abbrev travelDiary2 : Schema :=
  [⟨"name", ⟨.string, false⟩⟩, ⟨"location", ⟨.string, false⟩⟩, ⟨"lastVisited", ⟨.int, false⟩⟩]

example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))

-- This does not type check, even though it is a more accurate type of travel diary
-- example : Subschema travelDiary2 peak :=
--   .cons .here
--     (.cons (.there .here)
--       (.cons (.there (.there (.there .here))) .nil))

example : Subschema [] peak := .nil
example : Subschema [] peak := by constructor

example : Subschema [⟨"location", ⟨.string, false⟩⟩] peak := by
  constructor
  constructor
  constructor
  constructor

example : Subschema [⟨"location", ⟨.string, false⟩⟩] peak :=
  .cons (.there .here) .nil

example : Subschema [⟨"location", ⟨.string, false⟩⟩] peak := by repeat constructor

example: Subschema travelDiary peak := by repeat constructor

example : Subschema travelDiary waterfall := by repeat constructor

def Subschema.addColumn (sub : Subschema smaller bigger) : Subschema smaller (c :: bigger) :=
  match sub with
  | .nil => .nil
  | .cons col sub' => .cons (.there col) sub'.addColumn

def Subschema.reflexive : (s : Schema) → Subschema s s
  | [] => .nil
  | _ :: cs => .cons .here (reflexive cs).addColumn

def Row.project (row : Row s) : (s' : Schema) → Subschema s' s → Row s'
  | [], .nil => ()
  | [_], .cons c .nil => row.get c
  | _::_::_, .cons c cs => (row.get c, row.project _ cs)

-- "Ordinary comparison operators yield null (signifying “unknown”), not true or false, when either input is null."
-- (https://www.postgresql.org/docs/current/functions-comparison.html)
inductive DBExpr (s : Schema) : NDBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 : DBExpr s { underlying := t, nullable := n1 }) (e2 : DBExpr s { underlying := t, nullable := n2 }) : DBExpr s { underlying := .bool, nullable := n1 || n2 }
  | lt (e1 : DBExpr s { underlying := .int, nullable := n1 }) (e2 : DBExpr s { underlying := .int, nullable := n2 }) : DBExpr s { underlying := .bool, nullable := n1 || n2 }
  | and (e1 : DBExpr s { underlying := .bool, nullable := n1 }) (e2 : DBExpr s { underlying := .bool, nullable := n2 }) : DBExpr s { underlying := .bool, nullable := n1 || n2 }
  | const : (t : DBType).asType → DBExpr s { underlying := t, nullable := false }
  | isNull (e : DBExpr s { underlying := u, nullable := true }) : DBExpr s { underlying := .bool, nullable := false }
  | not (e : DBExpr s { underlying := .bool, nullable := n }) : DBExpr s { underlying := .bool, nullable := n }

def tallInDenmark : DBExpr peak ⟨.bool, false⟩ :=
  .and (.lt (.const 1000) (DBExpr.col "elevation" (.there (.there .here))))
    (.eq (DBExpr.col "location" (.there .here)) ((.const "Denmark") : DBExpr peak ({ underlying := .string, nullable := false } : NDBType)))

def visited : DBExpr peak ⟨.bool, false⟩ :=
  .not (.isNull (DBExpr.col "lastVisited" (.there (.there (.there .here)))))

def neverVisited : DBExpr peak ⟨.bool, false⟩ :=
  .isNull (DBExpr.col "lastVisited" (.there (.there (.there .here))))

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2 => NDBType.nullableEq (evaluate row e1) (evaluate row e2)
  | .lt e1 e2 => NDBType.nullableLessThan (evaluate row e1) (evaluate row e2)
  | .and e1 e2 => NDBType.nullableAnd (evaluate row e1) (evaluate row e2)
  | .const v => v
  | isNull e => match (evaluate row e) with | some _ => false | none => true
  | not e => NDBType.nullableNot (evaluate row e)

#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

#eval visited.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval visited.evaluate ("Fictional mountain", "Denmark", 1230, none)

#eval neverVisited.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval neverVisited.evaluate ("Fictional mountain", "Denmark", 1230, none)

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s {underlying := .bool, nullable := false} → Query s
  | project : Query s → (s' : Schema) → Subschema s' s → Query s'
  | product :
    Query s1 → Query s2 →
    disjoint (s1.map Column.name) (s2.map Column.name) →
    Query (s1 ++ s2)
  | renameColumn :
    Query s → (c : HasCol s n t) → (n' : String) → !((s.map Column.name).contains n') →
    Query (s.renameColumn c n')
  | prefixWith :
    (n : String) → Query s →
    Query (s.map fun c => {c with name := n ++ "." ++ c.name})

def addVal (v : c.contains.asType) (row : Row s) : Row (c :: s) :=
  match s, row with
  | [], () => v
  | _::_, v' => (v, v')

def Row.append (r1 : Row s1) (r2 : Row s2) : Row (s1 ++ s2) :=
  match s1, r1 with
  | [], () => r2
  | [_], v => addVal v r2
  | _::_::_, (v, r') => (v, r'.append r2)

def Table.cartesianProduct (table1 : Table s1) (table2 : Table s2) : Table (s1 ++ s2) := Id.run do
  let mut out : Table (s1 ++ s2) := []
  for r1 in table1 do
    for r2 in table2 do
      out := (r1.append r2) :: out
  pure out.reverse

def List.without [BEq α] (source banned : List α) : List α :=
  source.filter fun r => !(banned.contains r)

def Row.rename (c : HasCol s n t) (row : Row s) : Row (s.renameColumn c n') :=
  match s, row, c with
  | [_], v, .here => v
  | _::_::_, (v, r), .here => (v, r)
  | _::_::_, (v, r), .there next => addVal v (r.rename next)

def prefixRow (row : Row s) : Row (s.map fun c => {c with name := n ++ "." ++ c.name}) :=
  match s, row with
  | [], _ => ()
  | [_], v => v
  | _::_::_, (v, r) => (v, prefixRow r)

def Query.exec : Query s → Table s
  | .table t => t
  | .union q1 q2 => exec q1 ++ exec q2
  | .diff q1 q2 => exec q1 |>.without (exec q2)
  | .select q e => exec q |>.filter e.evaluate
  | .project q _ sub => exec q |>.map (·.project _ sub)
  | .product q1 q2 _ => exec q1 |>.cartesianProduct (exec q2)
  | .renameColumn q c _ _ => exec q |>.map (·.rename c)
  | .prefixWith _ q => exec q |>.map prefixRow

open Query in
def example1 :=
  table mountainDiary |>.select
    (.lt (.const 500) (DBExpr.col "elevation" (.there (.there .here)))) |>.project
    [⟨"elevation", ⟨.int, false⟩⟩] (by repeat constructor)

#eval example1.exec

open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfallResult := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfallResult (by simp [disjoint])
    |>.select (.eq (DBExpr.col "mountain.location" (.there .here)) (DBExpr.col "waterfall.location" (.there (.there (.there (.there (.there .here)))))))
    |>.project [⟨"mountain.name", ⟨.string, false⟩⟩, ⟨"waterfall.name", ⟨.string, false⟩⟩] (by repeat constructor)

#eval example2.exec

open Query in
def example3 :=
  table mountainDiary |>.select
    visited |>.project
    [⟨"name", ⟨.string, false⟩⟩] (by repeat constructor)

#eval example3.exec

open Query in
def example4 :=
  table mountainDiary |>.select
    neverVisited |>.project
    [⟨"name", ⟨.string, false⟩⟩] (by repeat constructor)

#eval example4.exec

-- # Dates

inductive DBType where
  | int | string | bool | date

abbrev isMonth (n : Nat) : Bool := n > 0 && n < 13

def Month : Type := {n : Nat // (isMonth n)}

instance : OfNat Month 1 where
  ofNat := ⟨1, by simp⟩
instance : OfNat Month 2 where
  ofNat := ⟨2, by simp⟩
instance : OfNat Month 3 where
  ofNat := ⟨3, by simp⟩
instance : OfNat Month 4 where
  ofNat := ⟨4, by simp⟩
instance : OfNat Month 5 where
  ofNat := ⟨5, by simp⟩
instance : OfNat Month 6 where
  ofNat := ⟨6, by simp⟩
instance : OfNat Month 7 where
  ofNat := ⟨7, by simp⟩
instance : OfNat Month 8 where
  ofNat := ⟨8, by simp⟩
instance : OfNat Month 9 where
  ofNat := ⟨9, by simp⟩
instance : OfNat Month 10 where
  ofNat := ⟨10, by simp⟩
instance : OfNat Month 11 where
  ofNat := ⟨11, by simp⟩
instance : OfNat Month 12 where
  ofNat := ⟨12, by simp⟩

instance : ToString Month where
  toString month := toString (month.val)

abbrev isDay (month : Month) (n : Nat) : Bool := n > 0 && (
  match month with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => n < 32
  | 4 | 6 | 9 | 11 => n < 31
  | 2 => n < 29 -- Ignore leap years
)

def Day (month : Month) : Type := {n : Nat // (isDay month n)}

instance : ToString (Day month) where
  toString day := toString (day.val)

def daysInYear : Nat := Id.run do
  let mut sum := 0
  for month in [1:13] do
    if h : isMonth month then
      for day in [1:32] do
        if isDay ⟨month, h⟩ day then
          sum := sum + 1
        else
          break
  pure sum

-- Can I prove that it is 365?
#eval daysInYear

-- Unsolved goal. Does this mean there are partial functions in the definition of `daysInYear`?
-- def daysInYearIs365 : daysInYear = 365 := by simp [daysInYear]

def daysInMonth (month : Month) : Nat :=
  let rec counter : Nat → Nat
    | 0 => 0
    | n + 1 => if isDay month n then
        1 + (counter n)
      else
        (counter n)
  counter 32

def daysInFebruary : (daysInMonth 2) = 28 := rfl
def daysInDecember : (daysInMonth 12) = 31 := rfl

def daysInYear2 : Nat :=
  let rec counter : Nat → Nat
    | 0 => 0
    | n + 1 => if hMonth : isMonth n then
        (daysInMonth ⟨n, hMonth⟩) + (counter n)
      else
        (counter n)
  counter 13

#eval daysInYear2

def daysInYearIs365 : daysInYear2 = 365 := rfl

def Year : Type := Nat

structure RawDate where
  year : Nat
  month : Nat
  day : Nat
deriving BEq, Repr

instance : ToString RawDate where
  toString date := s!"{date.year}-{date.month}-{date.day}"

structure Date where
  date : RawDate
  hMonth: isMonth date.month
  hDay: isDay ⟨date.month, hMonth⟩ date.day

def Date.year (d : Date) : Year := d.date.year
def Date.month (d : Date) : Month := ⟨d.date.month, d.hMonth⟩
def Date.day (d : Date) : Day d.month := ⟨d.date.day, d.hDay⟩

instance : ToString Date where
  toString date := toString date.date

#eval { date := {year := 1901, month := 2, day := 28}, hMonth := (by simp), hDay := (by simp) : Date}

macro "date!" n:term : term => `({ date := $n, hMonth := (by simp), hDay := (by simp) : Date })

#eval date! {year := 1904, month := 3, day := 30}

def Date.beq (d1 d2 : Date) : Bool :=
  d1.date == d2.date

instance : BEq Date where
  beq := Date.beq

instance : Repr Date where
  reprPrec date := reprPrec date.date

abbrev DBType.asType : DBType → Type
  | .int => Int
  | .string => String
  | .bool => Bool
  | .date => Date

#eval ("Mount Hood" : DBType.string.asType)
#eval (date! {year := 1900, month := 12, day := 31} : DBType.date.asType)

def DBType.beq (t : DBType) (x y : t.asType) : Bool :=
  match t with
  | .int | .string | .bool | .date => x == y

instance {t : DBType} : BEq t.asType where
  beq := t.beq

instance : BEq DBType where
  beq
    | .int, .int | .string, .string | .bool, .bool | .date, .date => true
    | _, _ => false

instance {t : DBType} : Repr t.asType where
  reprPrec :=
    match t with
    | .int | .string | .bool | .date => reprPrec

structure Column where
  name : String
  contains : DBType

abbrev Schema := List Column

abbrev Row : Schema → Type
  | [] => Unit
  | [col] => col.contains.asType
  | col1 :: col2 :: cols => col1.contains.asType × Row (col2::cols)

abbrev Table (s : Schema) := List (Row s)

abbrev peak : Schema := [
  ⟨"name", DBType.string⟩,
  ⟨"location", DBType.string⟩,
  ⟨"elevation", DBType.int⟩,
  ⟨"lastVisited", DBType.date⟩
]

def mountainDiary : Table peak := [
  ⟨"Mount Nebo", "USA", 3637, date! {year := 2013, month := 2, day := 5}⟩,
  ⟨"Moscow Mountain", "USA", 1519, date! {year := 2015, month := 3, day := 15}⟩,
  ⟨"Himmelbjerget", "Denmark", 147,  date! {year := 2004, month := 4, day := 25}⟩,
  ⟨"Mount St. Helens", "USA", 2549, date! {year := 2010, month := 5, day := 21}⟩
]

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .date⟩
]

def waterfallDiary : Table waterfall := [
  ⟨"Multnomah Falls", "USA", date! {year := 2018, month := 6, day := 4}⟩,
  ⟨"Shoshone Falls", "USA", date! {year := 2014, month := 7, day := 1}⟩
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

inductive HasCol : Schema → String → DBType → Type where
  | here : HasCol (⟨name, t⟩ :: _) name t
  | there : HasCol s name t → HasCol (_ :: s) name t

example : HasCol peak "elevation" .int :=
  .there (.there .here)

def Row.get (row : Row s) (col : HasCol s n t) : t.asType :=
  match s, col, row with
  | [_], .here, v => v
  | _::_::_, .here, (v, _) => v
  | _::_::_, .there next, (_, r) => get r next

#eval mountainDiary[1].get (.there (.there .here) : HasCol peak "elevation" .int)

inductive Subschema : Schema → Schema → Type where
  | nil : Subschema [] bigger
  | cons :
    HasCol bigger n t →
    Subschema smaller bigger →
    Subschema (⟨n, t⟩ :: smaller) bigger

abbrev travelDiary : Schema :=
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .date⟩]

example : Subschema travelDiary peak :=
  .cons .here
    (.cons (.there .here)
      (.cons (.there (.there (.there .here))) .nil))

example : Subschema [] peak := .nil
example : Subschema [] peak := by constructor

example : Subschema [⟨"location", .string⟩] peak := by
  constructor
  constructor
  constructor
  constructor

example : Subschema [⟨"location", .string⟩] peak :=
  .cons (.there .here) .nil

example : Subschema [⟨"location", .string⟩] peak := by repeat constructor

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

inductive DBExpr (s : Schema) : DBType → Type where
  | col (n : String) (loc : HasCol s n t) : DBExpr s t
  | eq (e1 e2 : DBExpr s t) : DBExpr s .bool
  | lt (e1 e2 : DBExpr s .int) : DBExpr s .bool
  | before (e1 e2 : DBExpr s .date) : DBExpr s .bool
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
    (.eq (c! "location") (.const "Denmark"))

def RawDate.lt (d1 d2 : RawDate) : Bool :=
  if d1.year == d2.year then
    if d1.month == d2.month then
      d1.day < d2.day
    else
      d1.month < d2.month
  else
    d1.year < d2.year

instance : LT RawDate where
  lt d1 d2 := (RawDate.lt d1 d2)

def Date.lt (d1 d2 : Date) : Bool :=
  d1.date.lt d2.date

instance : LT Date where
  lt d1 d2 := (Date.lt d1 d2)

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2 => evaluate row e1 == evaluate row e2
  | .lt e1 e2 => evaluate row e1 < evaluate row e2
  | .before e1 e2 => (evaluate row e1).lt (evaluate row e2)
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v

#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, date! {year := 2023, month := 8, day := 15})
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, date! {year := 2023, month := 9, day := 12})
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, date! {year := 1996, month := 10, day := 8})

#eval (date! {year := 2000, month := 2, day := 1}).lt (date! {year := 2000, month := 2, day := 3})

def visitedEarlyInDenmark : DBExpr peak .bool :=
  .and (.before (c! "lastVisited") (.const (date! {year := 2000, month := 1, day := 1})))
    (.eq (c! "location") (.const "Denmark"))
#eval visitedEarlyInDenmark.evaluate ("Valby Bakke", "Denmark", 31, date! {year := 2023, month := 8, day := 15})
#eval visitedEarlyInDenmark.evaluate ("Valby Bakke", "Denmark", 31, date! {year := 1999, month := 8, day := 15})

def disjoint [BEq α] (xs ys : List α) : Bool :=
  not (xs.any ys.contains || ys.any xs.contains)

def Schema.renameColumn : (s : Schema) → HasCol s n t → String → Schema
  | c :: cs, .here, n' => {c with name := n'} :: cs
  | c :: cs, .there next, n' => c :: renameColumn cs next n'

inductive Query : Schema → Type where
  | table : Table s → Query s
  | union : Query s → Query s → Query s
  | diff : Query s → Query s → Query s
  | select : Query s → DBExpr s .bool → Query s
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
    (.lt (.const 500) (c! "elevation")) |>.project
    [⟨"elevation", .int⟩] (by repeat constructor)

#eval example1.exec

open Query in
def example2 :=
  let mountain := table mountainDiary |>.prefixWith "mountain"
  let waterfallResult := table waterfallDiary |>.prefixWith "waterfall"
  mountain.product waterfallResult (by simp [disjoint])
    |>.select (.eq (c! "mountain.location") (c! "waterfall.location"))
    |>.project [⟨"mountain.name", .string⟩, ⟨"waterfall.name", .string⟩] (by repeat constructor)

#eval example2.exec

open Query in
def example3 :=
  table mountainDiary |>.select
    (.before (c! "lastVisited") (.const (date! {year := 2014, month := 8, day := 15})) ) |>.project
    [⟨"elevation", .int⟩, ⟨"lastVisited", .date⟩] (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))

#eval example3.exec

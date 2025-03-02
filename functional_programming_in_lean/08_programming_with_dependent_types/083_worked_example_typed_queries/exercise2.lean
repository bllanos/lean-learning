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
  ⟨"lastVisited", DBType.int⟩
]

def mountainDiary : Table peak := [
  ⟨"Mount Nebo", "USA", 3637, 2013⟩,
  ⟨"Moscow Mountain", "USA", 1519, 2015⟩,
  ⟨"Himmelbjerget", "Denmark", 147, 2004⟩,
  ⟨"Mount St. Helens", "USA", 2549, 2010⟩
]

abbrev waterfall : Schema := [
  ⟨"name", .string⟩,
  ⟨"location", .string⟩,
  ⟨"lastVisited", .int⟩
]

def waterfallDiary : Table waterfall := [
  ⟨"Multnomah Falls", "USA", 2018⟩,
  ⟨"Shoshone Falls", "USA", 2014⟩
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
  [⟨"name", .string⟩, ⟨"location", .string⟩, ⟨"lastVisited", .int⟩]

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
  | and (e1 e2 : DBExpr s .bool) : DBExpr s .bool
  | const : t.asType → DBExpr s t

macro "c!" n:term : term => `(DBExpr.col $n (by repeat constructor))

def tallInDenmark : DBExpr peak .bool :=
  .and (.lt (.const 1000) (c! "elevation"))
    (.eq (c! "location") (.const "Denmark"))

def DBExpr.evaluate (row : Row s) : DBExpr s t → t.asType
  | .col _ loc => row.get loc
  | .eq e1 e2 => evaluate row e1 == evaluate row e2
  | .lt e1 e2 => evaluate row e1 < evaluate row e2
  | .and e1 e2 => evaluate row e1 && evaluate row e2
  | .const v => v

#eval tallInDenmark.evaluate ("Valby Bakke", "Denmark", 31, 2023)
#eval tallInDenmark.evaluate ("Fictional mountain", "Denmark", 1230, 2023)
#eval tallInDenmark.evaluate ("Mount Borah", "USA", 3859, 1996)

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

-- # Examples

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

-- "failed to synthesize OfNat Pos 7"
-- def seven : Pos := 7

-- "failed to synthesize HAdd Pos Pos ?m.266"
-- def fourteen : Pos := Pos.one + Pos.one

-- ## Classes and instances

-- Homogenous addition
#eval Add.add 5 3
-- Heterogeneous addition
#eval HAdd.hAdd 5 3

class Plus (α : Type) where
  plus : α → α → α
-- Type classes are functions of `Type`
#check (Plus)

instance : Plus Nat where
  plus := Nat.add

#eval Plus.plus 5 3

open Plus (plus) in
#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def seven : Pos := Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
def fourteen : Pos := Pos.plus seven seven

-- "failed to synthesize Plus Float"
-- #eval Plus.plus 5.2 917.25861

-- ## Overloaded addition

instance : Add Pos where
  add := Pos.plus

def fourteen2 : Pos := seven + seven

-- ## Conversion to strings

def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"

def Pos.toNat: Pos → Nat
  | Pos.one => 1
  | Pos.succ n => Pos.toNat n + 1

instance : ToString Pos where
  toString := toString ∘ Pos.toNat

#eval s!"There are {seven}"
-- Using `posToString`:
-- "There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"

-- #eval can use `ToString`, not only `Repr`
#eval seven

-- ## Overloaded multiplication

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => (n.mul k) + k

instance : Mul Pos where
  mul := Pos.mul

#eval [seven * Pos.one, seven * seven, Pos.succ Pos.one * seven]

-- ## Literal numbers

class OfNat2 (α : Type) (_ : Nat) where
  ofNat : α

inductive LessThan4 where
  | zero
  | one
  | two
  | three
deriving Repr

instance : OfNat LessThan4 0 where
  ofNat := LessThan4.zero

instance : OfNat LessThan4 1 where
  ofNat := LessThan4.one

instance : OfNat LessThan4 2 where
  ofNat := LessThan4.two

instance : OfNat LessThan4 3 where
  ofNat := LessThan4.three

#eval (3 : LessThan4)
-- #eval (4 : LessThan4)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

def eight : Pos := 8
#eval eight
-- def zero : Pos := 0

-- # Exercises

-- ## Another representation for positive numbers

structure Pos2 where
  succ ::
  pred : Nat

def one2 : Pos2 := {pred := 0}
def seven2 : Pos2 := {pred := 6}

def Pos2.plus: Pos2 → Pos2 → Pos2
  | {pred := a}, {pred := b} => { pred := a + b + 1 }

instance : Add Pos2 where
  add := Pos2.plus

def fourteenPos2 : Pos2 := seven2 + seven2

def Pos2.toNat : Pos2 → Nat
  | {pred := a} => a + 1

instance : ToString Pos2 where
  toString := toString ∘ Pos2.toNat

#eval s!"There are {seven2}"

def Pos2.mul (a b: Pos2) : Pos2 :=
  {pred := a.pred * b.pred + a.pred + b.pred}

instance : Mul Pos2 where
  mul := Pos2.mul

#eval [seven2 * one2,
       seven2 * seven2,
       (one2 + one2) * seven2]

instance : OfNat Pos2 (n + 1) where
  ofNat := Pos2.succ n

def eight2 : Pos2 := 8
#eval eight2
-- def zero2 : Pos2 := 0

-- ## Even numbers

inductive Even : Type where
  | zero : Even
  | succ : Even → Even

def fourEven : Even := Even.succ (Even.succ Even.zero)
open Even (zero succ) in
def eightEven : Even := succ (succ (succ (succ zero)))

def Even.plus : Even → Even → Even
  | Even.zero, k => k
  | Even.succ n, k => Even.succ (n.plus k)

instance : Add Even where
  add := Even.plus

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.succ n => n.toNat + 2

instance : ToString Even where
  toString := toString ∘ Even.toNat

def Even.mul : Even → Even → Even
  | Even.zero, _ => Even.zero
  | Even.succ n, k => Even.plus k (Even.plus k (Even.mul n k))

instance : Mul Even where
  mul := Even.mul

def twelveEven : Even := fourEven + eightEven
#eval twelveEven
def fortyEightEven : Even := twelveEven * fourEven
#eval fortyEightEven

-- ## HTTP Requests

inductive HttpVerb where
-- There are more methods than these
  | get
  | put
  | post
  | delete

structure HttpRequest where
  request ::
  method: HttpVerb
  uri: String
  version: String

structure HttpResponse where
  response ::
  statusCode : Nat
  body : String

def HttpResponse.toString: HttpResponse → String
  | { statusCode, body} =>
    s!"HTTP status code {statusCode} : {body}"

class HttpServer (α : Type) (_: HttpVerb) where
  handleRequest: α → IO HttpRequest → IO Unit

structure StatelessHttpServer where
  server ::

instance : HttpServer StatelessHttpServer HttpVerb.get where
  handleRequest (_ : StatelessHttpServer) (requestAction : IO HttpRequest) : IO Unit := do
    let request ← requestAction
    let stdout ← IO.getStdout
    stdout.putStrLn {statusCode := 200, body := s!"content exists for \"{request.uri}\"" : HttpResponse}.toString

instance : HttpServer StatelessHttpServer HttpVerb.put where
  handleRequest (_ : StatelessHttpServer) (requestAction : IO HttpRequest) : IO Unit := do
    let request ← requestAction
    let stdout ← IO.getStdout
    stdout.putStrLn {statusCode := 201, body := s!"content created for \"{request.uri}\"" : HttpResponse}.toString

instance : HttpServer StatelessHttpServer HttpVerb.post where
  handleRequest (_ : StatelessHttpServer) (requestAction : IO HttpRequest) : IO Unit := do
    let request ← requestAction
    let stdout ← IO.getStdout
    stdout.putStrLn {statusCode := 404, body := s!"\"{request.uri}\" not found" : HttpResponse}.toString

-- `delete` method intentionally not handled

-- Type classes have constructors
#check HttpServer.mk

def main : IO Unit :=
  let serverInstance : StatelessHttpServer := StatelessHttpServer.server
  -- "failed to synthesize HttpServer ?m.6849 HttpVerb.delete"
  -- HttpServer.handleRequest HttpVerb.delete

  let requests : List HttpRequest := [
    { method := HttpVerb.get, uri := "/get/this", version := "1.1" },
    { method := HttpVerb.put, uri := "/put/this", version := "1.1" },
    { method := HttpVerb.post, uri := "/post/this", version := "1.1" }
  ]
  let actions : List (IO Unit) := requests.map fun request =>
    match request.method with
    | HttpVerb.delete => (pure () : IO Unit)
    | HttpVerb.get => HttpServer.handleRequest HttpVerb.get serverInstance (pure request)
    | HttpVerb.put => HttpServer.handleRequest HttpVerb.put serverInstance (pure request)
    | HttpVerb.post => HttpServer.handleRequest HttpVerb.post serverInstance (pure request)
  actions.foldl (fun result action => do result; action) (pure ())

-- # Examples

import Lean

-- ## Positive numbers

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

-- #eval [1, 2, 3, 4, 5].drop (2 : Pos)

class Coe2 (α : Type) (β : Type) where
  coe : α → β

instance : Coe Pos Nat where
  coe x := x.toNat

#check @Coe.coe

#eval [1, 2, 3, 4, 5].drop (2 : Pos)
#check [1, 2, 3, 4, 5].drop (2 : Pos)

-- ## Chaining coercions

def oneInt : Int := Pos.one
def oneInt2 : Int := ↑↑Pos.one

inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
#eval coercedToB

def List.getLast2? : List α → Option α
  | [] => none
  | x :: xs => match xs with
    | [] => x
    | _ => xs.getLast2?

def List.getLast3? : List α → Option α
  | [] => none
  | [x] => x -- Coerced to `some x`
  | _ :: x :: xs => getLast3? (x :: xs)

def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"

-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
--   392

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)

def perhapsPerhapsPerhapsNat2 : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

-- ## Non-empty lists and dependent coercions

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance : Coe (NonEmptyList α) (List α) where
  coe
   | { head := x, tail := xs } => x :: xs

class CoeDep2 (α : Type) (x : α) (β : Type) where
  coe : β

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

-- ## Coercing to types

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Monoid Type where
  coe m := m.Carrier

def foldMap2 (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

instance : CoeSort Bool Prop where
  coe b := b = true

-- ## Coercing to functions

class CoeFun2 (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

-- #eval add5 3

instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3

inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
deriving Repr

structure Serializer where
  Contents : Type
  serialize : Contents → JSON

def Str : Serializer :=
  { Contents := String, serialize := JSON.string
  }

instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]

def buildResponse2 (title : String) (R : Serializer) (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", (CoeFun.coe R) record)
  ]

#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"

-- ### JSON as a String

#eval (5 : Float).toString

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString

#eval dropDecimals (5 : Float).toString
#eval dropDecimals (5.2 : Float).toString

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))

#eval ", ".separate ["1", "2"]
#eval ", ".separate ["1"]
#eval ", ".separate []

partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString (mem : String × JSON) :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"

#eval (buildResponse "FunctionalProgramming in Lean" Str "Programming is fun!").asString

-- ## Design considerations

def idahoSpiders : NonEmptyList ( α := String ):= {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def lastSpider : Option String :=
  List.getLast? idahoSpiders
#eval lastSpider

-- def lastSpider2 :=
--   List.getLast? idahoSpiders

def lastSpider2 :=
  List.getLast? (idahoSpiders : List String)

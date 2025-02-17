-- # Examples

inductive NatOrBool where
  | nat | bool

abbrev NatOrBool.asType (code : NatOrBool) : Type :=
  match code with
  | .nat => Nat
  | .bool => Bool

def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none

inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  -- This would produce an arbitrarily long type?
  | .pair t1 t2 => asType t1 × asType t2

def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
  match t with
  | .nat => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

-- Notice that it is possible to pass implicit arguments
-- when defining an instance of a type class.
instance {t : NestedPairs} : BEq t.asType where
  beq x y := t.beq x y

-- instance {t : NestedPairs} : BEq t.asType where
--   beq x y := x == y

-- ## A universe of finite types

inductive Finite where
  | unit : Finite
  | bool : Finite
  | pair : Finite → Finite → Finite
  | arr : Finite → Finite → Finite -- `arr`ow

abbrev Finite.asType : Finite → Type
  | .unit => Unit
  | .bool => Bool
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2

def ysPowerXs (xs : List α) (ys : List β) : List (List (α × β)) :=
  match xs with
  | [] => []
  | x :: xs' =>
    let ysPowerXs' := ysPowerXs xs' ys
    (ys.flatMap fun y => -- Flatten the lists of functions into a list of functions
      ysPowerXs'.map fun f => -- One list of functions where x maps to y
        (x, y) :: f) -- One function

-- def Finite.enumerate (t : Finite) : List t.asType :=
--   match t with
--   | .unit => [()]
--   | .bool => [true, false]
--   | .pair t1 t2 => t1.enumerate.flatMap fun x =>
--       t2.enumerate.map fun y => (x, y)
--   | .arr t1 t2 =>
--     let allT1 := t1.enumerate
--     let allT2 := t2.enumerate
--     let fTables := ysPowerXs allT1 allT2
--     fTables.map fun table =>
--       fun x =>
--         -- Need an implementation of BEq here
--         -- The solution given in the book avoids this problem by handling
--         -- each `Finite` type code separately, but another solution may be
--         -- to use a `mutual` block.
--         let findResult := table.find? fun element => element.fst == x
--         match findResult with
--         | none => allT2[0]! -- Need to prove that this should never happen
--         | some element => element.snd

def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
  let mut out : List (α × β) := []
  for x in xs do
    for y in ys do
      out := (x, y) :: out
  pure out.reverse

def List.foldr2 (f : α → β → β) (default : β) : List α → β
  | [] => default
  | a :: l => f a (foldr2 f default l)

mutual
def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
  match t with
  | .unit =>
    results.map fun r =>
      fun () => r
  | .bool =>
    (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
  | .pair t1 t2 =>
    let f1s := t1.functions <| t2.functions results
    -- Un-currying the functions:
    f1s.map fun f =>
      fun (x, y) =>
        f x y
  | .arr t1 t2 =>
    let args := t1.enumerate
    let base :=
      results.map fun r =>
        fun _ => r
    args.foldr
      (fun arg rest =>
        (t2.functions rest).map fun more =>
          fun f => more (f arg) f)
      base

def Finite.enumerate (t : Finite) : List t.asType :=
  match t with
  | .unit => [()]
  | .bool => [true, false]
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr t1 t2 => t1.functions t2.enumerate
end

def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
  match t with
  | .unit => true
  | .bool => x == y
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
    t1.enumerate.all fun arg => beq t2 (x arg) (y arg)

#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
#eval Finite.beq (.arr .bool .bool) id (not ∘ not)

-- # Exercises

-- ## String conversion for Finite

def Finite.toString (t : Finite) (x : t.asType) : String :=
  match t with
  | .unit => "Finite ()"
  | .bool => s!"Finite {x}"
  | .pair t1 t2 => s!"Finite ({toString t1 x.fst}, {toString t2 x.snd})"
  | .arr t1 t2 =>
    let allT1 := t1.enumerate
    let table := allT1.map fun arg => (toString t1 arg, toString t2 (x arg))
    s!"Finite {table}"

-- Even if marked as `@[default_instance]`,
-- this does not override the built-in ToString instance
instance {t : Finite} : ToString t.asType where
  toString := t.toString

#eval (Finite.toString .unit ())
#eval (ToString.toString ())

#eval (Finite.toString .bool true)
#eval (Finite.toString (.pair .bool .unit) (true, ()))
#eval (Finite.toString (.arr .bool .bool) fun
  | true => false
  | false => false
  )

-- ## Finite with Empty and Option types

inductive Finite2 where
  | empty : Finite2
  | unit : Finite2
  | bool : Finite2
  | option : Finite2 → Finite2
  | pair : Finite2 → Finite2 → Finite2
  | arr : Finite2 → Finite2 → Finite2 -- `arr`ow

abbrev Finite2.asType : Finite2 → Type
  | .empty => Empty
  | .unit => Unit
  | .bool => Bool
  | .option t => Option (asType t)
  | .pair t1 t2 => asType t1 × asType t2
  | .arr t1 t2 => asType t1 → asType t2

#check absurd
#check Empty.elim
#check Empty.rec

mutual
def Finite2.functions (t : Finite2) (results : List α) : List (t.asType → α) :=
  match t with
  | .empty => [Empty.elim]
  | .unit =>
    results.map fun r =>
      fun () => r
  | .bool =>
    (results.product results).map fun (r1, r2) =>
    fun
      | true => r1
      | false => r2
  | .option t1 =>
    -- Choose a result for `none`
    -- Choose a result for each of `t1.asType`
    -- `|results| ^ (|t1.asType| + 1)` possible functions
    -- `|results| × (|results| ^ |t1.asType|)` possible functions
    (results.product (t1.functions results)).map fun (r1, r2) =>
    fun
      | none => r1
      | some x => r2 x
  | .pair t1 t2 =>
    let f1s := t1.functions <| t2.functions results
    -- Un-currying the functions:
    f1s.map fun f =>
      fun (x, y) =>
        f x y
  | .arr t1 t2 =>
    let args := t1.enumerate
    let base :=
      results.map fun r =>
        fun _ => r
    args.foldr
      (fun arg rest =>
        (t2.functions rest).map fun more =>
          fun f => more (f arg) f)
      base

def Finite2.enumerate (t : Finite2) : List t.asType :=
  match t with
  | .empty => []
  | .unit => [()]
  | .bool => [true, false]
  | .option t1 => none :: (t1.enumerate.map some)
  | .pair t1 t2 => t1.enumerate.product t2.enumerate
  | .arr t1 t2 => t1.functions t2.enumerate
end

def Finite2.beq (t : Finite2) (x y : t.asType) : Bool :=
  match t with
  | .empty => false -- Unreachable
  | .unit => true
  | .bool => x == y
  | .option t1 => match x, y with
    | none, none => true
    | some x', some y' => beq t1 x' y'
    | _, _ => false
  | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
  | .arr t1 t2 =>
    t1.enumerate.all fun arg => beq t2 (x arg) (y arg)

#eval Finite2.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
#eval Finite2.beq (.arr .bool .bool) id (not ∘ not)
#eval Finite2.beq (.option .bool) none none
#eval Finite2.beq (.option .bool) none (some true)
#eval Finite2.beq (.option .bool) (some true) (some true)
#eval Finite2.beq (.option .bool) (some true) none
#eval Finite2.beq (.option .bool) (some true) (some false)

def Finite2.toString (t : Finite2) (x : t.asType) : String :=
  match t with
  | .empty => "Finite2 Empty"
  | .unit => "Finite2 ()"
  | .bool => s!"Finite2 {x}"
  | .option t1 => s!"Finite2 {match x with | none => "None" | some x' => s!"Some ({toString t1 x'})"}"
  | .pair t1 t2 => s!"Finite2 ({toString t1 x.fst}, {toString t2 x.snd})"
  | .arr t1 t2 =>
    let allT1 := t1.enumerate
    let table := allT1.map fun arg => (toString t1 arg, toString t2 (x arg))
    s!"Finite2 {table}"

#eval (Finite2.toString .unit ())
#eval (ToString.toString ())

#eval (Finite2.toString .bool true)
#eval (Finite2.toString (.option .bool) none)
#eval (Finite2.toString (.option .bool) (some true))
#eval (Finite2.toString (.pair .bool .unit) (true, ()))
#eval (Finite2.toString (.arr .bool .bool) fun
  | true => false
  | false => false
  )

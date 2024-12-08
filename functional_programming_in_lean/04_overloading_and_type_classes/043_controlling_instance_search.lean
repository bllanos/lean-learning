-- # Examples

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

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

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

-- #eval HPlus.hPlus (3 : Pos) (5 : Nat)
#eval HPlus.hPlus (γ := Pos) (3 : Pos) (5 : Nat)
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)

-- ## Output parameters

class HPlus2 (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ

instance : HPlus2 Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus2 Pos Nat Pos where
  hPlus := addPosNat

#eval HPlus2.hPlus (3 : Pos) (5 : Nat)

-- ## Default instances

instance [Add α] : HPlus2 α α α where
  hPlus := Add.add

#eval HPlus2.hPlus (3 : Nat) (5 : Nat)
#check HPlus2.hPlus (5 : Nat) (3 : Nat)
#check HPlus2.hPlus (5 : Nat)

@[default_instance]
instance [Add α] : HPlus2 α α α where
  hPlus := Add.add

#check HPlus2.hPlus (5 : Nat)

-- # Exercises

structure PPoint {α : Type} where
  x : α
  y : α
deriving Repr

instance [Mul α] : HMul (PPoint (α := α)) α (PPoint (α := α)) where
  hMul p s := { x := p.x * s, y := p.y * s }

#eval {x := 2.5, y := 3.7 : PPoint (α := Float) } * 2.0

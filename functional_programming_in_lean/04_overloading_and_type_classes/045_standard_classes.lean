-- # Examples

-- Floating point numbers overload Boolean equality?
-- In Rust, they only overload "partial equality"
#eval BEq.beq 4.5 4.5

-- This has type `Prop`.
#check (fun (x : Nat) => 1 + x) = (Nat.succ ·)

#check 2 < 4
#eval if 2 < 4 then 1 else 2

-- Propositional equality of functions is undecidable?
-- #eval if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"

inductive Ordering2 where
| lt
| eq
| gt

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.comp : Pos → Pos → Ordering
  | one, pos => match pos with
    | one => Ordering.eq
    | succ _ => Ordering.lt
  | succ n, pos => match pos with
    | one => Ordering.gt
    | succ k => n.comp k

instance : Ord Pos where
  compare := Pos.comp

-- ## Hashing

class Hashable2 (α : Type) where
  hash : α → UInt64

def hashPos : Pos → UInt64
  | Pos.succ n => mixHash 1 (hashPos n)
  | Pos.one => 0

instance : Hashable Pos where
  hash := hashPos

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
#check (BinTree.leaf)

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1 (mixHash (hashBinTree left) (mixHash (hash x) (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

-- ## Deriving standard classes

deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

#check Inhabited
#check Inhabited.default
deriving instance Inhabited for Pos

#eval Inhabited.default (α := Pos)

#check Ord

-- ## Appending

class HAppend2 (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ

instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail}

def idahoSpiders : NonEmptyList ( α := String ):= {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }

#eval idahoSpiders ++ ["Trapdoor Spider"]

-- ## Functors

#eval Functor.map (· + 5) [1, 2, 3]
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1, 2, 3], [4, 5, 6]]
#eval (· + 5) <$> [1, 2, 3]

instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail

class Functor2 (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll

-- Functor rules
-- `id <$> x = x`
-- `map (fun y => f ∘ g y) x = map f (map g x)`

-- # Exercises

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys : (NonEmptyList α) :=
    match xs with
      | [] => ys
      | x :: xs => { head := x, tail := xs ++ (List.cons ys.head ys.tail) }

#eval ["Trapdoor Spider"] ++ idahoSpiders
#eval ([] : List String) ++ idahoSpiders

 def BinTree.map {α β : Type} (f : α → β) : BinTree α → BinTree β
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch l x r => BinTree.branch (l.map f) (f x) (r.map f)

instance : Functor BinTree where
  map := BinTree.map

-- Identity rule of functors
#eval id <$> (BinTree.leaf : BinTree Nat)
#eval id <$> (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

-- Composition rule of functors
#eval (· * 2) <$> (BinTree.leaf : BinTree Nat)
#eval (· * 2) <$> (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

#eval (· + 2) <$> (BinTree.leaf : BinTree Nat)
#eval (· + 2) <$> (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

#eval ((· + 2) ∘ (· * 2)) <$> (BinTree.leaf : BinTree Nat)
#eval ((· + 2) ∘ (· * 2)) <$> (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

-- Mapping between different types
#eval toString <$> (BinTree.branch BinTree.leaf 5 (BinTree.branch BinTree.leaf 10 BinTree.leaf))

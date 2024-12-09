-- # Examples

def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size
#eval northernTrees[2]
-- #eval northernTrees[8]

-- ## Non-empty lists

-- It seems like defining `α` as an explicit parameter would be better.
structure NonEmptyList {α : Type} : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList ( α := String ):= {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? {α : Type} : (NonEmptyList ( α := α )) → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? { head := h, tail := t } n

def NonEmptyList.get2? {α : Type} : (NonEmptyList ( α := α )) → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get? n

abbrev NonEmptyList.inBounds (xs : (NonEmptyList (α := α))) (i : Nat) : Prop :=
  i ≤ xs.tail.length

theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by simp [idahoSpiders]
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by simp [idahoSpiders]

def NonEmptyList.get (xs : NonEmptyList (α := α)) (i : Nat) (ok: xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

-- ## Overloading indexing

class GetElem2 (coll : Type) (idx : Type) (item : outParam Type) (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item

instance : GetElem (NonEmptyList ( α := α )) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

#eval idahoSpiders[0]
-- #eval idahoSpiders[9]

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.toNat: Pos → Nat
  | Pos.one => 1
  | Pos.succ n => Pos.toNat n + 1

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y

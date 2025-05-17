-- # Practice

def arr : Array String := #["one", "two", "three"]

example : String :=
  -- Using a field accessor of the `Array` structure
  -- triggers a conversion to a logical representation
  match arr.toList with
    | [] => "empty"
    | x :: _xs => x

-- # Exercise

-- Inefficient representation
-- (equivalent to a linked list)
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos

def Pos.toNat: Pos → Nat
  | Pos.one => 1
  | Pos.succ n => Pos.toNat n + 1

instance : ToString Pos where
  toString := toString ∘ Pos.toNat

def Pos.add : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.add k)

instance : Add Pos where
  add := Pos.add

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => (n.mul k) + k

instance : Mul Pos where
  mul := Pos.mul

-- Efficient representation
-- (same representation as `Nat`)
def FastPos : Type := {x : Nat // x > 0}

-- Pendantic proof
theorem nat_add_ne_zero : ∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0 := by
  intro n k hn hk
  match n with
  | .zero => contradiction
  | .succ n' => match k with
    | .zero => contradiction
    | .succ k' =>
      rw [Nat.add_succ, Nat.add_comm, Nat.add_succ]
      have hne := Nat.succ_ne_zero
      apply hne

-- Shorter proof
theorem nat_add_ne_zero2 : ∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0 := by
  omega

def FastPos.toNat: FastPos → Nat
  | { val, property := _property } => val

instance : ToString FastPos where
  toString := toString ∘ FastPos.toNat

def FastPos.add (p1 p2 : FastPos) : FastPos :=
  ⟨p1.val + p2.val, (by
    have hne1 := Nat.ne_zero_of_lt p1.property
    have hne2 := Nat.ne_zero_of_lt p2.property
    have hne3 := nat_add_ne_zero hne1 hne2
    rw [Nat.ne_zero_iff_zero_lt] at hne3
    assumption
    )⟩

instance : Add FastPos where
  add := FastPos.add

def FastPos.mul (p1 p2 : FastPos) : FastPos :=
  ⟨p1.val * p2.val, (by
    simp
    rw [←Nat.ne_zero_iff_zero_lt, Nat.mul_ne_zero_iff]
    constructor
    apply Nat.ne_zero_of_lt p1.property
    apply Nat.ne_zero_of_lt p2.property
    )⟩

instance : Mul FastPos where
  mul := FastPos.mul

#eval Pos.one + (Pos.succ Pos.one)
#eval (Pos.one + (Pos.succ Pos.one)) * (Pos.succ Pos.one)

#eval (⟨1, by decide⟩ + ⟨2, by decide⟩ : FastPos)
#eval (⟨3, by decide⟩ * ⟨2, by decide⟩ : FastPos)

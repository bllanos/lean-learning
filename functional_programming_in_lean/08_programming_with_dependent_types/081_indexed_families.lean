-- # Examples

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

#check Vect.nil
#check (Vect.nil)
#check Vect.cons
#check (Vect.cons)

-- example : Vect String 3 := Vect.nil

#check 0
#check Nat

-- example : Vect String n := Vect.nil

-- example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

def List.replicate2 (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  -- This line is wrong, but the compiler cannot catch the mistake
  | k + 1 => x :: x :: replicate2 k x

-- def Vect.replicate2 (n : Nat) (x : α) : Vect α n :=
--   match n with
--   | 0 => .nil
--   -- Type mismatch error
--   | k + 1 => .cons x (.cons x (replicate2 k x))

def Vect.length (_v : Vect α n) : { x : Nat // x = n } :=
  ⟨n, by simp⟩

def vec2 : Vect Nat 2 := Vect.cons 2 (Vect.cons 1 Vect.nil)
#eval vec2.length

def Vect.slowLength (v : Vect α n) : { x : Nat // x = n } :=
  match v with
   | .nil => ⟨0, by simp⟩
   | .cons _ tail =>
    let {val := xTail, property := hTail} := slowLength tail
    ⟨xTail + 1, by simp [hTail]⟩

#eval vec2.slowLength

#eval ["Mount Hood", "Mount Jefferson", "South Sister"].zip [
  "Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"
]

#eval [3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

-- def List.zip2 : List α → List β → List (α × β)
--   | [], [] => []
--   | x :: xs, y :: ys => (x, y) :: zip xs ys

-- def Vect.zip2 : Vect α n → Vect β n → Vect (α × β) n
--   | .nil, .nil => .nil
--   | .nil, .cons y ys => .nil
--   | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)

-- Demonstrating index refinement during pattern matching
def Vect.zip2 : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip2 k xs ys)

-- # Exercises

-- ## Vect.zip

def oregonianPeaks : Vect String 3 :=
  Vect.cons "Mount Hood" (
    Vect.cons "Mount Jefferson" (
      Vect.cons "South Sister"
      Vect.nil))

def Vect.fromList : (xs : List α) → Vect α (xs.length)
  | [] => .nil
  | y :: ys => .cons y (fromList ys)

def danishPeaks : Vect String 3 := (Vect.fromList [
  "Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"
])

#eval oregonianPeaks.zip danishPeaks

def Vect.elementsToString [ToString α] : Vect α (k+1) → String
  | .cons x xs =>
    match xs with
    | .nil => ToString.toString x
    | .cons y ys => s!"{ToString.toString x}, {elementsToString (.cons y ys)}"

instance [ToString α] : ToString (Vect α n) where
  toString : Vect α n → String
  | .nil => "[]"
  | .cons x xs => s!"[{(Vect.cons x xs).elementsToString}]"

#eval oregonianPeaks.zip danishPeaks

-- ## Vect.map

def Vect.map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

#eval (Vect.fromList [1, 2, 3]).map fun (x : Nat) => (-x : Int)

-- ## Vect.zipWith

def Vect.zipWith (f : α → β → γ) : Vect α n → Vect β n → Vect γ n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

#eval (Vect.fromList [1, 2, 3]).zipWith
  (fun (x : Nat) (y : Int) => x + 3 * y)
  (Vect.fromList [-1, -2, -3])

-- ## Vect.unzip

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) v =>
    let (xs, ys) := unzip v
    (.cons x xs, .cons y ys)

#eval [(1, "a"), (2, "b"), (3, "c")] |> Vect.fromList |>.unzip
#eval Vect.unzip <| Vect.fromList <| [(1, "a"), (2, "b"), (3, "c")]

-- ## Vect.snoc

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (snoc ys x)

#eval Vect.snoc (.cons "snowy" .nil) "peaks"

-- ## Vect.reverse

-- This version has quadratic complexity
def Vect.reverseSlow : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => snoc (reverseSlow xs) x

#eval (Vect.fromList ([] : List Nat)).reverseSlow
#eval (Vect.fromList ([1] : List Nat)).reverseSlow
#eval (Vect.fromList ([1, 2] : List Nat)).reverseSlow
#eval (Vect.fromList ([1, 2, 3] : List Nat)).reverseSlow

def plus_shift_one (n k : Nat) : n + (k + 1) = (n + 1) + k :=
  match k with
  | 0 => rfl (a := (n + 1))
  | k' + 1 => congrArg (· + 1) (plus_shift_one n k')

def Vect.reverseHelper (tail : Vect α n) (previous : Vect α k) : Vect α (k + n) :=
  match tail with
  | .nil => previous
  | .cons x xs => plus_shift_one k _ ▸ ((reverseHelper xs ((.cons x previous) : Vect α (k + 1))) : Vect α (k + 1 + _))

def plus_zero_n (n : Nat) : 0 + n = n :=
  match n with
  | 0 => rfl (a := 0)
  | k + 1 => congrArg (· + 1) (plus_zero_n k)

def Vect.reverse (v : Vect α n) : Vect α n :=
  plus_zero_n n ▸ reverseHelper v .nil

#eval (Vect.fromList ([] : List Nat)).reverse
#eval (Vect.fromList ([1] : List Nat)).reverse
#eval (Vect.fromList ([1, 2] : List Nat)).reverse
#eval (Vect.fromList ([1, 2, 3] : List Nat)).reverse

-- mathlib4 defines `Vect.reverse` in terms of `Vect.toList`,
-- but mathlib4 defines `Vect` as a subtype of `List`.
-- See [here](https://github.com/leanprover-community/mathlib4/blob/3d193da9516cf6a8ae8dd7a0f7fe1b7747b9250b/Mathlib/Data/Vector/Basic.lean#L243)

def Vect.toList : Vect α n → { x : List α // x.length = n }
  | .nil => ⟨[], by simp⟩
  | .cons x xs =>
    let { val := result, property := h } := toList xs
    ⟨ x :: result, by simp [h] ⟩

def list_reverse_length (xs : List α) : xs.reverse.length = xs.length := by simp

def Vect.reverseViaList (v : Vect α n) : Vect α n :=
  let { val := result, property := h } := v.toList
  let reversed : Vect α n := h ▸ (list_reverse_length result ▸ (Vect.fromList result.reverse))
  reversed

#eval (Vect.fromList ([] : List Nat)).reverseViaList
#eval (Vect.fromList ([1] : List Nat)).reverseViaList
#eval (Vect.fromList ([1, 2] : List Nat)).reverseViaList
#eval (Vect.fromList ([1, 2, 3] : List Nat)).reverseViaList

-- ## Vect.drop

-- Cheating: https://github.com/leanprover/fp-lean/blob/7eefe73cba60f23ab60cd1ad194c08d254e5ce42/examples/Examples/DependentTypes.lean#L294
-- The trick seems to be to explore possible valid cases
-- using pattern matching on both arguments simultaneously.
def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, v => v
  | j + 1, .cons _ xs => drop j xs

#eval danishPeaks.drop 2

-- ## Vect.take

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | j + 1, .cons x xs => .cons x (take j xs)

#eval danishPeaks.take 2

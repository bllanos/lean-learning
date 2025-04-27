-- # Examples

structure Fin2 (n : Nat) where
  val : Nat
  isLt : LT.lt val n

#eval (5 : Fin 8)

#eval (45 : Fin 10)

def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else
    none

def Array.find2 (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0

-- # Exercises

def Fin.next? : Fin n → Option (Fin n)
  | { val, isLt := _ } =>
    let next := val + 1
    if h : next < n then
      some ⟨next, h⟩
    else
      none

#eval (3 : Fin 8).next?

#eval (7 : Fin 8).next?

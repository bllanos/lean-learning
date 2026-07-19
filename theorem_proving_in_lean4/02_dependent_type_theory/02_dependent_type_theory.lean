-- # Examples

-- ## 2.1 Simple type theory

def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

-- #check: reports types
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

#eval 5 * 4
#eval m + 2
#eval b1 && b2

#check Nat → Nat
#check Nat -> Nat

#check Nat × Nat
#check Prod Nat Nat

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)

#check Nat × Nat → Nat
-- Equivalent to
#check (Nat × Nat) → Nat
#check (Nat → Nat) → Nat
-- Not equivalent to
#check Nat → Nat → Nat

#check Nat.succ
#check (0, 1)
#check Nat.add

#check Nat.succ 2
#check Nat.add 3
#check Nat.add 5 2
-- .n is a notation for .fst, .snd, etc.
#check (5, 9).1

#eval Nat.succ 2
#eval Nat.add 5 2
-- #eval Nat.add 3 -- Cannot synthesize `Repr` for type `Nat → Nat`
#eval (5, 9).1
#eval (5, 9).2

-- ## Types as objects

#check Nat
#check Bool
#check Nat → Bool
#check Nat × Bool
#check Nat → Nat
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat
#check Nat → Nat → Bool

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α
#check F α
#check F Nat
#check G α
#check G α β
#check G α Nat

#check Prod α β
#check α × β
#check Prod Nat Nat
#check Nat × Nat

#check List α
#check List Nat

#check Type -- Abbreviation for `Type 0`
#check Type 0
#check Type 1
#check Type 2
#check Type 3
#check Type 4

def t1 : Type 1 := Type 0
-- It seems that objects in a universe are not in higher universes.
-- def t2 : Type 2 := Type 0
def t2 : Sort 1 := Nat
def t3 : Sort 0 := True
#check Prop -- Type
def t4 : Type := Prop

-- Polymorphism over universes of types
#check List
-- List.{u} (α : Type u) : Type u
#check Prod
-- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

universe u
def F' (α : Type u) : Type u := Prod α α
#check F'
-- Leaving the universe level implicit
def F'' (α : Type v) : Type v := Prod α α
#check F''
-- Explicit universe level
def F'''.{w} (α : Type w) : Type w := Prod α α
#check F'''

-- ## 2.3 Function abstraction and evaluation

#check fun (x : Nat) => x + 5
#check λ (x : Nat) => x + 5
#check fun x => x + 5
#check λ x => x + 5

#eval (λ x : Nat => x + 5) 10

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

-- Identity on `Nat`
#check fun x : Nat => x
-- Constant function
#check fun _x : Nat => true
-- Composition
#check fun x : Nat => g (f x)
#check fun x => g (f x)

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => (g ∘ f) x
universe v
#check fun (α β γ : Type v) (g : β → γ) (f : α → β) (x : α) => (g ∘ f) x

#check (fun x : Nat => x) 1
#check (fun _x : Nat => true) 1

def f' (n : Nat) : String := toString n
def g' (s : String) : Bool := s.length > 0

#check (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => (u ∘ v) x) Nat String

#eval (fun x : Nat => x) 1
#eval (fun _x : Nat => true) 1

-- ## 2.4 Definitions

def double (x : Nat) : Nat := x + x
#eval double 3
def double' : Nat → Nat :=
  fun x => x + x
#eval double' 3
def double'' := fun (x : Nat) => x + x

def pi := 3.141592654
def add (x y : Nat) := x + y
#eval add 3 2

def add' (x : Nat) (y : Nat) := x + y
#eval add' (double 3) (7 + 9)

def greater (x y : Nat) :=
  if x > y then x
  else y

def doTwice (f : Nat → Nat) (x : Nat) : Nat := (f ∘ f) x
#eval doTwice double 2

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  (g ∘ f) x

def square (x : Nat) : Nat :=
  x * x
#eval compose Nat Nat Nat double square 3

-- ## 2.5 Local definitions

#check let y := 2 + 2; y * y
#eval let y := 2 + 2; y * y

def twice_double (x : Nat) : Nat :=
  let y := x + x; y * y
def twice_double' (x : Nat) : Nat :=
  let y := x + x
  y * y
#eval twice_double 2
#eval twice_double' 2

#check let y := 2 + 2; let z := y + y; z * z
#eval let y := 2 + 2; let z := y + y; z * z

def t (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2
/-
  def bar := (fun a => fun x : a => x + 2) Nat
-/
def bar := (fun (a : Type) {_h : (HAdd a Nat Nat)} => fun x : a => x + 2)
#check bar Nat 2
#check @bar Nat _ 2
#eval @bar Nat instHAdd 5

-- ## 2.6 Variables and sections

def compose' (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice' (α : Type) (h : α → α) (x : α) : α := h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α := h (h (h x))

variable (α β γ : Type)

def compose'' (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
def doTwice'' (h : α → α) (x : α) : α := h (h x)
def doThrice' (h : α → α) (x : α) : α := h (h (h x))

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose''' := g (f x)
def doTwice''' := h (h x)
def doThrice'' := h (h (h x))

#print compose'''
#print doTwice'''
#print doThrice''

section useful
  variable (α β γ : Type)
  variable (g' : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose4 := g' (f x) -- `g` is not in scope
  def doTwice4 := h (h x)
  def doThrice4 := h (h (h x))
end useful
-- def compose5 := g' (f x) -- `g'` is not in scope
def compose5 := g (f x) -- `g` is in scope

-- ## 2.7 Namespaces

namespace Foo
  def a : Nat := 5
  def fFoo (x : Nat) : Nat := x + 7
  def fa : Nat := fFoo a
  def ffa : Nat := fFoo (fFoo a)

  #check a
  #check fFoo
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a
-- #check fFoo
#check Foo.a
#check Foo.fFoo
#check Foo.fa
#check Foo.ffa

open Foo
#check a
#check fFoo
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

open List
#check nil
#check cons
#check map

namespace Foo2
  def a : Nat := 5
  def fFoo (x : Nat) : Nat := x + 7
  def fa : Nat := fFoo a

  namespace Bar
    def ffa : Nat := fFoo (fFoo a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo2

#check Foo2.fa
#check Foo2.Bar.ffa

open Foo2
#check fa
#check Bar.ffa

namespace Foo3
  def a : Nat := 5
  def fFoo (x : Nat) : Nat := x + 7
  def fa : Nat := fFoo a
end Foo3

#check Foo3.a
#check Foo3.fFoo

namespace Foo3
  def ffa : Nat := fFoo (fFoo a)
end Foo3

-- ## 2.8 What makes dependent type theory dependent?

def cons2 (α : Type) (a : α) (as : List α) : List α := List.cons a as
#check cons2
#check cons2 Nat
#check cons2 Bool

#check @List.cons
#check @List.nil
#check @List.length
#check @List.append

universe u2 v2
def f2 (α : Type u2) (β : α → Type v2) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩
def g2 (α : Type u2) (β : α → Type v2) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b
def h1 (x : Nat) : Nat :=
 (f2 Type (fun α => α) Nat x).2
#eval h1 5
#check f2 Type (fun α => α) Nat
def h2 (x : Nat) : Nat :=
  (g2 Type (fun α => α) Nat x).2
#eval h2 5

-- ## 2.9 Implicit arguments

universe u3
def Lst (α : Type u3) : Type u3 := List α
def Lst.cons (α : Type u3) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u3) : Lst α := List.nil
def Lst.append (α : Type u3) (as bs : Lst α) : Lst α := List.append as bs
#check Lst
#check Lst.cons
#check Lst.nil
#check Lst.append

#check Lst.cons Nat 0 (Lst.nil Nat)
def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)
#check Lst.append Nat as bs
#check Lst.cons _ 0 (Lst.nil _)
def as2 : Lst Nat := Lst.nil _
def bs2 : Lst Nat := Lst.cons _ 5 (Lst.nil _)
#check Lst.append _ as2 bs2

universe u4
def Lst2 (α : Type u4) : Type u4 := List α
def Lst2.cons {α : Type u4} (a : α) (as : Lst2 α) : Lst α := List.cons a as
def Lst2.nil {α : Type u4} : Lst2 α := List.nil
def Lst2.append {α : Type u4} (as bs : Lst2 α) : Lst2 α := List.append as bs

#check Lst2.cons 0 Lst2.nil
def as3 : Lst2 Nat := Lst2.nil
def bs3 : Lst2 Nat := Lst2.cons 5 Lst2.nil
#check Lst2.append as3 bs3

-- Same as `id` from the standard library
def ident.{u5} {α : Type u5} (x : α) := x
#check (ident)
#check ident 1
#check ident "hello"
#check @ident

section
  universe u5
  variable {α : Type u5}
  variable (x : α)
  def ident2 := x
end

#check ident2
#check ident2 4
#check ident2 "hello"

#check (List.nil)
#check (id)
#check (List.nil : List Nat)
#check (id : Nat → Nat)

#check 2
#check (2 : Nat)
#check (2 : Int)

#check id
#check (id)
#check (@id)
#check @id
#check @id Nat
#check @id Bool
#check id Bool
#check id (α := Bool)

#check @id Nat 1
#check @id Bool true

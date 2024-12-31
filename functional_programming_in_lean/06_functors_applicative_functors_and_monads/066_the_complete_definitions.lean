-- # Examples

class Functor2 (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)

def simpleConst (x : α) (_ : β) : α := x

#eval [1, 2, 3].map (simpleConst "same")

#check Function.const

class Functor3 (f : Type u → Type v) : Type (max (u + 1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
inductive Functor4 (f : Type u → Type v) : Type (max (u + 1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor4 f

-- ## Applicative

class Pure2 (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α

class Seq2 (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class SeqRight2 (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β

class SeqLeft2 (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class Applicative2 (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqRight f, SeqLeft f where
  map := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft := fun a b => Seq.seq (map (fun a' => (fun _ => a')) a) b
  -- fun a b => Seq.seq (Functor.map (Function.const _) a) b
  -- fun a b => Seq.seq ((fun x _ => x) <$> a) b)
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

-- ## Monad

class Bind2 (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class Monad2 (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map f x := bind x (Function.comp pure f)
  seq f x := bind f fun y =>
    Functor.map y (x ())
  seqLeft x y := bind x fun a =>
    bind (y ()) fun _ => pure a
  seqRight x y := bind x fun _ => y ()

-- # Exercises

-- ## 2 a)
-- Implementation of map from Applicative
-- map x y := Seq.seq (pure x) fun _ => y

-- Property:
-- map id y = y
-- Proof:
--   Seq.seq (pure id) fun _ => y
--   y -- By the Applicative contract

-- Property:
-- map (f ∘ g) y = map f (map g y)
-- Proof:
-- Seq.seq (pure (f ∘ g)) fun _ => y = Seq.seq (pure f) fun _ => (Seq.seq (pure g) fun _ => y)
-- (pure (f ∘ g)) <*> y = (pure f) <*> (pure g) <*> y
-- (pure (f ∘ g)) <*> y = (pure (f g)) <*> y -- By the Applicative contract
-- (pure (f ∘ g)) <*> y = (pure (f ∘ g)) <*> y

-- ## 2 b)
-- Implementation of map from Monad
-- map f x := bind x (Function.comp pure f)

-- Property:
-- map id y = y
-- Proof:
--   bind y (Function.comp pure id)
--   bind y fun a => pure (id a)
--   bind y fun a => pure a
--   bind y pure
--   y -- By the Monad contract

-- Property:
-- map (f ∘ g) y = map f (map g y)
-- Proof:
--   bind y (Function.comp pure (f ∘ g)) = bind (bind y (Function.comp pure g)) (Function.comp pure f)
--   bind y fun a => pure (f (g a)) = bind (bind y fun a => pure (g a)) fun a => pure (f a)
--   bind y fun a => pure (f (g a)) = bind y (fun a => bind ((fun a' => pure (g a')) a) (fun a' => pure (f a'))) -- By the Monad contract
--   bind y fun a => pure (f (g a)) = bind y (fun a => bind (pure (g a)) (fun a' => pure (f a')))
--   bind y fun a => pure (f (g a)) = bind y (fun a => ((fun a' => pure (f a')) (g a)) -- By the Monad contract
--   bind y fun a => pure (f (g a)) = bind y (fun a => pure (f (g a)))

-- ## 2 c)
-- Implementation of seq from Monad
-- seq f x := bind f fun y => Functor.map y (x ())

-- Property:
-- seq (pure id) (fun _ => v) = v
-- Proof:
--   bind (pure id) fun y => Functor.map y ((fun _ => v) ())
--   Functor.map id ((fun _ => v) ()) -- By the Monad contract
--   Functor.map id v
--   v

-- Property:
-- pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)
-- Proof:
-- pure Function.comp <*> u <*> v <*> w is
--   (bind
--     (bind
--       (bind (pure Function.comp) fun y =>
--         Functor.map y u)
--       fun y' => Functor.map y' v)
--     fun y'' => Functor.map y'' w)
--   (bind
--     (bind
--       Functor.map Function.comp u
--       fun y' => Functor.map y' v)
--     fun y'' => Functor.map y'' w) -- By the Monad contract
--
-- u <*> (v <*> w) is
--   bind
--     u
--     fun y =>
--       Functor.map y (bind v fun y' =>
--          Functor.map y' w)

-- At this point, I can reason intuitively that the sequences of function applications
-- are the same. To formally prove it, I might need to expand the definitions of Functor.map.

-- Property:
-- pure f <*> pure x = pure (f x)
-- Proof:
-- bind (pure f) fun y => Functor.map y (pure x) = pure (f x)
-- Functor.map f (pure x) = pure (f x) -- By the Monad contract
-- bind (pure x) (Function.comp pure f) = pure (f x) -- Definition of map
-- bind (pure x) (fun y => pure (f y)) = pure (f x)
-- pure (f x) = pure (f x) -- By the Monad contract

-- Property:
-- u <*> pure x = pure (fun f => f x) <*> u
-- Proof:
-- bind u fun y => Functor.map y (pure x) = bind (pure (fun f => f x)) fun y => Functor.map y u
-- bind u fun y => bind (pure x) (fun y' => pure (y y')) = bind (pure (fun f => f x)) fun y => bind u (fun y' => pure (y y')) -- Definition of map
-- bind u fun y => pure (y x) = bind u (fun y' => pure ((fun f => f x) y')) -- By the Monad contract
-- bind u fun y => pure (y x) = bind u fun y' => pure (y' x)

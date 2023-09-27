module Numbers where

open import Basics
open import ExtUni

_<_ : Nat -> Nat -> P
x < ze = `Zero
ze < su y = `One
su x < su y = x < y

Fin : Nat -> U
Fin n = `Nat `>< \ k -> `Pr (k < n)


_+N_ : Nat -> Nat -> Nat
ze   +N m = m
su n +N m = su (n +N m)

-- a little extra never hurt anybody
-- mulAdd n x s = n * x + s
mulAdd : Nat -> Nat -> Nat -> Nat
mulAdd ze     x s = s
mulAdd (su n) x s = x +N mulAdd n x s

_*N_ : Nat -> Nat -> Nat
x *N y = mulAdd x y ze

-- subtraction as a view
data InFin? (n : Nat) : Nat -> Set where
  inFin : (k : El (Fin n)) -> InFin? n (fst k)
  tooBigBy : (e : Nat) -> InFin? n (n +N e)

inFin? : (n m : Nat) -> InFin? n m
inFin? ze m          = tooBigBy m
inFin? (su n) ze     = inFin (ze , _)
inFin? (su n) (su m) with inFin? n m
inFin? (su n) (su .k) | inFin (k , kp) = inFin (su k , kp)
inFin? (su n) (su .(n +N e)) | tooBigBy e = tooBigBy e

substNatEq : (x y : Nat)(q : Pr (Eq `Nat `Nat x y))(P : Nat -> Set)
  -> P x -> P y
substNatEq ze ze q P px = px
substNatEq (su x) (su y) q P px = substNatEq x y q (su - P) px

data UnPlus (n : Nat) : Set where
  split+ : ((a b : Nat) -> Pr (Eq `Nat `Nat n (su a +N b)) -> UnPlus b) -> UnPlus n

unPlus : (n : Nat) -> UnPlus n
unPlus ze = split+ \ _ _ ()
unPlus (su n) with unPlus n
... | res@(split+ unp) = split+ \
  { ze b pf     -> substNatEq n b pf UnPlus res
  ; (su a) b pf -> unp a b pf }

data DivMod : Nat -> Nat -> Set where
  divBy0 : (n : Nat) -> DivMod n ze
  quotRem : {d : Nat}(q : Nat)(r : El (Fin d)) -> DivMod (mulAdd q d (fst r)) d

divMod' : (n d : Nat) -> UnPlus n -> DivMod n d
divMod' n ze r = divBy0 n
divMod' n (su d) r with inFin? (su d) n
divMod' .(fst k) (su d) r | inFin k = quotRem ze k
divMod' .(su d +N e) (su d) (split+ f) | tooBigBy e with divMod' e (su d) (f d e (refl `Nat (d +N e)))
divMod' .(su d +N (mulAdd q (su d) (fst r))) (su d) (split+ f) | tooBigBy ._ | quotRem q r
  = quotRem (su q) r

divMod : (n d : Nat) -> DivMod n d
divMod n d = divMod' n d (unPlus n)

reduce : (n : Nat) -> Nat -> El (Fin (su n))
reduce n k with divMod k (su n)
reduce n .(mulAdd q (su n) (fst r)) | quotRem q r = r


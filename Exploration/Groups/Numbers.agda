module Numbers where

-- needs refactored in terms of call graphs?

open import Basics
open import ExtUni
open import Reasoning

_<_ : Nat -> Nat -> P
x < ze = `Zero
ze < su y = `One
su x < su y = x < y

n<sun : (n : Nat) -> Pr (n < su n)
n<sun ze = _
n<sun (su n) = n<sun n

trans< : (i j k : Nat) -> Pr (i < j) -> Pr (j < k) -> Pr (i < k)
trans< ze (su j) (su k) p q = _
trans< (su i) (su j) (su k) p q = trans< i j k p q

Fin : Nat -> U
Fin n = `Nat `>< \ k -> `Pr (k < n)

_+N_ : Nat -> Nat -> Nat
ze   +N m = m
su n +N m = su (n +N m)

_+Nze : (n : Nat) -> Pr (Eq `Nat `Nat (n +N ze) n)
ze +Nze = _
su n +Nze = n +Nze

assoc+N : (i j k : Nat) -> Pr (Eq `Nat `Nat ((i +N j) +N k) (i +N (j +N k)))
assoc+N ze j k = refl `Nat (j +N k)
assoc+N (su i) j k = assoc+N i j k

tooBig< : (n e : Nat) -> Pr ((n +N e) < n) -> Zero
tooBig< (su n) e l = tooBig< n e l

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
  ; (su a) b pf -> unp a b pf
  }

data DivMod : Nat -> Nat -> Set where
  divBy0 : (n : Nat) -> DivMod n ze
  quotRem : {d : Nat}(q : Nat)(r : El (Fin d)) -> DivMod (mulAdd q d (fst r)) d

{-
data DivModR : (n d : Nat) -> DivMod n d -> Set where
  divModRd0 : {n : Nat} -> DivModR n ze (divBy0 n)
  divModStop : {d : Nat}{r@(k , _) : El (Fin (su d))} -> DivModR k (su d) (quotRem ze r)
  divModStep : {q d n m : Nat}{r@(k , _) : El (Fin (su d))}
    -> DivModR n (su d) (quotRem q r)
    -> Pr (Eq `Nat `Nat (su d +N n) m)
    -> DivModR m (su d) (quotRem (su q) r)
-}

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

{-
reducePlus : (n x : Nat) -> Pr (Eq (Fin (su n)) (Fin (su n))
  (reduce n (su n +N x)) (reduce n x))
reducePlus n x with inFin? n (n +N x)
... | z = {!!}

reduceMulAdd : (q n r : Nat) -> Pr (
  Eq (Fin (su n)) (Fin (su n))
    (reduce n (mulAdd q (su n) r)) (reduce n r))
reduceMulAdd ze n r = refl (Fin (su n)) (reduce n r)
reduceMulAdd (su q) n r = (_, <>) let open EQPRF `Nat in
  fst (reduce n (su n +N mulAdd q (su n) r)) -[ fst (reducePlus n (mulAdd q (su n) r)) >
  fst (reduce n (mulAdd q (su n) r)) -[ fst (reduceMulAdd q n r) >
  fst (reduce n r) [QED]
-}

finZero : (n : Nat) -> El (Fin (su n))
finZero n = 0 , _

finPlus : (n : Nat) -> El (Fin (su n) `> Fin (su n) `> Fin (su n))
finPlus n (x , _) (y , _) = reduce n (x +N y)

plusInverse : (n : Nat) -> El (Fin (su n)) -> El (Fin (su n))
plusInverse n (ze , p) = n , n<sun n
plusInverse (su n) (su i , p) with j , q <- plusInverse n (i , p)
  = j , trans< j (su n) (su (su n)) q (n<sun (su n))

plusAbsorbZero : (n : Nat)(x : El (Fin (su n))) ->
  Pr (Eq (Fin (su n)) (Fin (su n))(finPlus n (finZero n) x) x)
plusAbsorbZero n (x , p) with inFin? (su n) x
... | inFin (k , _) = refl `Nat k , _
... | tooBigBy e with () <- tooBig< n e p

{-
reduceLemma : (n : Nat)(i j : Nat) ->
  Pr (Eq (Fin (su n)) (Fin (su n))
      (finPlus n (reduce n i) (reduce n j))
      (reduce n (i +N j)))
reduceLemma n i j with divMod i (su n) | divMod j (su n)
reduceLemma n .(mulAdd qi (su n) ri) .(mulAdd qj (su n) rj) | quotRem qi (ri , ip) | quotRem qj (rj , jp) = {!!}
-}

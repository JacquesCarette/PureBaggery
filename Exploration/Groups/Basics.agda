module Basics where

--------------------------------------------------------------------
-- First, a lot of kit to get started

-- Using proof irrelevance keeps us from using details that we
-- should not care about. [Also brings in complications.]
record Hide (X : Set) : Set where
  constructor hide
  field
    .expose : X
open Hide public

mapHide : forall {S T} -> (S -> T) -> Hide S -> Hide T
mapHide f (hide s) = hide (f s)


--------------
-- empty, singleton and (exactly) 2 point set along with eliminator
data Zero' : Set where
Zero = Hide Zero'
naughtE : forall {k}{X : Set k } -> Zero -> X
naughtE (hide ())

record One : Set where constructor <>

data Two : Set where `0 `1 : Two
_<01>_ : forall {k}{P : Two -> Set k} -> P `0 -> P `1 -> (b : Two) -> P b
(p0 <01> p1) `0 = p0
(p0 <01> p1) `1 = p1
not : Two -> Two
not = `1 <01> `0

-- dependent sum, disjoint union (coproduct) and product
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_
_+_ _*_ : Set -> Set -> Set
S + T = Two >< \ { `0 -> S ; `1 -> T }
S * T = S >< \ _ -> T

{- -- if only this worked for U and P as nicely as it does for Set
module _ {I : Set} where
  _*:_ _-:>_ : (I -> Set) -> (I -> Set) -> (I -> Set)
  (P *: Q) i = P i * Q i
  (P -:> Q) i = P i -> Q i
  [_] <_> : (I -> Set) -> Set
  [ P ] = forall {i} -> P i
  < P > = _ >< P
-}

-- uncurry
/\_ : {S : Set}{T : S -> Set}{P : S >< T -> Set}
   -> ((s : S)(t : T s) -> P (s , t))
   -> (st : S >< T) -> P st
(/\ k) (s , t) = k s t

id : forall {k}{X : Set k} -> X -> X
id x = x

-- dependent function composition, pipe style
_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  -> C a (f a)
(f - g) a = g (f a)

flip : forall {i j k}{A : Set i}{B : Set j}{C : A -> B -> Set k}
  (f : (a : A)(b : B) -> C a b)
  (b : B)(a : A) -> C a b
flip f b a = f a b

-- Parallel application of a pair of functions onto a pair.
_>><<_ : forall {S S' : Set}{T : S -> Set}{T' : S' -> Set}
  (f : S -> S')(g : {s : S} -> T s -> T' (f s))
  -> (S >< T) -> (S' >< T')
(f >><< g) (s , t) = f s , g t

-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

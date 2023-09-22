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

--------------
-- empty, singleton and (exactly) 2 point set along with eliminator
data Zero' : Set where
Zero = Hide Zero'
record One : Set where constructor <>
data Two : Set where `0 `1 : Two
_<01>_ : forall {k}{P : Two -> Set k} -> P `0 -> P `1 -> (b : Two) -> P b
(p0 <01> p1) `0 = p0
(p0 <01> p1) `1 = p1

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

-- uncurry
/\_ : {S : Set}{T : S -> Set}{P : S >< T -> Set}
   -> ((s : S)(t : T s) -> P (s , t))
   -> (st : S >< T) -> P st
(/\ k) (s , t) = k s t

-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}
_+N_ : Nat -> Nat -> Nat
ze +N m = m
su n +N m = su (n +N m)


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

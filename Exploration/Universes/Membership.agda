module Membership where

open import String

open import Basics
open import Thinnings

-- we don't want this to be polymorphic
-- evidence of where a in L actually is
data _-in_ (a : String) : (L : List String) -> Set where
  ze : {as : List String} -> a -in (a ,- as)
  su : {b : String} {as : List String} -> a -in as -> a -in (b ,- as)

-- is a in L ?
_-In_ : (a : String) -> (L : List String) -> Set
a -In [] = Zero
a -In (x ,- l) with primStringEquality a x
... | `0 = a -In l
... | `1 = One

-- LATER: use these even more pervasively down below
-- mapping down an -in
zee : {x : String} {xs : List String} -> <: _-in (x ,- xs) :>
zee = _ , ze

-- could be golfed to _ >><< su
suu : {x : String} {xs : List String} -> <: _-in xs :> ->  <: _-in (x ,- xs) :>
suu (_ , i) = (_ , su i)

-- when we know a is in l, we can (fairly silently) get to know where something is
--  (which, magically, is going to be a, but we don't / can't promise that)
$ : (a : String) -> {l : List String} -> {_ : a -In l} -> <: _-in l :>
$ a {x ,- l} {p} with primStringEquality a x
... | `0 = suu ($ a {l} {p})
... | `1 = zee

-- remove the enum element being pointed at
_-bar_ : (xs : List String) -> <: _-in xs :>
  -> List String
(x ,- xs) -bar (_ , ze) = xs
(x ,- xs) -bar (_ , su i) = x ,- (xs -bar (_ , i))

-- show what remains was there in the first place
bar-subset : (xs : List String)(i : <: _-in xs :>)
  -> (xs -bar i) <= xs
bar-subset (x ,- xs) (_ , ze) = x ^- io
bar-subset (x ,- xs) (_ , su i) = x ,- bar-subset xs (_ , i)

thin-in : forall {x xs ys} -> x -in xs -> xs <= ys -> x -in ys
thin-in i (a ^- th) = su (thin-in i th)
thin-in ze (a ,- th) = ze
thin-in (su i) (a ,- th) = su (thin-in i th)


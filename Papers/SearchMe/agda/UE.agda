module UE where

open import Basics

open import String

UE = List String

-- we don't want this to be polymorphic
-- evidence of where a in L actually is
data _-in_ (a : String) : (L : List String) -> Set where
  ze : {as : List String} -> a -in (a ,- as)
  su : {b : String} {as : List String} -> a -in as -> a -in (b ,- as)

[_]E : UE -> Set
[ ts ]E = <: (_-in ts) :>


-- is a in L ?
_-In_ : (a : String) -> (L : List String) -> Set
a -In [] = Zero
a -In (x ,- l) with primStringEquality a x
... | `0 = a -In l
... | `1 = One

pattern zee = _ , ze
pattern suu i = _ , su i

-- could be golfed to _ >><< su
sus : {x : String} {xs : List String} -> <: _-in xs :> ->  <: _-in (x ,- xs) :>
sus (_ , i) = suu i


-- when we know a is in l, we can (fairly silently) get to know where something is
--  (which, magically, is going to be a, but we don't / can't promise that)
$ : (a : String) -> {l : List String} -> {_ : a -In l} -> <: _-in l :>
$ a {x ,- l} {p} with primStringEquality a x
... | `0 = sus ($ a {l} {p})
... | `1 = zee

_~E>_ : (ts : UE)(T : [ ts ]E -> Set) -> Set
data _-E>_ (ts : UE)(T : [ ts ]E -> Set) : Set where
  <_> : ts ~E> T -> ts -E> T
[] ~E> T = One
(t ,- ts) ~E> T = T zee * (ts -E> (sus - T))

\\E : {ts : UE}{T : [ ts ]E -> Set}
   -> ((x : [ ts ]E) -> T x)
   -> ts -E> T
\\E {[]} f = < <> >
\\E {t ,- ts} f = < f zee , \\E (sus - f) >

_$E_ : {ts : UE}{T : [ ts ]E -> Set}
   -> ts -E> T
   -> ((x : [ ts ]E) -> T x)
_$E_ {t ,- ts} < z , k > zee = z
_$E_ {t ,- ts} < z , k > (suu i) = k $E (_ , i)

infixl 20 _$E_

betaE : {ts : UE}{T : [ ts ]E -> Set}
   -> (f : (x : [ ts ]E) -> T x)
   -> (x : [ ts ]E) -> (\\E f $E x) ~ f x
betaE {t ,- ts} f zee = r~
betaE {t ,- ts} f (suu i) = betaE (sus - f) (_ , i)

etaE : {ts : UE}{T : [ ts ]E -> Set}
    -> (k : ts -E> T)
    -> (\\E \ i -> k $E i) ~ k
etaE {[]} < <> > = r~
etaE {t ,- ts} < z , k > = ((z ,_) - <_>) $~ etaE k

extE : {ts : UE}{T : [ ts ]E -> Set}
    -> (f g : (x : [ ts ]E) -> T x)
    -> ((x : [ ts ]E) -> f x ~ g x)
    -> \\E f ~ \\E g
extE {[]} f g q = r~
extE {t ,- ts} f g q =
  <_> $~ (R~ _,_ ~$~ q zee ~$~ extE _ _ (sus - q))

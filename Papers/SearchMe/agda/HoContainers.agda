module HoContainers where

open import Basics

infix 20 _<|_
record Container : Set1 where
  constructor _<|_
  field
    Sh : Set
    Po : Sh -> Set
open Container

infix 15 [_]^C
[_]^C : Container -> Set -> Set
[ S <| P ]^C X = S >< \ s -> P s -> X

data _^*_ (C : Container)(X : Set) : Set where
  #   : X -> C ^* X
  <_> : [ C ]^C (C ^* X) -> C ^* X

join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join (# t) = t
join < s , k > = < s , (\ p -> join (k p)) >

-- skip example

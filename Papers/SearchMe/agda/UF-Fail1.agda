module UF-Fail1 where

open import Basics

data UE : Set
[_]E : UE -> Set

data UE where -- pro tem
  `0 `1 `2 : UE

[ `0 ]E = Zero
[ `1 ]E = One
[ `2 ]E = Two

data UF : Set
[_]F : UF -> Set

data UF where
  `[_] : UE -> UF
  _`><_ : (S : UF)(T : [ S ]F -> UF) -> UF

-- skipping _`->_

[ `[ N ] ]F = [ N ]E
[ S `>< T ]F = [ S ]F >< \ s -> [ T s ]F

_-E>_ : (N : UE) -> ([ N ]E -> Set) -> Set
`0 -E> T = One
`1 -E> T = T <>
`2 -E> T = T `0 * T `1

_-F>_ : (N : UF) -> ([ N ]F -> Set) -> Set
`[ N ] -F> T = N -E> T
(R `>< S) -F> T = R -F> \ r -> S r -F> \ s -> T (r , s)

\\E : {N : UE}{T : [ N ]E -> Set}
   -> ((x : [ N ]E) -> T x)
   -> N -E> T
\\E {`0} f = <>
\\E {`1} f = f <>
\\E {`2} f = f `0 , f `1

_$E_ : {N : UE}{T : [ N ]E -> Set}
   -> N -E> T
   -> ((x : [ N ]E) -> T x)
_$E_ {`1} k x = k
_$E_ {`2} (a , b) `0 = a
_$E_ {`2} (a , b) `1 = b

\\F : {N : UF}{T : [ N ]F -> Set}
   -> ((x : [ N ]F) -> T x)
   -> N -F> T
\\F {`[ N ]} f = \\E {N} f
\\F {R `>< S} f = \\F {R} \ r -> \\F {S r} \ s -> f (r , s)

_$F_ : {N : UF}{T : [ N ]F -> Set}
   -> N -F> T
   -> ((x : [ N ]F) -> T x)
_$F_ {`[ N ]} k x = _$E_ {N} k x
_$F_ {R `>< S} k (r , s) = _$F_ {S r} (_$F_ {R} k r) s

-- skipping *internal* _`-F>_

infix 20 _<|_
record Fontainer : Set where
  constructor _<|_
  field
    Sh : UF
    Po : [ Sh ]F -> UF
open Fontainer

infix 15 [_]^F
[_]^F : Fontainer -> Set -> Set
[ S <| P ]^F X = [ S ]F >< \ s -> P s -F> \ _ -> X

data _^*_ (C : Fontainer)(X : Set) : Set where
  #   : X -> C ^* X
  <_> : [ C ]^F (C ^* X) -> C ^* X

{- THIS JOIN TYPECHECKS BUT DOESN'T TERMINATION-CHECK
join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join (# t) = t
join {C} < s , k > =
  < s , (\\F {C .Po s} \ p -> join (_$F_ {C .Po s} k p)) >
-}

data Problem : Set where
  base : Problem
  _-F<_ : (S : UF)(P : [ S ]F -> Problem) -> Problem

module _ {C : Fontainer} where

  module _ {X : Set} where
  
    data Rec : C ^* X -> Set where
      # : forall x -> Rec (# x)
      step : (s : [ C .Sh ]F)
         -> forall {k}
         -> (f : (p : [ C .Po s ]F) -> Rec (_$F_ {C .Po s} k p))
         -> Rec < s , k >

    Input : Problem -> Set
    Input base = C ^* X
    Input (S -F< P) = S -F> \ s -> Input (P s)

    Output : (P : Problem) -> Input P -> Set
    Output base t = Rec t
    Output (S -F< P) k = (s : [ S ]F) ->
      Output (P s) (_$F_ {S} k s)

    solve : (P : Problem)(i : Input P) -> Output P i
    solve base (# x) = # x
    solve base < s , k > = step s
      (solve (C .Po s -F< (\ _ -> base)) k)
    solve (`[ N ] -F< P) k = {!!}
    solve ((R `>< S) -F< P) k =
      /\ solve (R -F< \ r -> S r -F< \ s -> P (r , s)) k

    rec = solve base

joinr : forall {C X} -> (t : C ^* (C ^* X)) -> Rec t -> C ^* X
joinr (# t) (# t) = t
joinr {C} < s , k > (step s f) =
  < s , \\F {C .Po s} (\ p -> joinr (_$F_ {C .Po s} k p) (f p)) >

join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join ts = joinr ts (rec ts)

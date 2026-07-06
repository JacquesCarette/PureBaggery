module UF where

open import Basics
open import UE

data UF : Set
[_]F : UF -> Set

data UF where
  `[_] : UE -> UF
  _`><_ : (S : UF)(T : [ S ]F -> UF) -> UF

-- skipping _`->_

[ `[ N ] ]F = [ N ]E
[ S `>< T ]F = [ S ]F >< \ s -> [ T s ]F

_~F>_ : (S : UF)(T : [ S ]F -> Set) -> Set
data _-F>_ (S : UF)(T : [ S ]F -> Set) : Set where
  <_> : S ~F> T -> S -F> T
`[ N ] ~F> T = N  -E> T
(R `>< S) ~F> T = R -F> \ r -> S r -F> \ s -> T (r , s)

\\F : {S : UF}{T : [ S ]F -> Set}
   -> ((x : [ S ]F) -> T x)
   -> S -F> T
\\F {`[ N ]} f = < \\E f >
\\F {R `>< S} f = < (\\F \ r -> \\F \ s -> f (r , s)) >

_$F_ : {S : UF}{T : [ S ]F -> Set}
   -> S -F> T
   -> ((x : [ S ]F) -> T x)
_$F_ {`[ N ]} < k > x = k $E x
_$F_ {R `>< S} < k > (r , s) = k $F r $F s

infixl 30 _$F_

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

data Problem : Set where
  base : Problem
  _-F<_ : (S : UF)(P : [ S ]F -> Problem) -> Problem
  _-E<_ : (S : UE)(P : [ S ]E -> Problem) -> Problem

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
    Input (S -E< P) = S -E> \ s -> Input (P s)

    Output : (P : Problem) -> Input P -> Set
    Output base t = Rec t
    Output (S -F< P) k = (s : [ S ]F) ->
      Output (P s) (k $F s)
    Output (S -E< P) k = (s : [ S ]E) ->
      Output (P s) (k $E s)

    solve : (P : Problem)(i : Input P) -> Output P i
    
    solve base (# x) = # x
    solve base < s , k > = step s
      (solve (C .Po s -F< (\ _ -> base)) k)
      
    solve ((R `>< S) -F< P) < k > (r , s) =
      solve (R -F< \ r -> S r -F< \ s -> P (r , s)) k r s
    solve (`[ ts ] -F< P) < k > i =
      solve (ts -E< P) k i
      
    solve ([] -E< P) i (_ , ())
    solve ((t ,- ts) -E< P) < z , k > zee =
      solve (P zee) z
    solve ((t ,- ts) -E< P) < z , k > (suu i) =
      solve (ts -E< (sus - P)) k (_ , i)

    rec = solve base

joinr : forall {C X} -> (t : C ^* (C ^* X)) -> Rec t -> C ^* X
joinr (# t) (# t) = t
joinr < s , k > (step s f) =
  < s , (\\F \ p -> joinr (k $F p) (f p)) >

join : forall {C X} -> C ^* (C ^* X) -> C ^* X
join ts = joinr ts (rec ts)

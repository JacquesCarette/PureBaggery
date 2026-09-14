module Fontainer where

open import Basics
open import UE
open import UF

infix 20 _<|_
record Fontainer : Set where
  constructor _<|_
  field
    Sh : UF
    Po : [ Sh ]F -> UF
open Fontainer public

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


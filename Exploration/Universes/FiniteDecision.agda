module FiniteDecision where

open import Basics
open import Universes
open import Finite
open import TabulatedFunctions
open import Membership
open import String

-- Either we can prove them all, or get an actual witness of a counter-example
-- but first a helper for the String case
decideEnum : (xs : List String) -> (D : <: _-in xs :> -> Decision UDATA) -> Decision UDATA
decideEnum xs D .Naw = `F (`E xs) `>< \ x -> D x .Naw
decideEnum xs D .Aye = `E xs `#>> \ x -> D x .Aye
decideEnum xs D .exclude (x , p) f = D x .exclude p (ffapp (`E xs) f x)
decideEnum [] D .decide = `1 , < <> >
decideEnum (x ,- xs) D .decide with D zee .decide | decideEnum xs (suu - D) .decide
... | `0 , p | c , q = `0 , zee , p
... | `1 , p | `0 , i , q = `0 , suu i , q
... | `1 , p | `1 , < q > = `1 , < p , q >

decideAll : (T : UF) (D : ElF T -> Decision UDATA) -> Decision UDATA
decideAll T D .Naw = `F T `>< \ t -> D t .Naw
decideAll T D .Aye = T `#>> \ t -> D t .Aye
decideAll T D .exclude (t , p) f = D t .exclude p (ffapp T f t)
decideAll (S `>< T) D .decide with decideAll S (\ s -> decideAll (T s) \ t -> D (s , t)) .decide
... | `0 , s , t , n  = `0 , (s , t) , n
... | `1 , q = `1 , < q >
decideAll `0 D .decide = `1 , < <> >
decideAll `1 D .decide with D <> .decide
... | `0 , ans = `0 , <> , ans
... | `1 , ans = `1 , < ans >
decideAll (`E xs) D .decide = decideEnum xs D .decide

-- can we turn a Decision UPROPS into Decision UDATA ?
-- yes we can!
dataifyDecision : Decision UPROPS -> Decision UDATA
dataifyDecision D .Naw = `Prf (D .Naw)
dataifyDecision D .Aye = `Prf (D .Aye)
dataifyDecision D .decide = D .decide
dataifyDecision D .exclude = D .exclude

-- this special case may or may not be worth it
decideTab : (S : UF) (T : ElF S -> U Data) (D : (s : ElF S) (t : El (T s)) -> Decision UDATA) ->
  (f : S #> (T - El)) -> Decision UDATA
decideTab S T D f = decideAll S \ s -> D s (ffapp S f s)

module Leftovers where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import FiniteEq
open import TabulatedFunctions
open import Universes
open import Equality

-- Baby steps towards differential structure

bar-diff : (xs : List String)(i : <: _-in xs :>)
  -> (j : <: _-in (xs -bar i) :>)
  -> El (Enum-Eq xs i xs (_ , thin-in (snd j) (bar-subset xs i)))
  -> Zero
bar-diff (x ,- xs) (_ , su i) (_ , su j) q = 
  bar-diff xs (_ , i) (_ , j) q


{-
-- aha we may struggle to push this through for Sigma
me-or-not : (T : UF)(me : ElF T)(x : ElF T)
  -> ElF (`ctors (("self" , `1) ,- ("other" , T -sans me) ,- []))
me-or-not (S `>< T) (sme , tme) (sx , tx)
  with me-or-not S sme sx
... | (."self" , ze) , <> = {!!}
  -- want to call me-or-not (T sme) tme tx
  -- but need sme = sx
... | (."other" , su ze) , s'
  = $ "other" , $ "diffLeft" , s' , {!!} -- want tx but need coherence
me-or-not `1 <> <> = $ "self" , <>
me-or-not (`E xs) i j = {!!}
-}

-- we may have more luck showing
-- T -sans t  iso  to  T `>< \ t' -> t' /= t

sans-diff : (T : UF)(t : ElF T)(t' : ElF (T -sans t))
  -> El (EqF T t T (sans-embed T t t')) -> Zero
sans-diff (S `>< T) (s , t) ((."diffLeft" , ze) , s' , t') (q , _)
  = sans-diff S s s' q
sans-diff (S `>< T) (s , t) ((."diffRight" , su ze) , t') (_ , q)
  = sans-diff (T s) t t' q
sans-diff (`E xs) t t' q = bar-diff xs t t' q

-- the other direction is tricky

-- HEREAFTER, or rather not, we need transport and J to finish the job
{-
diff-sans : (T : UF)(t t' : ElF T)
  -> (El (EqF T t T t') -> Zero)
  -> ElF (T -sans t) >< \ t^ ->
     El (EqF T t' T (sans-embed T t t^))
diff-sans (S `>< T) (s , t) (s' , t') n
  with EqFDec S s S s' .decide
... | `0 , n' =
  let s^ , q = diff-sans S s s' n' in
  ($ "diffLeft" , s^ , {!!}) , {!!}
... | `1 , z = {!!}
diff-sans `1 t t' n with () <- n <>
diff-sans (`E x) t t' n = {!!}
-}

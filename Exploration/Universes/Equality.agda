module Equality where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import FiniteEq

List-Rel : {k : Kind} (T0 T1 : U k) (R : El T0 -> El T1 -> U Props)
  -> List (El T0) -> List (El T1) -> U Props
List-Rel T0 T1 R [] [] = `1
List-Rel T0 T1 R (x ,- xs) (y ,- ys) = R x y `/\ List-Rel T0 T1 R xs ys
List-Rel _ _ _ _ _ = `0 -- for once!

-- Propositional equality across the universes
-- Pious equality (true at different types)
--   (some cases are 'just true', left to catch-all, but commented out for
--    documentary evidence that that is what we meant)
{-# TERMINATING #-}
-- TODO: beat the termination checker
Eq : {k : Kind} (T0 : U k) -> El T0 -> (T1 : U k) -> El T1 -> U Props
-- forcing Agda to match on the types first to be lazier in the values;
-- otherwise EqDec chokes
Eq _ _ `0 _ = `1
Eq {Props} T0 t0 T1 t1 = `1 -- proofs are all equal, by fiat
Eq (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  Eq S0 s0 S1 s1 `/\ Eq (T0 s0) t0 (T1 s1) t1
-- Eq `1 <> `1 <> = `1
Eq (S0 `-> T0) f0 (S1 `-> T1) f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=> Eq (T0 s0) (f0 s0) (T1 s1) (f1 s1) 
Eq (S0 `#>> T0) f0 (S1 `#>> T1) f1 =
  ElF-Rel S0 S1 \ s0 s1 -> Eq (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)
Eq (`E xs) t0 (`E ys) t1 = Enum-Eq xs t0 ys t1
Eq (`List T0) ts0 (`List T1) ts1 = List-Rel T0 T1 (\ t0 t1 -> Eq T0 t0 T1 t1) ts0 ts1
-- in particular, strictness on (con s0 f0) must not stop the second Mu being found
Eq (`Mu I0 Sh0 Pos0 posix0 i0) (con s0 f0) (`Mu I1 Sh1 Pos1 posix1 i1) (con s1 f1) =
  Eq (Sh0 i0) s0 (Sh1 i1) s1
  `/\ ElF-Rel (Pos0 i0 s0) (Pos1 i1 s1) \ p0 p1 ->
        Eq (`Mu I0 Sh0 Pos0 posix0 (posix0 i0 s0 p0)) (ffapp (Pos0 i0 s0) f0 p0)
           (`Mu I1 Sh1 Pos1 posix1 (posix1 i1 s1 p1)) (ffapp (Pos1 i1 s1) f1 p1)
-- Eq (`Prf T0) t0 (`Prf T1) t1 
Eq _ _ _ _ = `1

HERELESSAFTER: use T2E, we hope

_<=>_ :  {k : Kind} (T0 T1 : U k) -> U Props
_<=>_ {Props} P0 P1 = (P0 `=> P1) `/\ (P1 `=> P0)
_<=>_ {_} (S0 `>< T0) (S1 `>< T1)
  =   (S0 <=> S1)
  `/\ {!!}
_<=>_ {_} `0 `0 = {!!}
_<=>_ {_} `1 `1 = {!!}
_<=>_ {_} (T0 `-> T) (T1 `-> T₁) = {!!}
_<=>_ {_} (S `#>> T) (S₁ `#>> T₁) = {!!}
_<=>_ {_} (`E x) (`E x₁) = {!!}
_<=>_ {_} (`List T0) (`List T1) = {!!}
_<=>_ {_} (`Prf T0) (`Prf T1) = {!!}
_ <=> _ = `0

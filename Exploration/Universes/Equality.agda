module Equality where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import FiniteEq

List-Rel : {k0 k1 : Kind} (T0 : U k0) (T1 : U k1) (R : El T0 -> El T1 -> U Props)
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
Eq : {k0 k1 : Kind} (T0 : U k0) -> El T0 -> (T1 : U k1) -> El T1 -> U Props
-- forcing Agda to match on the types first to be lazier in the values;
-- otherwise EqDec chokes
Eq _ _ `0 _ = `1
Eq {Props} {Props} T0 t0 T1 t1 = `1 -- proofs are all equal, by fiat
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


-- HERELESSAFTER: use T2E, we hope
-- helper for List String equality
Strings-Eq : List String -> List String -> U Props
Strings-Eq [] [] = `1
Strings-Eq [] (_ ,- _) = `0
Strings-Eq (_ ,- _) [] = `0
Strings-Eq (x ,- xs) (y ,- ys) = `So (primStringEquality x y) `/\ Strings-Eq xs ys

_<=>_ :  {k0 k1 : Kind} (T0 : U k0) (T1 : U k1) -> U Props
_<=>_ {Props} {Props} P0 P1 = (P0 `=> P1) `/\ (P1 `=> P0)
_<=>_ {_} (S0 `>< T0) (S1 `>< T1)
  =   (S0 <=> S1)
  `/\ (S0 `-> \ s0 -> S1 `-> \ s1 ->
  Eq S0 s0 S1 s1 `=> (T0 s0 <=> T1 s1))
_<=>_ {_} `0 `0 = `1
_<=>_ {_} `1 `1 = `1
_<=>_ {_} (S0 `-> T0) (S1 `-> T1)
  = (S1 <=> S0)
  `/\ (S1 `-> \ s1 -> S0 `-> \ s0 ->
  Eq S1 s1 S0 s0 `=> (T0 s0 <=> T1 s1))
_<=>_ {_} (S0 `#>> T0) (S1 `#>> T1)
  = (S1 =F= S0)
  `/\ (S1 `#>> \s1 -> S0 `#>> \ s0 -> EqF S1 s1 S0 s0 `=> (T0 s0 <=> T1 s1))
_<=>_ {_} (`E xs) (`E ys) = Strings-Eq xs ys
_<=>_ {_} (`List T0) (`List T1) = T0 <=> T1
_<=>_ {_} (`Mu I0 Sh0 Pos0 posix0 i0) (`Mu I1 Sh1 Pos1 posix1 i1)
  = (I0 <=> I1)
  `/\ (I0 `-> \ i0 -> I1 `-> \ i1 ->
      Eq I0 i0 I1 i1 `=>
          ((Sh0 i0 <=> Sh1 i1)
          `/\ (Sh0 i0 `-> \ sh0 -> Sh1 i1 `-> \ sh1 ->
              Eq (Sh0 i0) sh0 (Sh1 i1) sh1 `=>
                ((Pos1 i1 sh1 =F= Pos0 i0 sh0)
                `/\ ((Pos1 i1 sh1) `#>> \ p1 -> (Pos0 i0 sh0) `#>> \ p0 ->
                     EqF (Pos1 i1 sh1) p1 (Pos0 i0 sh0) p0 `=> Eq I0 (posix0 i0 sh0 p0) I1 (posix1 i1 sh1 p1))))))
  `/\ Eq I0 i0 I1 i1 
_<=>_ {_} (`Prf T0) (`Prf T1) = (T0 `=> T1) `/\ (T1 `=> T0)
_ <=> _ = `0

-- HERE
coeU :  {k0 k1 : Kind} (S : U k0) (T : U k1) -> El (S <=> T) -> El S -> El T

postulate
  cohU : {k0 k1 : Kind} (S : U k0) (T : U k1) -> (Q : El (S <=> T)) -> (s : El S) ->
      El (Eq S s T (coeU S T Q s))
      
coeU {Props} {Props} P0 P1 (f , _) p0 = f p0
coeU {Props} {Data} (P0 `>< T) (T₁ `>< T₂) Q s = {!!}
coeU {Props} {Data} `0 _ Q ()
coeU {Props} {Data} `1 `1 Q s = {!!}
coeU {Props} {Data} (S `#>> T) (S₁ `#>> T₁) Q s = {!!}
coeU {Props} {Data} (`Mu P0 Sh Pos posix x) (`Mu T Sh₁ Pos₁ posix₁ x₁) Q s = {!!}
coeU {Props} {Data} (`Prf P0) (`Prf T) Q s = {!!}
coeU {Props} {Extensional} S T Q s = {!!}
coeU {Data} {_} (S `>< T) (T₁ `>< T₂) Q s = {!!}
coeU {Data} {_} `1 `1 Q s = {!!}
coeU {Data} {_} (S `#>> T) (S₁ `#>> T₁) Q s = {!!}
coeU {Data} {_} (`E x) (`E x₁) Q s = {!!}
coeU {Data} {_} (`List S) (`List T) Q s = {!!}
coeU {Data} {_} (`Mu S Sh Pos posix x) (`Mu T Sh₁ Pos₁ posix₁ x₁) Q s = {!!}
coeU {Data} {_} (`Prf S) (`Prf T) Q s = {!!}
coeU {Extensional} {_} S T Q s = {!!}

{-
coeU {Props} {Props} P0 P1 (f , _) p0 = f p0
-- sadly, we will need to repeat ourselves, but at least off-diagonal computes away
coeU {Data} (S0 `>< T0) (S1 `>< T1) (P , f) (s0 , t0) =
  let s1 = coeU S0 S1 P s0 in
  s1 , {!!}
coeU {Data} `1 `1 Q s = <>
coeU {Data} (S0 `#>> T0) (S1 `#>> T1) (P , f) g = fflam S1 \ s1 ->
  let s0 = coeF S1 S0 P s1 in
  let t0 = ffapp S0 g s0 in
  let Q = ffapp S0 (ffapp S1 f s1) s0 (cohF S1 S0 P s1) in  
  coeU (T0 s0) (T1 s1) Q t0
coeU {Data} (`E xs) (`E ys) Q s = {!!}
coeU {Data} (`List S) (`List T) Q s = {!!}
coeU {Data} (`Mu I0 Sh0 Pos0 posix0 i0) (`Mu I1 Sh1 Pos1 posix1 i1) Q s = {!!}
coeU {Data} (`Prf S) (`Prf T) Q s = {!!}
coeU {Data} {Extensional} S T Q s = ?
coeU {Extensional} (S `>< T) (T₁ `>< T₂) Q s = {!!}
coeU {Extensional} `1 `1 Q s = <>
coeU {Extensional} (S0 `-> T0) (S1 `-> T1) (P , Q) f s1 = {!!}
coeU {Extensional} (S `#>> T) (S₁ `#>> T₁) Q s = {!!}
coeU {Extensional} (`E x) (`E x₁) Q s = {!!}
coeU {Extensional} (`List S) (`List T) Q s = {!!}
coeU {Extensional} (`Mu S Sh Pos posix x) (`Mu T Sh₁ Pos₁ posix₁ x₁) Q s = {!!}
coeU {Extensional} (`Prf S) (`Prf T) Q s = {!!}
-}

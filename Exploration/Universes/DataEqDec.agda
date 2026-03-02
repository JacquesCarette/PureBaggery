module DataEqDec where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import FiniteEq
open import Mu
open import Decided

EqDec : (T0 : U FO) (t0 : El T0) (T1 : U FO) (t1 : El T1) -> UD
EqDec (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) = EqDec S0 s0 S1 s1 `& EqDec (T0 s0) t0 (T1 s1) t1
EqDec `1 t0 `1 t1 = `1
EqDec (S0 `#>> T0) f0 (S1 `#>> T1) f1 = `Aa S0 (\s0 -> `Aa S1 (\ s1 -> `Aa (DF (EqF S0 s0 S1 s1))
  \ _ -> EqDec (T0 s0) (f0 $$ s0) (T1 s1) (f1 $$ s1)))
EqDec (`F T0) t0 (`F T1) t1 = EqF T0 t0 T1 t1
EqDec (`Mu T0 Sh0 Pos0 posix0 i0) t0 (`Mu T1 Sh1 Pos1 posix1 i1) t1 =
  MuEq i0 t0 i1 t1
  where
    open MUEQ (\ i0 s0 i1 s1 -> EqDec (Sh0 i0) s0 (Sh1 i1) s1)
EqDec (HOP>FO `^ T0) t0 (HOP>FO `^ T1) t1 = `1 -- yes, proofs are indeed equal
EqDec _ _ _ _ = `0 -- see if this is nicer than `1 ?

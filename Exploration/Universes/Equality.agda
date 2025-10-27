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

Eq : {k0 k1 : Kind} (T0 : U k0) -> El T0 -> (T1 : U k1) -> El T1 -> U Props
MuEq : {k0 k1 : Kind} {Ix0 : Set} {Sh0 : Ix0 -> U k0} {Pos0 : (i : Ix0) -> El (Sh0 i) -> UF}
  {posix0 : (i : Ix0) (s : El (Sh0 i)) (p : ElF (Pos0 i s)) -> Ix0}
  {Ix1 : Set} {Sh1 : Ix1 -> U k1} {Pos1 : (i : Ix1) -> El (Sh1 i) -> UF}
  {posix1 : (i : Ix1) (s : El (Sh1 i)) (p : ElF (Pos1 i s)) -> Ix1}
  (i0 : Ix0) {t0 : Mu Ix0 (Sh0 - El) Pos0 posix0 i0} (r0 : MuRec _ _ _ _ t0)
  (i1 : Ix1) {t1 : Mu Ix1 (Sh1 - El) Pos1 posix1 i1} (r1 : MuRec _ _ _ _ t1)
  -> U Props
-- forcing Agda to match on the types first to be lazier in the values;
-- otherwise EqDec chokes
Eq _ _ `0 _ = `1
-- but this causes trouble in coqU? refactor?
Eq {Props} {Props} T0 t0 T1 t1 = `1 -- proofs are all equal, by fiat
Eq (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  Eq S0 s0 S1 s1 `/\ Eq (T0 s0) t0 (T1 s1) t1
-- Eq `1 <> `1 <> = `1
Eq (S0 `-> T0) f0 (S1 `-> T1) f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=> Eq (T0 s0) (f0 s0) (T1 s1) (f1 s1) 
Eq (S0 `#>> T0) f0 (S1 `#>> T1) f1 =
  S0 `#>> \ s0 -> S1 `#>> \ s1 -> EqF S0 s0 S1 s1 `=> Eq (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)
Eq (`F E0) e0 (`F E1) e1 = EqF E0 e0 E1 e1
Eq (`List T0) ts0 (`List T1) ts1 = List-Rel T0 T1 (\ t0 t1 -> Eq T0 t0 T1 t1) ts0 ts1
-- in particular, strictness on (con s0 f0) must not stop the second Mu being found
Eq {k0} {k1} (`Mu I0 Sh0 Pos0 posix0 i0) t0 (`Mu I1 Sh1 Pos1 posix1 i1) t1 =
  MuEq {k0} {k1} {Sh0 = Sh0} {Sh1 = Sh1} i0 (muRec _ _ _ _ t0) i1 (muRec _ _ _ _ t1)
  {-
  Eq (Sh0 i0) s0 (Sh1 i1) s1
  `/\ ((Pos0 i0 s0) `#>> \ p0 -> (Pos1 i1 s1) `#>> \ p1 ->
        (EqF (Pos0 i0 s0) p0 (Pos1 i1 s1) p1) `=>
        Eq (`Mu I0 Sh0 Pos0 posix0 (posix0 i0 s0 p0)) (ffapp (Pos0 i0 s0) f0 p0)
           (`Mu I1 Sh1 Pos1 posix1 (posix1 i1 s1 p1)) (ffapp (Pos1 i1 s1) f1 p1))
  -}
-- Eq (`Prf T0) t0 (`Prf T1) t1 
Eq _ _ _ _ = `1

MuEq {k0} {k1} {Sh0 = Sh0} {Pos0 = Pos0} {Sh1 = Sh1} {Pos1 = Pos1} i0 (con s0 c0) i1 (con s1 c1) =
  Eq (Sh0 i0) s0 (Sh1 i1) s1
  `/\ ((Pos0 i0 s0) `#>> \ p0 -> (Pos1 i1 s1) `#>> \ p1 ->
        (EqF (Pos0 i0 s0) p0 (Pos1 i1 s1) p1) `=>
        MuEq {k0} {k1} {Sh0 = Sh0} {Sh1 = Sh1} _ (c0 p0) _ (c1 p1))

-- OFFICIAL TYPE EQUALITY (EXTENSIONAL FOR PROPOSITIONS)
_<=>_ :  {k0 k1 : Kind} (T0 : U k0) (T1 : U k1) -> U Props

-- STRUCTURAL TYPE COERCIBILITY
_<==>_ :  {k0 k1 : Kind} (T0 : U k0) (T1 : U k1) -> U Props


_<=>_ {Props} {Props} P0 P1 = (P0 `=> P1) `/\ (P1 `=> P0)
T0 <=> T1 = T0 <==> T1

(S0 `>< T0) <==> (S1 `>< T1)
  =   (S0 <==> S1)
  `/\ (S0 `-> \ s0 -> S1 `-> \ s1 ->
         Eq S0 s0 S1 s1 `=> (T0 s0 <==> T1 s1))
`0 <==> `0 = `1
`1 <==> `1 = `1
(S0 `-> T0) <==> (S1 `-> T1)
  =   (S1 <=> S0)
  `/\ (S1 `-> \ s1 -> S0 `-> \ s0 ->
         Eq S1 s1 S0 s0 `=> (T0 s0 <==> T1 s1))
(S0 `#>> T0) <==> (S1 `#>> T1)
  = (S1 =F= S0)
  `/\ (S1 `#>> \s1 -> S0 `#>> \ s0 ->
        EqF S1 s1 S0 s0 `=> (T0 s0 <==> T1 s1))
`F E0 <==> `F E1 = E0 =F= E1
`List T0 <==> `List T1 = T0 <==> T1
`Mu  I0 Sh0 Pos0 posix0 i0 <==> `Mu I1 Sh1 Pos1 posix1 i1
  = (I0 <==> I1)
  `/\ (I0 `-> \ i0 -> I1 `-> \ i1 ->
      Eq I0 i0 I1 i1 `=>
          ((Sh0 i0 <==> Sh1 i1)
          `/\ (Sh0 i0 `-> \ sh0 -> Sh1 i1 `-> \ sh1 ->
              Eq (Sh0 i0) sh0 (Sh1 i1) sh1 `=>
                ((Pos1 i1 sh1 =F= Pos0 i0 sh0)
                `/\ ((Pos1 i1 sh1) `#>> \ p1 -> (Pos0 i0 sh0) `#>> \ p0 ->
                     EqF (Pos1 i1 sh1) p1 (Pos0 i0 sh0) p0 `=> Eq I0 (posix0 i0 sh0 p0) I1 (posix1 i1 sh1 p1))))))
  `/\ Eq I0 i0 I1 i1 
`Prf P0 <==> `Prf P1 = P0 <=> P1
_ <==> _ = `0

coeU :  {k0 k1 : Kind} (S : U k0) (T : U k1) -> El (S <=> T) -> El S -> El T
cowU :  {k0 k1 : Kind} (S : U k0) (T : U k1) -> El (S <==> T) -> El S -> El T

postulate
  cohU : {k0 k1 : Kind} (S : U k0) (T : U k1) -> (Q : El (S <==> T)) -> (s : El S) ->
      El (Eq S s T (cowU S T Q s))

-- fix this name
  coqU : {k0 k1 : Kind} (S : U k0) (T : U k1) -> (Q : El (S <=> T)) -> (s : El S) ->
      El (Eq S s T (coeU S T Q s))

cowhU :  {k0 k1 : Kind} (S : U k0) (T : U k1)(Q : El (S <==> T))(s : El S)
     -> <: Eq S s T - El :>
cowhU S T Q s = cowU S T Q s , cohU S T Q s

coeqU : {k0 k1 : Kind} (S : U k0) (T : U k1) -> (Q : El (S <=> T)) -> (s : El S)
     -> <: Eq S s T - El :>
coeqU S T Q s = coeU S T Q s , coqU S T Q s

coeU {Props}       {Props}       P R (pr , _) p = pr p
coeU {Props}       {Data}        S T Q s = cowU S T Q s
coeU {Props}       {Extensional} S T Q s = cowU S T Q s
coeU {Data}        {_}           S T Q s = cowU S T Q s
coeU {Extensional} {_}           S T Q s = cowU S T Q s

cowU (S0 `>< T0) (S1 `>< T1) (QS , QT) (s0 , t0) =
  let s1 , sq = cowhU S0 S1 QS s0 in
  let t1 = cowU (T0 s0) (T1 s1) (QT s0 s1 sq) t0 in
  s1 , t1
cowU `1 `1 Q <> = <>
cowU (S0 `-> T0) (S1 `-> T1) (QS , QT) f0 s1 = 
  let s0 , sq = coeqU S1 S0 QS s1 in
  let t0 = f0 s0 in
  let t1 = cowU (T0 s0) (T1 s1) (QT s1 s0 sq) t0
  in t1
cowU (S0 `#>> T0) (S1 `#>> T1) (QS , QT) f0 = fflam S1 \ s1 ->
  let s0 , sq = coehF S1 S0 QS s1 in
  let t0 = ffapp S0 f0 s0 in
  let t1 = cowU (T0 s0) (T1 s1) (ffapp S0 (ffapp S1 QT s1) s0 sq) t0
  in t1
cowU (`F E0) (`F E1) Q x = coeF E0 E1 Q x
cowU (`List S) (`List T) Q = list (cowU S T Q)
cowU (`Mu I0 Sh0 Pos0 posix0 i0) (`Mu I1 Sh1 Pos1 posix1 i1) (QI , K0 , iq) t0 =
  help (muRec _ _ _ _ t0) iq
  where
  help : {i0 : El I0}{t0 : El (`Mu I0 Sh0 Pos0 posix0 i0)} ->
       MuRec (El I0) (Sh0 - El) Pos0 posix0 t0 ->
       {i1 : El (I1)}(iq : El (Eq I0 i0 I1 i1)) ->
       Mu (El I1) (Sh1 - El) Pos1 posix1 i1
  help (con s0 k0) iq = 
    let QSh , K1 = K0 _ _ iq in
    let s1 , sq = cowhU (Sh0 _) (Sh1 _) QSh s0 in
    let QPos , K2 = K1 s0 s1 sq in
    con s1 (fflam (Pos1 _ s1) \ p1 ->
      let p0 , pq = coehF (Pos1 _ s1) (Pos0 _ s0) QPos p1 in
      help (k0 p0) (ffapp (Pos0 _ s0) (ffapp (Pos1 _ s1) K2 p1) p0 pq)
    )
cowU (`Prf P) (`Prf R) (pr , _) p = pr p


postulate
  reflU : {k : Kind}(T : U k)(t : El T) -> El (Eq T t T t)
  RespUU : {k0 k1 : Kind}(S : U k0)(s0 s1 : El S)(q : El (Eq S s0 S s1))
    -> (T : (s1 : El S)(q : El (Eq S s0 S s1)) -> U k1)
    -> El (T s0 (reflU S s0) <=> T s1 q)

J-UU : {k0 k1 : Kind}(S : U k0)(s0 s1 : El S)(q : El (Eq S s0 S s1))
    -> (T : (s1 : El S)(q : El (Eq S s0 S s1)) -> U k1)
    -> El (T s0 (reflU S s0))
    -> El (T s1 q)
J-UU S s0 s1 q T = coeU (T s0 (reflU S s0)) (T s1 q) (RespUU S s0 s1 q T)


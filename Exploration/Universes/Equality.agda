module Equality where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions
open import Universes
open import FiniteEq
open import Decided
open import DataEqDec
open import Mu

Eq : {k : Kind} (T0 : U k)(t0 : El T0)(T1 : U k)(t1 : El T1) -> Props

module _
  {Ix0 : Set} {Sh0 : Ix0 -> Types} {Pos0 : (i : Ix0) -> El (Sh0 i) -> UF}
  {posix0 : (i : Ix0) (s : El (Sh0 i)) (p0 : ElF (Pos0 i s)) -> Ix0}
  {Ix1 : Set} {Sh1 : Ix1 -> Types} {Pos1 : (i : Ix1) -> El (Sh1 i) -> UF}
  {posix1 : (i : Ix1) (s : El (Sh1 i)) (p : ElF (Pos1 i s)) -> Ix1} where

  MuHoEqHelp :
         (i0 : Ix0) {m0 : Mu Ix0 (Sh0 - El) Pos0 posix0 i0} (r0 : MuRec m0)
         (i1 : Ix1) (m1 : Mu Ix1 (Sh1 - El) Pos1 posix1 i1) -> Props
  MuHoEqHelp i0 (con s0 r0) i1 (con s1 k1) = 
    Eq (Sh0 i0) s0 (Sh1 i1) s1 `/\
    (uf=>vl (Pos0 i0 s0) `-> \ p0 ->
     uf=>vl (Pos1 i1 s1) `-> \ p1 ->
     Forget (EqF (Pos0 i0 s0) p0 (Pos1 i1 s1) p1) `=>
     MuHoEqHelp _ (r0 p0) _ (k1 $$ p1))
         
  MuHoEq : (i0 : Ix0) (m0 : Mu Ix0 (Sh0 - El) Pos0 posix0 i0)
         (i1 : Ix1) (m1 : Mu Ix1 (Sh1 - El) Pos1 posix1 i1) -> Props
  MuHoEq i0 m0 = MuHoEqHelp i0 (muRec m0)

Eq {FO} T0 t0 T1 t1 = Forget (EqDec T0 t0 T1 t1)
Eq {HO Proof} T0 t0 T1 t1 = `1

Eq {HO Value} (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  Eq S0 s0 S1 s1 `/\ Eq (T0 s0) t0 (T1 s1) t1
Eq {HO Value} `1 t0 `1 t1 = `1
Eq {HO Value} (S0 `-> T0) f0 (S1 `-> T1) f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=> Eq (T0 s0) (f0 s0) (T1 s1) (f1 s1)
Eq {HO Value} (`Mu I0 S0 P0 pi0 i0) t0 (`Mu I1 S1 P1 pi1 i1) t1 = MuHoEq {Sh0 = S0}{Sh1 = S1} i0 t0 i1 t1
Eq {HO Value} (FO>HOV `^ T0) t0 (FO>HOV `^ T1) t1 = Eq T0 t0 T1 t1
Eq {HO Value} _ _ _ _ = `0  -- does this matter?

infix 30 _<=>_
_<=>_ : forall {k} -> U k -> U k -> Props
_<=T=>_ : Types -> Types -> Props
_<=D=>_ : U FO -> U FO -> Props
_<=>_ {FO} = _<=D=>_
_<=>_ {HO Value} = _<=T=>_
_<=>_ {HO Proof} P0 P1 = (P0 `=> P1) `/\ (P1 `=> P0)

(S0 `>< T0) <=T=> (S1 `>< T1) =
  (S0 <=> S1) `/\ 
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=>
  (T0 s0 <=> T1 s1)
`0 <=T=> `0 = `1
`1 <=T=> `1 = `1
(S0 `-> T0) <=T=> (S1 `-> T1) = 
  (S1 <=> S0) `/\ 
  S1 `-> \ s1 -> S0 `-> \ s0 -> Eq S1 s1 S0 s0 `=>
  (T0 s0 <=> T1 s1)
`Mu I0 S0 P0 pi0 i0 <=T=> `Mu I1 S1 P1 pi1 i1 = 
  I0 <=> I1 `/\ Eq I0 i0 I1 i1 `/\ I0 `-> \ i0 -> I1 `-> \ i1 -> Eq I0 i0 I1 i1 `=>
  S0 i0 <=> S1 i1 `/\ S0 i0 `-> \ s0 -> S1 i1 `-> \ s1 -> Eq (S0 i0) s0 (S1 i1) s1 `=>
  Forget (P1 i1 s1 =F= P0 i0 s0) `/\ 
  uf=>vl (P1 i1 s1) `-> \ p1 -> uf=>vl (P0 i0 s0) `-> \ p0 ->
  Forget (EqF (P1 i1 s1) p1 (P0 i0 s0) p0) `=>
  Eq I0 (pi0 i0 s0 p0) I1 (pi1 i1 s1 p1)
(x `^ T0) <=T=> (FO>HOV `^ T1) with FO>HOV <- x = T0 <=> T1
_ <=T=> _ = `0

(S0 `>< T0) <=D=> (S1 `>< T1) = 
  (S0 <=> S1) `/\ vl S0 `-> \ s0 -> vl S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=>
  (T0 s0 <=> T1 s1)
`0 <=D=> `0 = `1
`1 <=D=> `1 = `1
(S0 `#>> T0) <=D=> (S1 `#>> T1) = 
  Forget (S1 =F= S0) `/\ 
  uf=>vl S1 `-> \ s1 -> uf=>vl S0 `-> \ s0 -> Forget (EqF S1 s1 S0 s0) `=>
  (T0 s0 <=> T1 s1)
`F T0 <=D=> `F T1 = Forget (T0 =F= T1)
`Mu I0 S0 P0 pi0 i0 <=D=> `Mu I1 S1 P1 pi1 i1 = 
  I0 <=> I1 `/\ Eq I0 i0 I1 i1 `/\ I0 `-> \ i0 -> I1 `-> \ i1 -> Eq I0 i0 I1 i1 `=>
  S0 i0 <=> S1 i1 `/\ vl (S0 i0) `-> \ s0 -> vl (S1 i1) `-> \ s1 -> Eq (S0 i0) s0 (S1 i1) s1 `=>
  Forget (P1 i1 s1 =F= P0 i0 s0) `/\ 
  uf=>vl (P1 i1 s1) `-> \ p1 -> uf=>vl (P0 i0 s0) `-> \ p0 ->
  Forget (EqF (P1 i1 s1) p1 (P0 i0 s0) p0) `=>
  Eq I0 (pi0 i0 s0 p0) I1 (pi1 i1 s1 p1)
(x `^ T0) <=D=> (HOP>FO `^ T1) with HOP>FO <- x = T0 <=> T1
_ <=D=> _ = `0


coeU :  {k : Kind} (S T : U k) -> El (S <=> T) -> El S -> El T
coeT :  (S T : Types) -> El (S <=> T) -> El S -> El T
coeD :  (S T : U FO) -> El (S <=> T) -> El S -> El T

coeU {FO} = coeD
coeU {HO Value} = coeT
coeU {HO Proof} P R (pr , rp) p = pr p

postulate
  cohU :  {k : Kind} (S T : U k)(Q : El (S <=> T))(s : El S) ->
    El (Eq S s T (coeU S T Q s))

coehU :  {k : Kind} (S T : U k)(Q : El (S <=> T))(s : El S) ->
  <: Eq S s T - El :>
coehU S T Q s = coeU S T Q s , cohU S T Q s


coeT (S0 `>< T0) (S1 `>< T1) (QS , QT) (s0 , t0) =
  let s1 , sq = coehU S0 S1 QS s0 in
  s1 , coeU (T0 s0) (T1 s1) (QT s0 s1 sq) t0
coeT `1 `1 Q <> = <>
coeT (S0 `-> T0) (S1 `-> T1) (QS , QT) f0 s1 = 
  let s0 , sq = coehU S1 S0 QS s1 in
  coeU (T0 s0) (T1 s1) (QT s1 s0 sq) (f0 s0)
coeT (`Mu I0 S0 P0 pi0 i0) (`Mu I1 S1 P1 pi1 i1) (IQ , iq , kQ) =
  muXForm i0 i1 iq
  where
    _~_ : El I0 -> El I1 -> Set
    i0 ~ i1  = El (Eq I0 i0 I1 i1)
    sh : (i0 : El I0)(i1 : El I1) -> i0 ~ i1 -> El (S0 i0) -> El (S1 i1)
    sh i0 i1 iq =
      let SQ , lQ = kQ i0 i1 iq in
      coeU (S0 i0) (S1 i1) SQ
    po : (i0 : El I0)(i1 : El I1)(iq : i0 ~ i1)(s0 : El (S0 i0)) ->
      ElF (P1 i1 (sh i0 i1 iq s0)) -> ElF (P0 i0 s0)
    po i0 i1 iq s0 =
      let SQ , lQ = kQ i0 i1 iq in
      let s1 , sq = coehU (S0 i0) (S1 i1) SQ s0 in
      let PQ , mQ = lQ s0 s1 sq in
      coeF (P1 i1 s1) (P0 i0 s0) (Recall (P1 i1 s1 =F= P0 i0 s0) PQ)
    pi~ : (i0 : El I0)(i1 : El I1)(iq : i0 ~ i1)(s0 : El (S0 i0))
          (p1 : ElF (P1 i1 (sh i0 i1 iq s0))) ->
          pi0 i0 s0 (po i0 i1 iq s0 p1) ~ pi1 i1 (sh i0 i1 iq s0) p1
    pi~ i0 i1 iq s0 p1 =
      let SQ , lQ = kQ i0 i1 iq in
      let s1 , sq = coehU (S0 i0) (S1 i1) SQ s0 in
      let PQ , mQ = lQ s0 s1 sq in
      let p0 , pq = coehF (P1 i1 s1) (P0 i0 s0) (Recall (P1 i1 s1 =F= P0 i0 s0) PQ) p1 in
      mQ p1 p0 (forget (EqF (P1 i1 s1) p1 (P0 i0 s0) p0) pq)
    open MUXFORM {El I0}{S0 - El}{P0}{pi0}{El I1}{S1 - El}{P1}{pi1} _~_ sh po pi~
coeT (FO>HOV `^ S) (FO>HOV `^ T) Q s = coeU S T Q s

coeD (S0 `>< T0) (S1 `>< T1) (QS , QT) (s0 , t0) =
  let s1 , sq = coehU S0 S1 QS s0 in
  s1 , coeU (T0 s0) (T1 s1) (QT s0 s1 sq) t0
coeD `1 `1 Q <> = <>
coeD (S0 `#>> T0) (S1 `#>> T1) (QS , QT) f0 = \\ \ s1 ->
  let s0 , sq = coehF S1 S0 (Recall (S1 =F= S0) QS) s1 in
  coeU (T0 s0) (T1 s1) (QT s1 s0 (forget (EqF S1 s1 S0 s0) sq)) (f0 $$ s0)
coeD (`F T0) (`F T1) Q t0 = coeF T0 T1 (Recall (T0 =F= T1) Q) t0
coeD (`Mu I0 S0 P0 pi0 i0) (`Mu I1 S1 P1 pi1 i1) (IQ , iq , kQ) =
  muXForm i0 i1 iq
  where
    _~_ : El I0 -> El I1 -> Set
    i0 ~ i1  = El (Eq I0 i0 I1 i1)
    sh : (i0 : El I0)(i1 : El I1) -> i0 ~ i1 -> El (S0 i0) -> El (S1 i1)
    sh i0 i1 iq =
      let SQ , lQ = kQ i0 i1 iq in
      coeU (S0 i0) (S1 i1) SQ
    po : (i0 : El I0)(i1 : El I1)(iq : i0 ~ i1)(s0 : El (S0 i0)) ->
      ElF (P1 i1 (sh i0 i1 iq s0)) -> ElF (P0 i0 s0)
    po i0 i1 iq s0 =
      let SQ , lQ = kQ i0 i1 iq in
      let s1 , sq = coehU (S0 i0) (S1 i1) SQ s0 in
      let PQ , mQ = lQ s0 s1 sq in
      coeF (P1 i1 s1) (P0 i0 s0) (Recall (P1 i1 s1 =F= P0 i0 s0) PQ)
    pi~ : (i0 : El I0)(i1 : El I1)(iq : i0 ~ i1)(s0 : El (S0 i0))
          (p1 : ElF (P1 i1 (sh i0 i1 iq s0))) ->
          pi0 i0 s0 (po i0 i1 iq s0 p1) ~ pi1 i1 (sh i0 i1 iq s0) p1
    pi~ i0 i1 iq s0 p1 =
      let SQ , lQ = kQ i0 i1 iq in
      let s1 , sq = coehU (S0 i0) (S1 i1) SQ s0 in
      let PQ , mQ = lQ s0 s1 sq in
      let p0 , pq = coehF (P1 i1 s1) (P0 i0 s0) (Recall (P1 i1 s1 =F= P0 i0 s0) PQ) p1 in
      mQ p1 p0 (forget (EqF (P1 i1 s1) p1 (P0 i0 s0) p0) pq)
    open MUXFORM {El I0}{S0 - El}{P0}{pi0}{El I1}{S1 - El}{P1}{pi1} _~_ sh po pi~
coeD (HOP>FO `^ S) (HOP>FO `^ T) Q s = coeU S T Q s

postulate
  reflU : {k : Kind}(T : U k)(t : El T) -> El (Eq T t T t)
  RespUU' : {k0 k1 : Kind}(S : U k0)(s0 s1 : El S)(q : El (Eq S s0 S s1))
    -> (T : El S -> U k1)
    -> El (T s0 <=> T s1)

RespUU : {k0 k1 : Kind}(S : U k0)(s0 s1 : El S)(q : El (Eq S s0 S s1))
    -> (T : (s1 : El S)(q : El (Eq S s0 S s1)) -> U k1)
    -> El (T s0 (reflU S s0) <=> T s1 q)
RespUU {FO} {k1} S s0 s1 q T =
  RespUU' (S `>< (λ s1 -> pf (Eq S s0 S s1))) (s0 , reflU S s0) (s1 , q) (q , <>)
    \ (s , q) -> T s q
RespUU {HO Value} {k1} S s0 s1 q T =
  RespUU' (S `>< (λ s1 -> pf (Eq S s0 S s1))) (s0 , reflU S s0) (s1 , q) (q , <>)
    \ (s , q) -> T s q
RespUU {HO Proof} {k1} S s0 s1 q T =
    RespUU' (S `>< (λ s1 -> pf (Eq S s0 S s1))) (s0 , reflU S s0) (s1 , q) <>
    \ (s , q) -> T s q

J-UU : {k0 k1 : Kind}(S : U k0)(s0 s1 : El S)(q : El (Eq S s0 S s1))
    -> (T : (s1 : El S)(q : El (Eq S s0 S s1)) -> U k1)
    -> El (T s0 (reflU S s0))
    -> El (T s1 q)
J-UU S s0 s1 q T = coeU (T s0 (reflU S s0)) (T s1 q) (RespUU S s0 s1 q T)

module Mu where

open import Basics
open import Membership
open import Finite
open import TabulatedFunctions
open import FiniteEq
open import Decided

module _ (Ix : Set) (Sh : Ix -> Set) (Pos : (i : Ix) -> Sh i -> UF)
  (posix : (i : Ix) (s : Sh i) (p : ElF (Pos i s)) -> Ix)
  where

  -- indexed containers (with finite sets of positions)
  data Mu  (i : Ix) : Set where
    con : (s : Sh i) -> (Pos i s #> \ p -> Mu (posix i s p)) -> Mu i

module _ {Ix : Set} {Sh : Ix -> Set} {Pos : (i : Ix) -> Sh i -> UF}
  {posix : (i : Ix) (s : Sh i) (p : ElF (Pos i s)) -> Ix}
  where
  
  -- proof of recursiveness is a Pi type, but the data is not
  data MuRec {i : Ix} : Mu Ix Sh Pos posix i -> Set where
    con : (s : Sh i){k : Pos i s #> \ p -> Mu Ix Sh Pos posix (posix i s p)}
       -> ((p : ElF (Pos i s)) -> MuRec (k $$ p))
       -> MuRec (con s k)

  -- lots of work needed to expose what we know to the termination
  -- checker
  data PoStack : Set where
    poNil : Ix -> PoStack
    poCons : (S : UF)(T : ElF S -> PoStack) -> PoStack

  ElPo : PoStack -> Set
  ElPo (poNil i) = Mu Ix Sh Pos posix i
  ElPo (poCons S T) = S #> \ s -> ElPo (T s) 

  ElPoRec : (stk : PoStack) -> ElPo stk -> Set
  ElPoRec (poNil i) x = MuRec x
  ElPoRec (poCons S T) k = (s : ElF S) -> ElPoRec (T s) (ffapp S k s)  

  muRec : {i : Ix}(x : Mu Ix Sh Pos posix i) -> MuRec x
  elPoRec : (p : PoStack)(x : ElPo p) -> ElPoRec p x
  muRecWork : (P : UF)(pstk : ElF P -> PoStack) (k : P #> (pstk - ElPo))
              (p : ElF P)
           -> ElPoRec (pstk p) (ffapp P k p)
  elPoTupRec : forall xs (pstk : ElF (`E xs) -> PoStack)
               (k : `E xs #> (pstk - ElPo)) (p : ElF (`E xs))
         ->  ElPoRec (pstk p) (ffapp (`E xs) k p)

  muRec {i} (con s k) = con s (muRecWork (Pos _ s) (posix _ s - poNil) k)
  elPoRec (poNil i) x = muRec x
  elPoRec (poCons S T) k = muRecWork S T k
  muRecWork (S `>< T) pstk < k > (s , t) = muRecWork S (\ s -> poCons (T s) \ t -> pstk (s , t)) k s t
  muRecWork `1 pstk < k > <> = elPoRec (pstk <>) k
  muRecWork (`E xs) pstk k p = elPoTupRec xs pstk k p
  elPoTupRec [] pstk k (_ , ())
  elPoTupRec (x ,- xs) pstk < j , _ > (_ , ze) = elPoRec (pstk zee) j
  elPoTupRec (x ,- xs) pstk < _ , k > (_ , su i) = elPoTupRec xs (suu - pstk) < k > (_ , i)

module _ {Ix : Set}{Sh0 Sh1 : Ix -> Set}(f : (i : Ix) -> Sh1 i -> Sh0 i)
       -- at every index we know how to transform 1-shapes into 0-shapes
       {Pos : (i : Ix) -> Sh0 i -> UF}
       {posix : (i : Ix) (s : Sh0 i) (p : ElF (Pos i s)) -> Ix}
  where

  shunWork : 
         {i : Ix}
         -- and now we extend that to Recursive data
      -> {x : Mu Ix Sh1 (\ i s1 -> Pos i (f i s1)) (\ i s1 p -> posix i (f i s1) p) i}
      -> MuRec x
      -> Mu Ix Sh0 Pos posix i
  shunWork (con sh xs) = con (f _ sh) (fflam (Pos _ (f _ sh)) \ p -> shunWork (xs p))

  shun : {i : Ix}
         -- and now we extend that to recursive data
      -> Mu Ix Sh1 (\ i s1 -> Pos i (f i s1)) (\ i s1 p -> posix i (f i s1) p) i
      -> Mu Ix Sh0 Pos posix i
  shun x = shunWork (muRec x)

-- Equality
module MUEQ
  {Ix0 : Set} {Sh0 : Ix0 -> Set} {Pos0 : (i : Ix0) -> Sh0 i -> UF}
  {posix0 : (i : Ix0) (s : Sh0 i) (p0 : ElF (Pos0 i s)) -> Ix0}
  {Ix1 : Set} {Sh1 : Ix1 -> Set} {Pos1 : (i : Ix1) -> Sh1 i -> UF}
  {posix1 : (i : Ix1) (s : Sh1 i) (p : ElF (Pos1 i s)) -> Ix1}
  (ShEq : (i0 : Ix0) (s0 : Sh0 i0) (i1 : Ix1) (s1 : Sh1 i1) -> UD) where

  MuEqHelp :
         (i0 : Ix0) {m0 : Mu Ix0 Sh0 Pos0 posix0 i0} (r0 : MuRec m0)
         (i1 : Ix1) (m1 : Mu Ix1 Sh1 Pos1 posix1 i1) -> UD
  MuEqHelp i0 (con s0 r0) i1 (con s1 k1) = ShEq i0 s0 i1 s1 `&
    `Aa (Pos0 i0 s0) (\ p0 -> `Aa (Pos1 i1 s1) (\ p1 -> `Aa (DF (EqF (Pos0 i0 s0) p0 (Pos1 i1 s1) p1))
      \ _ -> MuEqHelp _ (r0 p0) _ (k1 $$ p1))) 
         
  MuEq : (i0 : Ix0) (m0 : Mu Ix0 Sh0 Pos0 posix0 i0)
         (i1 : Ix1) (m1 : Mu Ix1 Sh1 Pos1 posix1 i1) -> UD
  MuEq i0 m0 = MuEqHelp i0 (muRec m0)

module MUXFORM
  {Ix0 : Set} {Sh0 : Ix0 -> Set} {Pos0 : (i : Ix0) -> Sh0 i -> UF}
  {posix0 : (i : Ix0) (s : Sh0 i) (p0 : ElF (Pos0 i s)) -> Ix0}
  {Ix1 : Set} {Sh1 : Ix1 -> Set} {Pos1 : (i : Ix1) -> Sh1 i -> UF}
  {posix1 : (i : Ix1) (s : Sh1 i) (p : ElF (Pos1 i s)) -> Ix1}
  (_~_ : Ix0 -> Ix1 -> Set)
  (sh : (i0 : Ix0)(i1 : Ix1) -> i0 ~ i1 -> Sh0 i0 -> Sh1 i1)
  (po : (i0 : Ix0)(i1 : Ix1)(iq : i0 ~ i1)(s0 : Sh0 i0) ->
    ElF (Pos1 i1 (sh i0 i1 iq s0)) -> ElF (Pos0 i0 s0))
  (pi~ : (i0 : Ix0)(i1 : Ix1)(iq : i0 ~ i1)(s0 : Sh0 i0)
         (p1 : ElF (Pos1 i1 (sh i0 i1 iq s0))) ->
         posix0 i0 s0 (po i0 i1 iq s0 p1) ~ posix1 i1 (sh i0 i1 iq s0) p1)
  where

  muXFormHelp : (i0 : Ix0)(i1 : Ix1) -> i0 ~ i1 ->
    {t : Mu Ix0 Sh0 Pos0 posix0 i0} -> MuRec t -> Mu Ix1 Sh1 Pos1 posix1 i1
  muXFormHelp i0 i1 iq (con s0 r0) =
    con (sh i0 i1 iq s0)
        (\\ \ p1 -> muXFormHelp _ _ (pi~ i0 i1 iq s0 p1) (r0 (po i0 i1 iq s0 p1)))
  
  muXForm : (i0 : Ix0)(i1 : Ix1) -> i0 ~ i1 ->
    Mu Ix0 Sh0 Pos0 posix0 i0 -> Mu Ix1 Sh1 Pos1 posix1 i1
  muXForm i0 i1 iq = muRec - muXFormHelp i0 i1 iq

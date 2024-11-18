module Fin where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Algebras
open import Iso
open import Numbers

{- -- gone to live in ExtUni.agda
_<_ : Nat -> Nat -> P
x < ze = `Zero
ze < su y = `One
su x < su y = x < y

Fin : Nat -> U
Fin n = `Nat `>< \ i -> `Pr (i < n)
-}

-- Fin's relation with _+_
finL : (n m : Nat) -> El (Fin n `> Fin (n +N m))
finL n m (i , p) = i , slackR i n m p where
  slackR : (i n m : Nat) -> Pr ((i < n) `=> (i < (n +N m)))
  slackR ze (su n) m p = <>
  slackR (su i) (su n) m p = slackR i n m p

finR : (n m : Nat) -> El (Fin m `> Fin (n +N m))
finR n m (i , p) = (n +N i) , shiftL n i m p where
  shiftL : (n i m : Nat) -> Pr ((i < m) `=> ((n +N i) < (n +N m)))
  shiftL ze i m p = p
  shiftL (su n) i m p = shiftL n i m p

finCase : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> ((j : El (Fin n)) -> El (F (finL n m j)))
  -> ((k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin (n +N m))) -> El (F i)
finCase ze m F fl fr = fr
finCase (su n) m F fl fr (ze , p) = fl (ze , <>)
finCase (su n) m F fl fr (su i , p) = finCase n m ((su >><< id) - F)
  ((su >><< id) - fl)
  fr
  (i , p)

finCaseL : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> (l : (j : El (Fin n)) -> El (F (finL n m j)))
  -> (r : (k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin n)) -> Pr (Oq (F (finL n m i)) (finCase n m F l r (finL n m i)) (l i))
finCaseL (su n) m F l r (ze , <>) = refl (F (finL (su n) m (ze , <>))) (l (ze , <>))
finCaseL (su n) m F l r (su i , p) = finCaseL n m ((su >><< id) - F)
  ((su >><< id) - l)
  r
  (i , p)

finCaseR : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> (l : (j : El (Fin n)) -> El (F (finL n m j)))
  -> (r : (k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin m)) -> Pr (Oq (F (finR n m i)) (finCase n m F l r (finR n m i)) (r i))
finCaseR ze m F l r ip = refl (F ip) (r ip)
finCaseR (su n) m F l r = finCaseR n m ((su >><< id) - F)
  ((su >><< id) - l)
  r

-- Automorphisms of Fin
FinAut : Nat -> U
FinAut n = Fin n <=> Fin n

FinEn : Nat -> U
FinEn n = Fin n `> Fin n

-- iso between internal _+_ (numbers) and external `+ (types)
module FINSUMADD (n m : Nat) where
  finSumAdd : Fin (n +N m) <==> (Fin n `+ Fin m)
  fwd finSumAdd = finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_)
  bwd finSumAdd = /\ (finL n m <01> finR n m)
  fwd-bwd finSumAdd = finCase n m (\ s -> `Pr (Oq (Fin (n +N m)) (bwd finSumAdd (fwd finSumAdd s)) s))
    (\ j -> let open EQPRF (Fin (n +N m)) in vert (
            (bwd finSumAdd (finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) (finL n m j)))
              ==[ congB (Fin n `+ Fin m) {fwd finSumAdd (finL n m j)} {`0 , j}
                      (bwd finSumAdd) (finCaseL n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) j ) >
            (bwd finSumAdd (`0 , j))
              ==[ reflB >
             finL n m j [==]))
    \ k -> let open EQPRF (Fin (n +N m)) in vert (
            (bwd finSumAdd (finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) (finR n m k)))
              ==[ congB (Fin n `+ Fin m) {fwd finSumAdd (finR n m k)} {`1 , k}
                      (bwd finSumAdd) (finCaseR n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) k ) >
            (bwd finSumAdd (`1 , k))
              ==[ reflB >
             finR n m k [==])
  bwd-fwd finSumAdd (`0 , j) = finCaseL n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) j
  bwd-fwd finSumAdd (`1 , k) = finCaseR n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) k

-- combining two FinAut isos
module FINSUMAUT (n m : Nat) where
  open FINSUMADD n m

  finCaseAut : El (FinAut n `> FinAut m `> FinAut (n +N m))
  finCaseAut f g = osi (
    Fin (n +N m) =[ finSumAdd >
    Fin n `+ Fin m =[ sgIso `Two (iso' f <01> iso' g) >
    Fin n `+ Fin m < finSumAdd ]=
    Fin (n +N m) [ISO])


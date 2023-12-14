module FreeGroup where

open import ExtUni
open import Group
open import Basics
open import List
open import Quotient

module _ (X : U) where

  open Group.Group
  open Equiv

  postulate -- moving the goalposts
    FGQ : El (List (`Two `* X)) -> El (List (`Two `* X)) -> U
      -- equivalence closure of the congruence closure of inverse cancellation
    eqFGQ : Equiv (El (List (`Two `* X))) (\ ss ts -> Pr (`In (FGQ ss ts)))
      -- postulate equivalence closure
    catfgq : (ls ss ts : El (List (`Two `* X)))
        -> Hide (El (FGQ ss ts)) -> El (FGQ (cat _ ls ss) (cat _ ls ts))
    fgqcat : (ss ts rs : El (List (`Two `* X)))
        -> Hide (El (FGQ ss ts)) -> El (FGQ (cat _ ss rs) (cat _ ts rs))
    invcal : (b : Two)(x : El X) -> El (FGQ (the _ (b , x)) (the _ (not b , x)))
        

  FreeGroupCarrier : U
  FreeGroupCarrier = `Quotient
    (List (`Two `* X))  -- `0 for not inverted; `1 for inverted
    (\ ss ts -> `In (FGQ ss ts))
    eqFGQ

  FreeGroup : Group FreeGroupCarrier
  neu FreeGroup = `[ nil _ ]
  inv FreeGroup = {!!}
  mul FreeGroup cxs cys =
    elElim FreeGroupCarrier cxs
      (\ _ -> FreeGroupCarrier)
      ((\ xs -> elElim FreeGroupCarrier cys
        (\ _ -> FreeGroupCarrier)
        ( (\ ys -> `[ cat _ xs ys ])
        , \ as bs q -> hide
           ( cat (`Two `* X) xs as
           , cat (`Two `* X) xs as
           , eqR eqFGQ (cat (`Two `* X) xs as) 
           , refl (List (`Two `* X)) (cat (`Two `* X) xs as)
           , hide (catfgq xs as bs q))
        ))
      , \ as bs q -> hide
           ( _
           , _
           , eqR eqFGQ _ 
           , refl (List (`Two `* X)) _
           , hide (fgqcat as bs _ q))
      )
  mulneu- FreeGroup = {!!}
  mulmul- FreeGroup = {!!}
  mulinv- FreeGroup = {!!}

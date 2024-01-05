module FreeGroup where

open import ExtUni
open import Group
open import Basics
open import List
open import Quotient
open import Reasoning

module _ (X : U) where

  open EQPRF (List (`Two `* X))

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
    invcal : (b : Two)(x : El X) -> El (FGQ (cat _ (the _ (b , x)) (the _ (not b , x))) (nil _) )
    revfgq : (ss ts : El (List (`Two `* X)))
        -> Hide (El (FGQ ss ts)) -> El (FGQ (rev _ ss) (rev _ ts))
    listfgq : (f : El ((`Two `* X) `> (`Two `* X)))
              (ss ts : El (List (`Two `* X)))
           -> ((b : Two)(x : El X) -> El (FGQ (cat _ (the _ (f (b , x))) (the _ (f (not b , x)))) (nil _)))
           -> Hide (El (FGQ ss ts))
           -> El (FGQ (list (`Two `* X) (`Two `* X) f ss) (list (`Two `* X) (`Two `* X) f ts))

  eqQ-FGQ : {xs ys : El (List (`Two `* X))}
         -> Pr (Eq (List (`Two `* X)) (List (`Two `* X)) xs ys)
         -> Pr (`In (FGQ xs ys))
  eqQ-FGQ {xs}{ys} q = eqQ (List _) (\ xs ys -> `In (FGQ xs ys)) eqFGQ xs ys q

  open EQUIVPRF (List _) (\ xs ys -> `In (FGQ xs ys)) eqFGQ 

  invcal' : (b : Two)(x : El X) -> El (FGQ (cat _ (the _ (not b , x)) (the _ (b , x))) (nil _) )
  invcal' `0 x = invcal `1 x
  invcal' `1 x = invcal `0 x


  FreeGroupCarrier : U
  FreeGroupCarrier = `Quotient
    (List (`Two `* X))  -- `0 for not inverted; `1 for inverted
    (\ ss ts -> `In (FGQ ss ts))
    eqFGQ

  FreeGroup : Group FreeGroupCarrier
  neu FreeGroup = `[ nil _ ]
  inv FreeGroup cxs = 
    elElim FreeGroupCarrier cxs
      (\ _ -> FreeGroupCarrier)
      ( (\ xs -> `[ list _ _ (not >><< id) (rev _ xs) ] )
      , \ as bs q -> homogTac FreeGroupCarrier _ _
         (hide (listfgq (not >><< id) _ _ (not - invcal)
           (hide (revfgq as bs q))))
      )
  mul FreeGroup cxs cys =
    elElim FreeGroupCarrier cxs
      (\ _ -> FreeGroupCarrier)
      ((\ xs -> elElim FreeGroupCarrier cys
        (\ _ -> FreeGroupCarrier)
        ( (\ ys -> `[ cat _ xs ys ])
        , \ as bs q -> homogTac FreeGroupCarrier _ _ (hide (catfgq xs as bs q))
        ))
      , \ as bs q -> homogTac FreeGroupCarrier _ _ (hide (fgqcat as bs _ q))
      )
  mulneu- FreeGroup cxs = elElim FreeGroupCarrier cxs
    (\ cxs -> `Pr
      (Eq FreeGroupCarrier FreeGroupCarrier
        (mul FreeGroup (neu FreeGroup) cxs) cxs))
    ( (\ xs -> homogTac FreeGroupCarrier _ _ (eqQ-FGQ (nilcat _ xs)))
    , _)
  mulmul- FreeGroup cxs cys czs = elElim FreeGroupCarrier cxs
    (\ cxs -> `Pr
       (Eq FreeGroupCarrier FreeGroupCarrier
         (mul FreeGroup (mul FreeGroup cxs cys) czs)
         (mul FreeGroup cxs (mul FreeGroup cys czs))))
    ( (\ xs -> elElim FreeGroupCarrier cys
        (\ cys -> `Pr
           (Eq FreeGroupCarrier FreeGroupCarrier
             (mul FreeGroup (mul FreeGroup `[ xs ] cys) czs)
             (mul FreeGroup `[ xs ] (mul FreeGroup cys czs))))
        ( (\ ys -> elElim FreeGroupCarrier czs
            (\ czs -> `Pr
               (Eq FreeGroupCarrier FreeGroupCarrier
                 (mul FreeGroup (mul FreeGroup `[ xs ] `[ ys ]) czs)
                 (mul FreeGroup `[ xs ] (mul FreeGroup `[ ys ] czs))))
            ( (\ zs -> homogTac FreeGroupCarrier _ _
                (eqQ-FGQ (catcat _ xs ys zs)))
            , _ ))
        , _ ))
      , _ )
  mulinv- FreeGroup cxs = elElim FreeGroupCarrier cxs
    (\ cxs -> `Pr
      (Eq FreeGroupCarrier FreeGroupCarrier
        (mul FreeGroup (inv FreeGroup cxs) cxs) (neu FreeGroup)))
    ( (\ xs -> homogTac FreeGroupCarrier _ _
      (listElim _ xs (\ xs -> `Pr (`In (FGQ (cat _ (list _ _ _ (rev _ xs)) xs) (nil _))))
         (eqQ-FGQ (
            cat _ (list _ _ (not >><< id) (rev _ (nil _))) (nil _)
              -[ catnil _ _ >
            list _ _ (not >><< id) (rev _ (nil _))
              -[ cong (list _ _ (not >><< id)) (revnil _) >
            list _ _ (not >><< id) (nil _)
              -[ listnil >
            nil _ [QED]))
         \ s ss ssh -> 
            cat _ (list _ _ (not >><< id) (rev _ (cat _ (the _ s) ss))) (cat _ (the _ s) ss)
              ~[ eqQ-FGQ (
                   cat _ (list _ _ (not >><< id) (rev _ (cat _ (the _ s) ss))) (cat _ (the _ s) ss)
                     -[ cong (\ xs -> cat _ (list _ _ _ xs) (cat _ (the _ s) ss)) (revcat _ _ _) >
                   cat _ (list _ _ (not >><< id) (cat _ (rev _ ss) (rev _ (the _ s)))) (cat _ (the _ s) ss)
                     -[ cong (\ xs -> cat _ xs (cat _ (the _ s) ss)) listcat >
                   cat _ (cat _ (list _ _ (not >><< id) (rev _ ss)) (list _ _ (not >><< id) (rev _ (the _ s)))) (cat _ (the _ s) ss)
                     -[ cong (\ xs -> cat _ (cat _ _ (list _ _ _ xs)) (cat _ (the _ s) ss)) (revthe _ s) >
                   cat _ (cat _ (list _ _ (not >><< id) (rev _ ss)) (list _ _ (not >><< id) (the _ s))) (cat _ (the _ s) ss)
                     -[ cong (\xs -> cat _ (cat _ _ xs) (cat _ (the _ s) ss)) listthe >
                   cat _ (cat _ (list _ _ (not >><< id) (rev _ ss)) (the _ ((not >><< id) s))) (cat _ (the _ s) ss)
                     -[ catcat _ _ _ _ >
                   cat _ (list _ _ (not >><< id) (rev _ ss)) (cat _ (the _ ((not >><< id) s)) (cat _ (the _ s) ss))
                     < cong (cat _ _) (catcat _ _ _ _) ]-
                   cat _ (list _ _ (not >><< id) (rev _ ss))
                     (cat _ (cat _ (the _ ((not >><< id) s)) (the _ s))
                        ss)
                     [QED]  
              ) >
            cat _ (list _ _ (not >><< id) (rev _ ss))
              (cat _ (cat _ (the _ ((not >><< id) s)) (the _ s))
                ss)
              ~[ hide (catfgq _ _ _ (hide (fgqcat _ _ _ (hide (invcal' _ _))))) >
            cat _ (list _ _ (not >><< id) (rev _ ss)) (cat _ (nil _) ss)
              ~[ eqQ-FGQ (cong (cat _ _) (nilcat _ ss)) >
            cat _ (list _ _ (not >><< id) (rev _ ss)) ss
              ~[ ssh >
            nil _
              [qed]))
    , _ )


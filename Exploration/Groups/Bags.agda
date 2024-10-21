{-# OPTIONS --allow-unsolved-metas #-}
module Bags where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Algebras
open import ProductsForAlgebras
open import Actions as ACT -- to deal with a name conflict
open import Iso
open import GroupsWeLike
open import ActionsWeLike
open import Numbers
open import Fin
open import Containers
open import ContainersWeLike
open import Representables
open import RepresentablesWeLike
open import GroupHomsWeLike

BagC : ContainerDesc
Shape BagC = `Nat
Store BagC n = JumbleR (Fin n)

Bag : U -> U
Bag = [ BagC ]C -- `Nat `>< \ n -> Jumble (Fin n) X


module _ (X : U) where

  open EQPRF X
  open _=CtrD=>_
  open _=Action=>_
  open _=Repr=>_
  open _=Group=>_
  open _=Monoid=>_
  open _=SemiGroup=>_

  nilBCM : OneC =CtrD=> BagC
  shape=> nilBCM _ = 0
  carrier=> (groupAct=> (store<= nilBCM _)) = snd
  mor (semigroup=> (monoid=> (group=> (groupAct=> (store<= nilBCM _))))) _ = id , id , (snd - naughtE) , (snd - naughtE)
  mul-pres (semigroup=> (monoid=> (group=> (groupAct=> (store<= nilBCM _))))) _ _ = (snd - naughtE) , (snd - naughtE) , _
  neu-pres (monoid=> (group=> (groupAct=> (store<= nilBCM _)))) = (snd - naughtE) , (snd - naughtE) , _
  act-pres (groupAct=> (store<= nilBCM _)) = _

  nilB : El (Bag X)
  nilB = [ nilBCM ]C=> X (_ , `[ naughtE ])
  -- 0 , `[ snd - naughtE ]

  oneBCM : IC =CtrD=> BagC
  shape=> oneBCM _ = 1
  carrier=> (groupAct=> (store<= oneBCM _)) = _
  mor (semigroup=> (monoid=> (group=> (groupAct=> (store<= oneBCM _))))) _ =
    id , id , (\ { (ze , p) -> _ }) , \ { (ze , p) -> _ }
  mul-pres (semigroup=> (monoid=> (group=> (groupAct=> (store<= oneBCM _))))) _ _ =
    (\ { (ze , _) (ze , _) -> _ }) , (\ { (ze , _) (ze , _) -> _ }) , _
  neu-pres (monoid=> (group=> (groupAct=> (store<= oneBCM _)))) =
    (\ { (ze , _) (ze , _) -> _ }) , (\ { (ze , _) (ze , _) -> _ }) , _
  act-pres (groupAct=> (store<= oneBCM _)) = _

  oneB : El (X `> Bag X)
  oneB x = [ oneBCM ]C=> X (_ , `[ kon x ])
  -- oneB x = 1 , `[ (\ _ -> x) ]

  catBCM : (BagC *C BagC) =CtrD=> BagC
  shape=> catBCM (l , r) = l +N r
  groupAct=> (store<= catBCM (l , r)) = want
    {-record { groupAct=> = (groupHomActionMor {!!} _ -Action- {!!}) -Action- ({!isoActionHom<= (invIso' (FINSUMADD.finSumAdd l r)) paos!}) }-}
    -- likely need to show that Fin (l +N r) <=> Fin l `+ Fin r
    -- round-trips
    {-record { groupAct=> = record
    { carrier=> = finCase l r (\ _ -> Fin l `+ Fin r) (`0 ,_) (`1 ,_)
    ; group=> = record { monoid=> = record
      { semigroup=> = record
        { mor = \ z -> {!!} -- id , id , (\ x -> refl `Nat (fst x) , _) , (\ x -> refl `Nat (fst x) , _)
        ; mul-pres = {!!} -- \ a b -> (\ _ _ -> id) , (\ _ _ -> id) , _
        }
      ; neu-pres = {!!} -- (\ _ _ -> id) , (\ _ _ -> id) , _
      } }
    ; act-pres = \ x h -> {!finCaseAut lg rg!}
    } } -}
    where
      --open FINSUMAUT l r
      open FINSUMADD l r
      paos : ACTION.Action (Automorphism (Fin l) *Group* Automorphism (Fin r)) (Fin l `+ Fin r)
      paos = pairActsOnSum (Automorphism (Fin l)) (Automorphism (Fin r)) (AutAct (Fin l)) (AutAct (Fin r))
      step0 : AutAct (Fin (l +N r)) =Action=>
              isoAction (Automorphism (Fin l) *Group* Automorphism (Fin r))
              paos (invIso' finSumAdd)
      step0 = record { carrier=> = id
                     ; group=> = {!groupPairHomAutSum (Automorphism (Fin l)) (Automorphism (Fin r))!}
                     ; act-pres = {!!} }
      -- HERE
      {-
      step1 : AutAct (Fin (l +N r)) =Action=>
              isoAction (Automorphism (Fin (l +N r))) (AutAct (Fin (l +N r))) finSumAdd
      step1 = isoActionHom=> _ (AutAct (Fin (l +N r))) finSumAdd
      step2 : isoAction (Automorphism (Fin (l +N r))) (AutAct (Fin (l +N r))) finSumAdd
               =Action=>
              isoAction (Automorphism (Fin l) *Group* Automorphism (Fin r))
              paos (invIso' finSumAdd)
      step2 = record { carrier=> = {!!} ; group=> = {!!} ; act-pres = {!!} }
      -}
      step3 : isoAction (Automorphism (Fin l) *Group* Automorphism (Fin r))
              paos (invIso' finSumAdd)
              =Action=> paos
      step3 = isoActionHom<= _ paos (invIso' finSumAdd)
      want : AutAct (Fin (l +N r)) =Action=> paos
      want = step0 -Action- step3

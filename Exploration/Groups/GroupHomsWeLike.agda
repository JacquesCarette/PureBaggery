module GroupHomsWeLike where

open import Basics
open import ExtUni
open import Reasoning
open import Iso
open import Algebras
open import ProductsForAlgebras
open import GroupsWeLike
open import Actions

module _ {G : U}{GG : Group G} where
 open ACTION GG
 open _=Group=>_
 open _=Monoid=>_
 open _=SemiGroup=>_

 module _ {X : U}(AX : Action X) where

  open EQPRF X
  open Action AX

  open Group GG

  actionsPermuteIso : El G -> X <==> X
  fwd (actionsPermuteIso g) x = act x g
  bwd (actionsPermuteIso g) x = act x (inv g)
  fwd-bwd (actionsPermuteIso g) x = vert (
    (act (act x g) (inv g)) < bleu (act-mul _ _ _) ]==
    act x (mul g (inv g)) ==[ bleu (act-eq-neu _ _ (mul-inv _)) >
    x [==])
  bwd-fwd (actionsPermuteIso g) x = vert (
    (act (act x (inv g)) g) < bleu (act-mul _ _ _) ]==
    act x (mul (inv g) g) ==[ bleu (act-eq-neu _ _ (mulinv- _)) >
    x [==])

  ActionsPermute : GG =Group=> Automorphism X
  mor (semigroup=> (monoid=> ActionsPermute)) g =
    osi (actionsPermuteIso g)
  mul-pres (semigroup=> (monoid=> ActionsPermute)) g h =
    eqIso {X}{X}
      (osi (actionsPermuteIso (mul g h)))
      (osi (compIso' (actionsPermuteIso g) (actionsPermuteIso h)))
      \ x -> act-mul x g h
  neu-pres (monoid=> ActionsPermute) = 
    eqIso {X}{X} (osi (actionsPermuteIso neu)) (idIso X)
      \ x -> act-neu x

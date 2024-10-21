module GroupHomsWeLike where

open import Basics
open import ExtUni
open import Reasoning
open import Iso
open import Algebras
open import ProductsForAlgebras
open import GroupsWeLike

module _ {X Y : U}(GX : Group X)(GY : Group Y) where

  open _=Group=>_
  open _=Monoid=>_
  open _=SemiGroup=>_
  open Group

  groupPairSumIso : El X -> El Y -> (X `+ Y) <==> (X `+ Y)
  fwd (groupPairSumIso x y) (`0 , x') = `0 , mul GX x' x
  fwd (groupPairSumIso x y) (`1 , y') = `1 , mul GY y' y
  bwd (groupPairSumIso x y) (`0 , x') = `0 , mul GX x' (inv GX x) 
  bwd (groupPairSumIso x y) (`1 , y') = `1 , mul GY y' (inv GY y) 
  fwd-bwd (groupPairSumIso x y) (`0 , x') = <> , vert (
    mul GX (mul GX x' x) (inv GX x)  ==[ bleu (mulmul- GX _ _ _) >
    mul GX x' (mul GX x (inv GX x))  ==[ bleu (elim> GX _ _ (mul-inv GX _)) >
    x' [==] )
    where
      open EQPRF X
  fwd-bwd (groupPairSumIso x y) (`1 , y') = <> , vert (
    mul GY (mul GY y' y) (inv GY y)  ==[ bleu (mulmul- GY _ _ _) >
    mul GY y' (mul GY y (inv GY y))  ==[ bleu (elim> GY _ _ (mul-inv GY _)) >
    y' [==] )
    where
      open EQPRF Y
  bwd-fwd (groupPairSumIso x y) (`0 , x') = <> , vert (
    mul GX (mul GX x' (inv GX x)) x  ==[ bleu (mulmul- GX _ _ _) >
    mul GX x' (mul GX (inv GX x) x) ==[ bleu (elim> GX _ _ (mulinv- GX _)) >
    x' [==] )
    where
      open EQPRF X
  bwd-fwd (groupPairSumIso x y) (`1 , y') = <> , vert (
    mul GY (mul GY y' (inv GY y)) y  ==[ bleu (mulmul- GY _ _ _) >
    mul GY y' (mul GY (inv GY y) y) ==[ bleu (elim> GY _ _ (mulinv- GY _)) >
    y' [==] )
    where
      open EQPRF Y


  groupPairHomAutSum : (GX *Group* GY) =Group=> Automorphism (X `+ Y)
  mor (semigroup=> (monoid=> groupPairHomAutSum)) (x , y) = osi {X `+ Y}{X `+ Y} (groupPairSumIso x y)
  mul-pres (semigroup=> (monoid=> groupPairHomAutSum)) (x0 , y0) (x1 , y1) = 
    eqIso {X `+ Y}{X `+ Y}
      (osi {X `+ Y}{X `+ Y} (groupPairSumIso (mul GX x0 x1) (mul GY y0 y1)))
      (osi {X `+ Y}{X `+ Y} (compIso' (groupPairSumIso x0 y0) (groupPairSumIso x1 y1)))
      \ { (`0 , x) -> <> , mul-mul GX _ _ _
        ; (`1 , y) -> <> , mul-mul GY _ _ _
        }
  neu-pres (monoid=> groupPairHomAutSum) = eqIso {X `+ Y}{X `+ Y}
      (osi {X `+ Y}{X `+ Y} (groupPairSumIso (neu GX) (neu GY)))
      (osi {X `+ Y}{X `+ Y} idIso')
      \ { (`0 , x) -> <> , mul-neu GX _
        ; (`1 , y) -> <> , mul-neu GY _
        }

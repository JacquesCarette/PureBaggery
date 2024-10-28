module ActionsWeLike where

open import Basics
open import ExtUni
open import Reasoning
open import Iso
open import Algebras
open import Actions
open import GroupsWeLike
open import ProductsForAlgebras

module _ (X : U) where
  open Group (Automorphism X)
  open ACTION (Automorphism X)
  open Action

  AutAct : Action X
  act AutAct x (f , _) = f x
  act-neu AutAct x = refl X x
  act-mul AutAct x (f , _) (g , _) = refl X _

module _ {G : U} (GG : Group G) where
  open Group GG
  open ACTION GG
  open Action

  selfAction : Action G
  act selfAction = mul
  act-neu selfAction = mul-neu
  act-mul selfAction = mul-mul

  module _ {X : U}(A : Action X) where
    
    -- every action lifts contravariantly to an action on functions by precomposition
    module _ {Y : U} where
      faction : Action (X `> Y)
      act faction fu gr x = fu (act A x (inv gr))
      act-neu faction fu = homogTac (X `> Y) (\ x -> fu (act A x (inv neu))) fu \ x ->
        EQPRF.cong Y X fu (let open EQPRF X in
        act A x (inv neu) -[ cong G (act A x) invneu >
        act A x neu       -[ act-neu A x >
        x [QED]) --  (act-neu A x)
      act-mul faction fu gr0 gr1 = homogTac (X `> Y)
        (\ x -> fu (act A x (inv (mul gr0 gr1))))
        (\ x -> fu (act A (act A x (inv gr1)) (inv gr0)))
        \ x -> EQPRF.cong Y X fu (let open EQPRF X in
           act A x (inv (mul gr0 gr1))         -[ cong G (act A x) (invmul gr0 gr1) >
           act A x (mul (inv gr1) (inv gr0))   -[ act-mul A x _ _ >
           act A (act A x (inv gr1)) (inv gr0) [QED] )

    -- an action on X can be translated to an action on any Y iso to X
    module _ {Y : U}(f : X <==> Y) where
      open Action
      open EQPRF Y
      open _=Action=>_

      isoAction : Action Y
      act isoAction y g = fwd f (act A (bwd f y) g)
      act-neu isoAction y = vert (
        fwd f (act A (bwd f y) neu) ==[ congB X (fwd f) (act-neu A _) >
        fwd f (bwd f y) ==[ bleu (bwd-fwd f y) >
        y [==])
      act-mul isoAction y g h = vert (
        fwd f (act A (bwd f y) (mul g h)) ==[ congB X (fwd f) (act-mul A (bwd f y) g h)  >
        fwd f (act A (act A (bwd f y) g) h) < congB X (\ x -> fwd f (act A x h)) (fwd-bwd f _) ]==
        fwd f (act A (bwd f (fwd f (act A (bwd f y) g))) h) [==])

      isoActionHom=> : A =Action=> isoAction
      isoActionHom=> .carrier=> = fwd f
      isoActionHom=> .group=> = idGroup
      isoActionHom=> .act-pres x g = vert (
        fwd f (act A (bwd f (fwd f x)) g) ==[ congB X (\ z -> fwd f (act A z g)) (fwd-bwd f _)  >
        fwd f (act A x g)                 [==])

      isoActionHom<= : isoAction =Action=> A
      isoActionHom<= .carrier=> = bwd f
      isoActionHom<= .group=> = idGroup
      isoActionHom<= .act-pres y g = EQPRF.!_ X (fwd-bwd f (act A (bwd f y) g))

module _ {X Y : U}(GX : Group X)(GY : Group Y) where

  open ACTION
  module _ {A B : U}(AGXA : Action GX A)(AGYB : Action GY B) where

    open Action

    pairActsOnSum : Action (GX *Group* GY) (A `+ B)
    fst (act pairActsOnSum (z , _) (x , y)) = z
    snd (act pairActsOnSum (`0 , a) (x , y)) = act AGXA a x
    snd (act pairActsOnSum (`1 , b) (x , y)) = act AGYB b y
    fst (act-neu pairActsOnSum (z , _)) = refl `Two z
    snd (act-neu pairActsOnSum (`0 , a)) = act-neu AGXA a
    snd (act-neu pairActsOnSum (`1 , b)) = act-neu AGYB b
    fst (act-mul pairActsOnSum (z , _) _ _) = refl `Two z
    snd (act-mul pairActsOnSum (`0 , a) (x0 , y0) (x1 , y1)) = act-mul AGXA a x0 x1
    snd (act-mul pairActsOnSum (`1 , b) (x0 , y0) (x1 , y1)) = act-mul AGYB b y0 y1


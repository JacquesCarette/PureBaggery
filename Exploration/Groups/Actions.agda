{-# OPTIONS --allow-unsolved-metas #-}
module Actions where

open import Basics
open import ExtUni
open import Reasoning
open import Quotient
open import Algebras

-- defines various bits of Actions of an Algebra over a carrier G in U,
-- up to group.

module ACTION {G : U} (GG : Group G) where
  open Group GG

  record Action (X : U) : Set where
    field
      act : El (X `> G `> X)

      act-neu : Pr (ALL 1 X \ x -> Oq X (act x neu) x)
      act-mul : Pr (ALL 1 X \ x -> ALL 2 G \ g h ->
                    Oq X (act x (mul g h)) (act (act x g) h))

    open EQPRF X

    act-eq-neu : Pr (ALL 1 G \ g -> ALL 1 X \ x -> Oq G g neu `=> Oq X (act x g) x)
    act-eq-neu g x q = 
      act x g   -[ cong G (act x) q >
      act x neu -[ act-neu x >
      x         [QED]

    actinv : Pr (X `-> \ x -> G `-> \ g -> Oq X (act x (mul g (inv g))) x)
    actinv x g = 
       act x (mul g (inv g)) -[ cong G (act x) (mul-inv g) >
       act x neu             -[ act-neu x >
       x                     [QED]

    -- every action induces an equivalence on the acted-on type
    _~G~_ : El X -> El X -> P
    x ~G~ y = G `# \ g -> Oq X (act x g) y

    open Equiv
    ActEquiv : Equiv (El X) (\ x y -> Pr (x ~G~ y))
    eqR ActEquiv x = hide (neu , act-neu x)
    eqS ActEquiv x y (hide gq) = hide (let g = fst gq in (inv g , (
      act y (inv g)          < cong X (\ y -> act y (inv g)) (snd gq)  ]-
      act (act x g) (inv g)  < act-mul x g (inv g) ]-
      act x (mul g (inv g))  -[ actinv x g >
      x [QED])))
    eqT ActEquiv x y z (hide gq) (hide hq) = hide
      let g = fst gq ; h = fst hq in mul g h , (
      act x (mul g h) -[ act-mul x g h >
      act (act x g) h -[ cong X (\ y -> act y h) (snd gq) >
      act y h -[ snd hq >
      z [QED])


module _ {G H : U} {GG : Group G} {HH : Group H} where
  private
    module GA = ACTION GG
    module HA = ACTION HH

{-  -- This is the classical version of an action homomorphism, with the
    -- group homomorphism in the forward direction
    record _=Action=>_ {X Y : U} (AX : GA.Action X) (AY : HA.Action Y) : Set where
      private
        module AX = GA.Action AX
        module AY = HA.Action AY
        
      field
        carrier=> : El (X `> Y)
        -- conceivable that we don't need a full homormorphism here
        group=> : GG =Group=> HH
        act-pres : Pr (ALL 1 X \ x -> ALL 1 G \ g ->
          Oq Y (AY.act (carrier=> x) (_=Group=>_.mor group=> g)) (carrier=> (AX.act x g)))

      pres-~G~ : Pr (ALL 2 X \ x0 x1 -> x0 AX.~G~ x1 `=> carrier=> x0 AY.~G~ carrier=> x1)
      pres-~G~ x0 x1 = mapHide (\ (g , g-pres) ->
        mor g ,
        (AY.act (carrier=> x0) (mor g) -[ act-pres x0 g >
        carrier=> (AX.act x0 g)        -[ cong X carrier=> g-pres >
        carrier=> x1                   [QED]))
        where
          open _=Group=>_ group=>
          open EQPRF Y
-}

  -- This is the one we're trying out...
  module _ {X Y : U} (AX : GA.Action X) (AY : HA.Action Y) where
    record _=Action=>_ : Set where
      private
        module AX = GA.Action AX
        module AY = HA.Action AY

      field
        carrier=> : El (X `> Y)
        -- conceivable that we don't need a full homomorphism here
        group=> : HH =Group=> GG
        act-pres : Pr (ALL 1 X \ x -> ALL 1 H \ h ->
          Oq Y (AY.act (carrier=> x) h ) (carrier=> (AX.act x (_=Group=>_.mor group=> h))))

module _ {A X : U}{G : Group A} where

  open ACTION G
  
  module _ {AX : Action X} where
    open _=Action=>_

    idAction :  AX =Action=> AX
    carrier=> idAction = id
    group=> idAction = idGroup
    act-pres idAction x g = refl X _

module _ {A X B Y C Z : U}{GA : Group A}{GB : Group B}{GC : Group C} where
  private
    module AA = ACTION GA
    module AB = ACTION GB
    module AC = ACTION GC

  module _ {AX : AA.Action X}{BY : AB.Action Y}{CZ : AC.Action Z} where
    open _=Action=>_
    open _=Group=>_
    open EQPRF Z

    _-Action-_ : AX =Action=> BY -> BY =Action=> CZ
              -> AX =Action=> CZ
    carrier=> (f -Action- g) = carrier=> f - carrier=> g
    group=> (f -Action- g) = group=> g -Group- group=> f
    act-pres (f -Action- g) x c = vert (
      AC.Action.act CZ (carrier=> g (carrier=> f x)) c
        ==[ bleu (act-pres g (carrier=> f x) c) >
      carrier=> g (AB.Action.act BY (carrier=> f x) (mor (group=> g) c))
        ==[ congB Y (carrier=> g) (act-pres f x (mor (group=> g) c)) >
      carrier=> g (carrier=> f (AA.Action.act AX x (mor (group=> f) (mor (group=> g) c)))) [==])
    

{-
      module _ (HG : HH =Group=> GG)(f : X <==> Y) where
        open _=Group=>_ HG
        private
          module AX = GA.Action AX
          module AY = HA.Action AY
        
        homGroupIsoAct : _=Action=>_
        homGroupIsoAct = record
          { carrier=> = fwd f
          ; group=> = HG
          ; act-pres = \ x h -> vert (
              AY.act (fwd f x) h ==[ {!!} >    -- we suspect this to be nonsense
              fwd f (AX.act x (mor h)) [==])
          } where open EQPRF Y
-}

{-
      pres-~G~ : Pr (ALL 2 X \ x0 x1 -> x0 AX.~G~ x1 `=> carrier=> x0 AY.~G~ carrier=> x1)
      pres-~G~ x0 x1 = mapHide (\ (g , g-pres) ->
        mor g ,
        (AY.act (carrier=> x0) (mor g) -[ act-pres x0 g >
        carrier=> (AX.act x0 g)        -[ cong X carrier=> g-pres >
        carrier=> x1                   [QED]))
        where
          open _=Group=>_ group=>
          open EQPRF Y
-}

module _ {A B X : U}{G : Group A}{H : Group B}(gh : G =Group=> H) where

  private
    module GA = ACTION G
    module GAA = GA.Action
    module HA = ACTION H

  open _=Group=>_ gh

  module _ (ha : HA.Action X) where

    private module HAA = HA.Action ha

    open EQPRF X
    open Group

    groupHomAction : GA.Action X
    GAA.act groupHomAction x = mor - HAA.act x
    GAA.act-neu groupHomAction x = vert (
      HAA.act x (mor (neu G)) ==[ congB B (HAA.act x) neu-pres >
      HAA.act x (neu H) ==[ bleu (HAA.act-neu x) >
      x [==])
    GAA.act-mul groupHomAction x g0 g1 = vert (
      HAA.act x (mor (mul G g0 g1)) ==[ congB B (HAA.act x) (mul-pres g0 g1) >
      HAA.act x (mul H (mor g0) (mor g1)) ==[ bleu (HAA.act-mul x _ _) >
      HAA.act (HAA.act x (mor g0)) (mor g1) [==])

    open _=Action=>_
    groupHomActionMor : ha =Action=> groupHomAction
    carrier=> groupHomActionMor = id
    group=> groupHomActionMor = gh
    act-pres groupHomActionMor x g = refl X _

{-
module _ {A X Y : U}{G : Group A}(f : X <==> Y) where
  private
    module GA = ACTION G
    module GAA = GA.Action

  module _ (gx : GA.Action X) where

    isoActionHom=> : gx =Action=> (GA.isoAction gx f)
    isoActionHom=> = {!!}

    -- likely to fit in (backend of composition) in hole in Representable
    isoActionHom<= : (GA.isoAction gx f) =Action=> gx
    isoActionHom<= = {!!}
-}

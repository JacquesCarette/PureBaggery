{-# OPTIONS --allow-unsolved-metas #-}
module Action where

open import Basics
open import ExtUni
open import Reasoning
open import Quotient
open import Iso
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

  module _ {X : U}(A : Action X){Y : U} where
    open Action

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

  module _ {X : U}(A : Action X){Y : U}(f : X <==> Y) where
    open Action
    open EQPRF Y

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

module _ {X Y : U} where

  module _ (SX : SemiGroup X)(SY : SemiGroup Y) where

    open SemiGroup

    _*SemiGroup*_ : SemiGroup (X `* Y)
    mul _*SemiGroup*_ (x0 , y0) (x1 , y1) = mul SX x0 x1 , mul SY y0 y1
    mulmul- _*SemiGroup*_ (x0 , y0) (x1 , y1) (x2 , y2) = mulmul- SX x0 x1 x2 , mulmul- SY y0 y1 y2

  module _ (MX : Monoid X)(MY : Monoid Y) where

    open Monoid

    _*Monoid*_ : Monoid (X `* Y)
    _*Monoid*_ = monoid/ _ (semiGroup MX *SemiGroup* semiGroup MY) (record
      { neu = neu MX , neu MY
      ; mulneu- = \ (x , y) -> mulneu- MX x , mulneu- MY y
      ; mul-neu = \ (x , y) -> mul-neu MX x , mul-neu MY y
      })

  module _ (GX : Group X)(GY : Group Y) where

    open Group using (monoid; inv; mulinv-)

    _*Group*_ : Group (X `* Y)
    _*Group*_ = group/ _ (monoid GX *Monoid* monoid GY) (record
      { inv = inv GX >><< inv GY
      ; mulinv- = \ (x , y) -> mulinv- GX x , mulinv- GY y
      })

    open ACTION
    module _ {A B : U}(AGXA : Action GX A)(AGYB : Action GY B) where

      open Action
      
      pairActsOnSum : Action _*Group*_ (A `+ B)
      fst (act pairActsOnSum (z , _) (x , y)) = z
      snd (act pairActsOnSum (`0 , a) (x , y)) = act AGXA a x
      snd (act pairActsOnSum (`1 , b) (x , y)) = act AGYB b y
      fst (act-neu pairActsOnSum (z , _)) = refl `Two z
      snd (act-neu pairActsOnSum (`0 , a)) = act-neu AGXA a
      snd (act-neu pairActsOnSum (`1 , b)) = act-neu AGYB b
      fst (act-mul pairActsOnSum (z , _) _ _) = refl `Two z
      snd (act-mul pairActsOnSum (`0 , a) (x0 , y0) (x1 , y1)) = act-mul AGXA a x0 x1
      snd (act-mul pairActsOnSum (`1 , b) (x0 , y0) (x1 , y1)) = act-mul AGYB b y0 y1

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

    idAction :  _=Action=>_ {X} {X} AX AX
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

    -- this ugliness is new in 2.6.3, fix later
    _-Action-_ : _=Action=>_ {X} {Y} AX BY -> _=Action=>_ {Y} {Z} BY CZ
               -> _=Action=>_ {X} {Z} AX CZ
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
    groupHomActionMor : _=Action=>_ {X} {X} ha groupHomAction
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

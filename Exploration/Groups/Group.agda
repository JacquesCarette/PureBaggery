{-# OPTIONS --allow-unsolved-metas #-}
module Group where

open import Basics
open import ExtUni
open import Reasoning
open import Quotient
open import Iso

-- defines various bits of Algebra over a carrier G in U,
-- up to group. Intermediate steps give good places to put
-- oft used combinators and some lemmas
module _ (G : U) where

  private _~_ = Oq G

  open EQPRF G

  record SemiGroup : Set where
    field  
      mul : El (G `> G `> G)

      mulmul- : Pr (ALL 3 G \ x y z ->
                  mul (mul x y) z ~ mul x (mul y z))

    middle4 : Pr (ALL 4 G \ w x y z ->
      mul (mul w x) (mul y z) ~ mul w (mul (mul x y) z))
    middle4 w x y z =
      mul (mul w x) (mul y z) -[ mulmul- _ _ _ >
      mul w (mul x (mul y z)) < cong G (mul _) (mulmul- _ _ _) ]-
      mul w (mul (mul x y) z) [QED]

  record Monoid : Set where
    field
      neu : El G
      mul : El (G `> G `> G)

      mulneu- : Pr (ALL 1 G \ x -> mul neu x ~ x)
      mul-neu : Pr (ALL 1 G \ x -> mul x neu ~ x)
      mulmul- : Pr (ALL 3 G \ x y z ->
                   mul (mul x y) z ~ mul x (mul y z))
                   
    mul-mul : Pr (ALL 3 G \ x y z ->
                 mul x (mul y z) ~ mul (mul x y) z)
    mul-mul x y z = ! mulmul- x y z
                  
    semiGroup : SemiGroup
    semiGroup = record { mul = mul ; mulmul- = mulmul- }

    intro> : Pr (ALL 2 G \ x y -> x ~ neu `=> y ~ mul y x)
    intro< : Pr (ALL 2 G \ x y -> x ~ neu `=> y ~ mul x y)
    elim> : Pr (ALL 2 G \ x y -> x ~ neu `=> mul y x ~ y)
    elim< : Pr (ALL 2 G \ x y -> x ~ neu `=> mul x y ~ y)

    intro> x y p = 
      y         < mul-neu y ]-
      mul y neu -[ cong G (mul y) (! p) >
      mul y x    [QED]
    intro< x y p = 
      y         < mulneu- y ]-
      mul neu y -[ cong G (flip mul _) (! p) >
      mul x y   [QED]
    elim> x y p = ! intro> x y p
    elim< x y p = ! intro< x y p
    
  module _ (X : SemiGroup) where
  
    open SemiGroup X

    record Monoid/ : Set where
      field
        neu : El G

        mulneu- : Pr (ALL 1 G \ x -> mul neu x ~ x)
        mul-neu : Pr (ALL 1 G \ x -> mul x neu ~ x)

    monoid/ : Monoid/ -> Monoid
    monoid/ M/ = let open Monoid/ M/ in record {
        neu = neu ; mul = mul ; mulneu- = mulneu- ;
        mul-neu = mul-neu ; mulmul- = mulmul- }

  record Group : Set where
    field

      neu : El G
      inv : El (G `> G)
      mul : El (G `> G `> G)

      mulneu- : Pr (ALL 1 G \ x -> mul neu x ~ x)
      mulmul- : Pr (ALL 3 G \ x y z ->
                   mul (mul x y) z ~ mul x (mul y z))
      mulinv- : Pr (ALL 1 G \ x -> mul (inv x) x ~ neu)

    semiGroup : SemiGroup
    semiGroup = record { mul = mul ; mulmul- = mulmul- }

    -- we can't golf these next two since we're trying to prove that
    -- there is a Monoid structure induced by Group
    -- left unital semigroup for the first two steps is a bit much
    mul-inv : Pr (ALL 1 G \ x -> mul x (inv x) ~ neu)
    mul-inv x = 
      mul x (inv x)
        < mulneu- _ ]-
      mul neu (mul x (inv x))
        < cong G (flip mul _) (mulinv- _) ]-
      mul (mul (inv (inv x)) (inv x)) (mul x (inv x))
        -[ SemiGroup.middle4 semiGroup _ _ _ _ >
      mul (inv (inv x)) (mul (mul (inv x) x) (inv x))
        -[ cong G (mul _) (cong G (flip mul _) (mulinv- _)) >
      mul (inv (inv x)) (mul neu (inv x))
        -[ cong G (mul _) (mulneu- _) >
      mul (inv (inv x)) (inv x)
        -[ mulinv- _ >
      neu [QED]

    mul-neu : Pr (ALL 1 G \ x -> mul x neu ~ x)
    mul-neu x =
      mul x neu < refl (G `> G) (mul _) _ _ (mulinv- _) ]-
      mul x (mul (inv x) x)  < mulmul- _ _ _ ]-
      mul (mul x (inv x)) x  -[ cong G (flip mul _) (mul-inv _) >
      mul neu x              -[ mulneu- _ >
      x                      [QED]

    monoid : Monoid
    monoid = monoid/ semiGroup (record { neu = neu ; mulneu- = mulneu- ; mul-neu = mul-neu })

    open Monoid monoid using (intro<; elim>; elim<)
    
    invinv : Pr (ALL 1 G  \ x -> inv (inv x) ~ x)
    invinv x =
      inv (inv x)                        -[ intro< _ _ (mul-inv _) >
      mul (mul x (inv x)) (inv (inv x))  -[ mulmul- _ _ _ >
      mul x (mul (inv x) (inv (inv x)))  -[ elim> _ _ (mul-inv (inv x)) >
      x                                  [QED]

    invneu : Pr (inv neu ~ neu)
    invneu =
      inv neu            < mulneu- _ ]-
      mul neu (inv neu)  -[ mul-inv _ >
      neu                [QED]

    -- If you already know what the inverse of a mul ought to be, you can check that
    invmul-ans : Pr (ALL 2 G \ x y -> mul (mul x y) (mul (inv y) (inv x)) ~ neu)
    invmul-ans x y =
      mul (mul x y) (mul (inv y) (inv x))
        -[ SemiGroup.middle4 semiGroup _ _ _ _ >
      mul x (mul (mul y (inv y)) (inv x))
        -[ cong G (mul x) (elim< _ _ (mul-inv y)) >
      mul x (inv x)
        -[ mul-inv x >
      neu [QED] 
    
    invmul : Pr (ALL 2 G \ x y -> inv (mul x y) ~ mul (inv y) (inv x))
    invmul x y =
       inv (mul x y)
         < mul-neu _ ]-
       mul (inv (mul x y)) neu
         < cong G (mul _) (invmul-ans x y) ]-
       mul (inv (mul x y)) (mul (mul x y) (mul (inv y) (inv x)))
         < mulmul- _ _ _ ]-
       mul (mul (inv (mul x y)) (mul x y)) (mul (inv y) (inv x))
         -[ elim< _ _ (mulinv- (mul x y)) >
       mul (inv y) (inv x) [QED]

  module _ (X : Monoid) where
  
    open Monoid X

    record Group/ : Set where
      field
        inv : El (G `> G)

        mulinv- : Pr (ALL 1 G \ x -> mul (inv x) x ~ neu)

    group/ : Group/ -> Group
    group/ G/ = let open Group/ G/ in record {
      neu = neu ; inv = inv ; mul = mul ;
      mulneu- = mulneu- ; mulmul- = mulmul- ; mulinv- = mulinv- }
    
  GroUp : U
  GroUp = 
    G `>< \ neu ->
    (G `> G) `>< \ inv ->
    (G `> G `> G) `>< \ mul ->
    `Pr ((ALL 1 G \ x -> mul neu x ~ x)
     `/\ (ALL 3 G \ x y z ->
                   mul (mul x y) z ~ mul x (mul y z))
     `/\ (ALL 1 G \ x -> mul (inv x) x ~ neu))

module _ {G : U} where

  -- rigid in the sense of unification
  rigidGroup : El (GroUp G) -> Group G
  rigidGroup (neu , inv , mul , mulneu- , mulmul- , mulinv-) = record
    { neu = neu
    ; inv = inv
    ; mul = mul
    ; mulneu- = mulneu-
    ; mulmul- = mulmul-
    ; mulinv- = mulinv-
    }

  -- 6 isn't Scott's 23, but it is still the same disease
  tupleGroup : Group G -> El (GroUp G)
  tupleGroup g = neu , inv , mul , mulneu- , mulmul- , mulinv-
    where open Group g

  module ACTION (GG : Group G) where
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
        act x g -[ cong G (act x) q >
        act x neu -[ act-neu x >
        x [QED]

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

    open Group

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

-- Homomorphisms for everything
module _ where
  -- SemiGroup
  record _=SemiGroup=>_ {X Y : U} (R : SemiGroup X) (S : SemiGroup Y) : Set where
    private
      module R = SemiGroup R
      module S = SemiGroup S
    field
      mor : El (X `> Y)
      mul-pres : Pr (ALL 2 X \ x0 x1 -> Oq Y (mor (R.mul x0 x1)) (S.mul (mor x0) (mor x1)))

  record _=Monoid=>_ {X Y : U} (R : Monoid X) (S : Monoid Y) : Set where
    private
      module R = Monoid R
      module S = Monoid S
    field
      semigroup=> : R.semiGroup =SemiGroup=> S.semiGroup

    open _=SemiGroup=>_ semigroup=> public
    field
      neu-pres : Pr (Oq Y (mor R.neu) S.neu)

  record _=Group=>_ {X Y : U} (R : Group X) (S : Group Y) : Set where
    private
      module R = Group R
      module S = Group S
    field
      monoid=> : R.monoid =Monoid=> S.monoid

    open _=Monoid=>_ monoid=> public
    
    -- automatically preserves the inverse
    inv-pres : Pr (ALL 1 X \ x -> Oq Y (mor (R.inv x)) (S.inv (mor x)))
    inv-pres x = 
      mor (R.inv x)                                         -[ SM.intro> _ _ (S.mul-inv (mor x))  >
      S.mul (mor (R.inv x)) (S.mul (mor x) (S.inv (mor x))) < S.mulmul- _ _ _ ]-
      S.mul (S.mul (mor (R.inv x)) (mor x)) (S.inv (mor x)) -[ SM.elim< _ _ (
          S.mul (mor (R.inv x)) (mor x) < mul-pres _ _ ]-
          mor (R.mul (R.inv x) x)       -[ cong X mor (R.mulinv- _) >
          mor R.neu                     -[ neu-pres >
          S.neu                         [QED]) >
      S.inv (mor x) [QED]
      where
        open EQPRF Y
        module SM = Monoid S.monoid

  module _ {X : U} where

    module _ {S : SemiGroup X} where
      open _=SemiGroup=>_

      idSemiGroup : S =SemiGroup=> S
      mor idSemiGroup = id
      mul-pres idSemiGroup _ _ = refl X _

    module _ {M : Monoid X} where
      open _=Monoid=>_

      idMonoid : M =Monoid=> M
      semigroup=> idMonoid = idSemiGroup
      neu-pres idMonoid = refl X _

    module _ {G : Group X} where
      open _=Group=>_

      idGroup : G =Group=> G
      monoid=> idGroup = idMonoid


  module _ {X Y Z : U} where
    open EQPRF Z

    module _ {R : SemiGroup X}{S : SemiGroup Y}{T : SemiGroup Z} where
      open SemiGroup
      open _=SemiGroup=>_
    
      _-SemiGroup-_ : R =SemiGroup=> S -> S =SemiGroup=> T -> R =SemiGroup=> T
      mor (rs -SemiGroup- st) = mor rs - mor st
      mul-pres (rs -SemiGroup- st) x0 x1 = vert (
        mor st (mor rs (mul R x0 x1)) ==[ congB Y (mor st) (mul-pres rs _ _) >
        mor st (mul S (mor rs x0) (mor rs x1)) ==[ bleu (mul-pres st _ _) >
        mul T (mor st (mor rs x0)) (mor st (mor rs x1)) [==])

    module _ {R : Monoid X}{S : Monoid Y}{T : Monoid Z} where
      open Monoid
      open _=Monoid=>_
      open _=SemiGroup=>_
    
      _-Monoid-_ : R =Monoid=> S -> S =Monoid=> T -> R =Monoid=> T
      semigroup=> (rs -Monoid- st) = semigroup=> rs -SemiGroup- semigroup=> st
      neu-pres (rs -Monoid- st) = vert (
        mst (mrs (neu R)) ==[ congB Y mst (neu-pres rs) >
        mst (neu S) ==[ bleu (neu-pres st) >
        neu T [==])
        where mrs = mor (semigroup=> rs) ; mst = mor (semigroup=> st)
      
    module _ {R : Group X}{S : Group Y}{T : Group Z} where
      open Group
      open _=Group=>_
    
      _-Group-_ : R =Group=> S -> S =Group=> T -> R =Group=> T
      monoid=> (rs -Group- st) = monoid=> rs -Monoid- monoid=> st

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

    idAction : AX =Action=> AX
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

    _-Action-_ : AX =Action=> BY -> BY =Action=> CZ -> AX =Action=> CZ
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

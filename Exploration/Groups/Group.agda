module Group where

open import Basics
open import ExtUni
open import Reasoning
open import Quotient

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
    record _=Action=>_ {X Y : U} (AX : GA.Action X) (AY : HA.Action Y) : Set where
      private
        module AX = GA.Action AX
        module AY = HA.Action AY
        
      field
        carrier=> : El (X `> Y)
        -- conceivable that we don't need a full homormorphism here
        group=> : HH =Group=> GG
        act-pres : Pr (ALL 1 X \ x -> ALL 1 H \ h ->
          Oq Y (AY.act (carrier=> x) h ) (carrier=> (AX.act x (_=Group=>_.mor group=> h))))
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

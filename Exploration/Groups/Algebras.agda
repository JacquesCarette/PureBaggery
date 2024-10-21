module Algebras where

open import Basics
open import ExtUni
open import Reasoning
open import Iso

-- defines various bits of Algebra over a carrier G in U,
-- up to group. Intermediate steps give good places to put
-- oft used combinators and some lemmas. The homomorphisms
-- of each of these Algebras are also defined here, as well as
-- id Homs and composition of homomorphisms. i.e., we give all
-- the stuff to make Things and their Categories of Thing Homs

-- Naming convention:
-- - X/ in the context of a Y means
--     "X over Y", such as "monoid over a semigroup".
-- - _=X=>_ means "X homomorphism", used as (say) A =Group=> B to mean
--     Group homomorphism from Group A to Group B
-- - idX means "identity X homomorphim"
-- - _-X-_ means "composition of X homomorphism", typed appropriately
-- - X=> in the context of =Y=> means "induces X homorphism when you have
--     a Y homomorphism in hand".

-- Note that we're not building a lattice of theories, nor
-- are we systematic, so no Magma nor LeftUnitalSemigroup.

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

    open Monoid monoid using (mul-mul; intro<; elim>; elim<) public
    
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
         -[ Monoid.intro> monoid _ _ (invmul-ans x y) >
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

  -- definition of a Group as an element of U
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
        mor st (mor rs (mul R x0 x1))                   ==[ congB Y (mor st) (mul-pres rs _ _) >
        mor st (mul S (mor rs x0) (mor rs x1))          ==[ bleu (mul-pres st _ _) >
        mul T (mor st (mor rs x0)) (mor st (mor rs x1)) [==])

    module _ {R : Monoid X}{S : Monoid Y}{T : Monoid Z} where
      open Monoid
      open _=Monoid=>_
      open _=SemiGroup=>_
    
      _-Monoid-_ : R =Monoid=> S -> S =Monoid=> T -> R =Monoid=> T
      semigroup=> (rs -Monoid- st) = semigroup=> rs -SemiGroup- semigroup=> st
      neu-pres (rs -Monoid- st) = vert (
        mst (mrs (neu R)) ==[ congB Y mst (neu-pres rs) >
        mst (neu S)       ==[ bleu (neu-pres st) >
        neu T             [==])
        where mrs = mor (semigroup=> rs) ; mst = mor (semigroup=> st)
      
    module _ {R : Group X}{S : Group Y}{T : Group Z} where
      open Group
      open _=Group=>_
    
      _-Group-_ : R =Group=> S -> S =Group=> T -> R =Group=> T
      monoid=> (rs -Group- st) = monoid=> rs -Monoid- monoid=> st

-- Isomomorphisms for everything
module _ {X Y : U} where
  open EQPRF X
  
  -- SemiGroup
  record _<=SemiGroup=>_ (R : SemiGroup X) (S : SemiGroup Y) : Set where
    open SemiGroup
    open _=SemiGroup=>_
    
    field
      fwdmor : R =SemiGroup=> S
      hasInv : El (HasInv X Y (mor fwdmor))

    private
      xy : X <==> Y
      xy = iso' ((mor fwdmor) , hasInv)

    bwdmor : S =SemiGroup=> R
    bwdmor .mor = fst hasInv
    bwdmor .mul-pres y0 y1 = vert (
      bwd xy (mul S y0 y1)
        < bleu (refl (Y `> Y `> X) (\ y0 y1 -> bwd xy (mul S y0 y1))
          _ _ (bwd-fwd xy y0)
          _ _ (bwd-fwd xy y1)) ]==
      bwd xy (mul S (fwd xy (bwd xy y0)) (fwd xy (bwd xy y1)))
        < congB Y (bwd xy) (mul-pres fwdmor _ _) ]==
      bwd xy (fwd xy (mul R (bwd xy y0) (bwd xy y1)))
        ==[ bleu (fwd-bwd xy _) >
      mul R (bwd xy y0) (bwd xy y1) [==] )
    
  record _<=Monoid=>_ (R : Monoid X) (S : Monoid Y) : Set where
    open Monoid
    open _=SemiGroup=>_
    open _=Monoid=>_
    
    field
      fwdmor : R =Monoid=> S
      hasInv : El (HasInv X Y (mor fwdmor))

    private
      xy : X <==> Y
      xy = iso' ((mor fwdmor) , hasInv)

      xySGI : semiGroup R <=SemiGroup=> semiGroup S
      xySGI = record { fwdmor = semigroup=> fwdmor ; hasInv = hasInv }

    bwdmor : S =Monoid=> R
    semigroup=> bwdmor = _<=SemiGroup=>_.bwdmor xySGI
    neu-pres bwdmor = vert (
      bwd xy (neu S) < congB Y (bwd xy) (neu-pres fwdmor) ]==
      bwd xy (fwd xy (neu R)) ==[ bleu (fwd-bwd xy _) >
      neu R [==])


  record _<=Group=>_ (R : Group X) (S : Group Y) : Set where
    open Group
    open _=SemiGroup=>_
    open _=Monoid=>_
    open _=Group=>_
    
    field
      fwdmor : R =Group=> S
      hasInv : El (HasInv X Y (mor fwdmor))

    private
      xy : X <==> Y
      xy = iso' ((mor fwdmor) , hasInv)

      xyMI : monoid R <=Monoid=> monoid S
      xyMI = record { fwdmor = monoid=> fwdmor ; hasInv = hasInv }

    bwdmor : S =Group=> R
    monoid=> bwdmor = _<=Monoid=>_.bwdmor xyMI

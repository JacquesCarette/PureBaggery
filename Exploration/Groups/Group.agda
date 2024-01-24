module Group where

open import Basics
open import ExtUni
open import Reasoning

module _ (G : U) where

  private _~_ = Oq G

  open EQPRF G

  record SemiGroup : Set where
    field  
      mul : El (G `> G `> G)

      mulmul- : Pr (G `-> \ x -> G `-> \ y -> G `-> \ z ->
                  mul (mul x y) z ~ mul x (mul y z))

    middle4 : Pr (ALL 4 G \ w x y z ->
      mul (mul w x) (mul y z) ~ mul w (mul (mul x y) z))
    middle4 w x y z =
      mul (mul w x) (mul y z) -[ mulmul- _ _ _ >
      mul w (mul x (mul y z)) < cong (mul _) (mulmul- _ _ _) ]-
      mul w (mul (mul x y) z) [QED]


  record Monoid : Set where
    field

      neu : El G
      mul : El (G `> G `> G)

      mulneu- : Pr (ALL 1 G \ x -> mul neu x ~ x)
      mul-neu : Pr (ALL 1 G \ x -> mul x neu ~ x)
      mulmul- : Pr (ALL 3 G \ x y z ->
                   mul (mul x y) z ~ mul x (mul y z))

    semiGroup : SemiGroup
    semiGroup = record { mul = mul ; mulmul- = mulmul- }

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

    mul-inv : Pr (ALL 1 G \ x -> mul x (inv x) ~ neu)
    mul-inv x = 
      mul x (inv x)
        < mulneu- _ ]-
      mul neu (mul x (inv x))
        < cong (flip mul _) (mulinv- _) ]-
      mul (mul (inv (inv x)) (inv x)) (mul x (inv x))
        -[ SemiGroup.middle4 semiGroup _ _ _ _ >
      mul (inv (inv x)) (mul (mul (inv x) x) (inv x))
        -[ cong (mul _) (cong (flip mul _) (mulinv- _)) >
      mul (inv (inv x)) (mul neu (inv x))
        -[ cong (mul _) (mulneu- _) >
      mul (inv (inv x)) (inv x)
        -[ mulinv- _ >
      neu [QED]

    mul-neu : Pr (ALL 1 G \ x -> mul x neu ~ x)
    mul-neu x =
      mul x neu < refl (G `> G) (mul _) _ _ (mulinv- _) ]-
      mul x (mul (inv x) x)  < mulmul- _ _ _ ]-
      mul (mul x (inv x)) x  -[ cong (flip mul _) (mul-inv _) >
      mul neu x              -[ mulneu- _ >
      x                      [QED]

    monoid : Monoid
    monoid = monoid/ semiGroup (record { neu = neu ; mulneu- = mulneu- ; mul-neu = mul-neu })

    invinv : Pr (ALL 1 G  \ x -> inv (inv x) ~ x)
    invinv x =
      inv (inv x)                         < mulneu- _ ]-
      mul neu (inv (inv x))               < cong (flip mul _) (mul-inv _) ]-
      mul (mul x (inv x)) (inv (inv x))  -[ mulmul- _ _ _ >
      mul x (mul (inv x) (inv (inv x)))  -[ cong (mul _) (mul-inv _) >
      mul x neu                          -[ mul-neu _ >
      x                                  [QED]

    invneu : Pr (inv neu ~ neu)
    invneu =
      inv neu            < mulneu- _ ]-
      mul neu (inv neu)  -[ mul-inv _ >
      neu                [QED]

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

  record Action (g : Group G)(X : U) : Set where
    open Group g
    
    field
      act : El (X `> G `> X)

      act-neu : Pr (ALL 1 X \ x -> Oq X (act x neu) x)
      act-mul : Pr (ALL 1 X \ x -> ALL 2 G \ g h ->
                    Oq X (act x (mul g h)) (act (act x g) h))
                    
    open EQPRF X

{-
    actinv : Pr (X `-> \ x -> G `-> \ g -> Eq X X (act x (mul g (inv g))) x)
    actinv x g = {!!}
-}

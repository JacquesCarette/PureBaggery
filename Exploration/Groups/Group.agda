module Group where

open import Basics
open import ExtUni
open import Reasoning

record Group (G : U) : Set where
  field
  
    neu : El G
    inv : El (G `> G)
    mul : El (G `> G `> G)
    
    mulneu- : Pr (G `-> \ x -> Eq G G (mul neu x) x)
    mulmul- : Pr (G `-> \ x -> G `-> \ y -> G `-> \ z ->
                 Eq G G (mul (mul x y) z) (mul x (mul y z)))
    mulinv- : Pr (G `-> \ x -> Eq G G (mul (inv x) x) neu)
    
  open EQPRF G
  
  mul-inv : Pr (G `-> \ x -> Eq G G (mul x (inv x)) neu)
  mul-inv x = 
    mul x (inv x)
      < mulneu- _ ]-
    mul neu (mul x (inv x))
      < cong (flip mul _) (mulinv- _) ]-
    mul (mul (inv (inv x)) (inv x)) (mul x (inv x))
      -[ mulmul- _ _ _ >
    mul (inv (inv x)) (mul (inv x) (mul x (inv x)))
      < cong (mul _) (mulmul- _ _ _) ]-
    mul (inv (inv x)) (mul (mul (inv x) x) (inv x))
      -[ cong (mul _) (cong (flip mul _) (mulinv- _)) >
    mul (inv (inv x)) (mul neu (inv x))
      -[ cong (mul _) (mulneu- _) >
    mul (inv (inv x)) (inv x)
      -[ mulinv- _ >
    neu [QED]

  mul-neu : Pr (G `-> \ x -> Eq G G (mul x neu) x)
  mul-neu x =
    mul x neu < refl (G `> G) (mul _) _ _ (mulinv- _) ]-
    mul x (mul (inv x) x)  < mulmul- _ _ _ ]-
    mul (mul x (inv x)) x  -[ cong (flip mul _) (mul-inv _) >
    mul neu x              -[ mulneu- _ >
    x                      [QED]

  invinv : Pr (G `-> \ x -> Eq G G (inv (inv x)) x)
  invinv x =
    inv (inv x)                         < mulneu- _ ]-
    mul neu (inv (inv x))               < cong (flip mul _) (mul-inv _) ]-
    mul (mul x (inv x)) (inv (inv x))  -[ mulmul- _ _ _ >
    mul x (mul (inv x) (inv (inv x)))  -[ cong (mul _) (mul-inv _) >
    mul x neu                          -[ mul-neu _ >
    x                                  [QED]

  invneu : Pr (Eq G G (inv neu) neu)
  invneu =
    inv neu            < mulneu- _ ]-
    mul neu (inv neu)  -[ mul-inv _ >
    neu                [QED]

  mul-mul : Pr (G `-> \ x -> G `-> \ y -> G `-> \ z ->
                 Eq G G (mul x (mul y z)) (mul (mul x y) z))
  mul-mul x y z = ! mulmul- x y z
  
GroUp : U -> U
GroUp G = 
  G `>< \ neu ->
  (G `> G) `>< \ inv ->
  (G `> G `> G) `>< \ mul ->
  `Pr ((G `-> \ x -> Eq G G (mul neu x) x)
   `/\ (G `-> \ x -> G `-> \ y -> G `-> \ z ->
                 Eq G G (mul (mul x y) z) (mul x (mul y z)))
   `/\ (G `-> \ x -> Eq G G (mul (inv x) x) neu))

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

      act-neu : Pr (X `-> \ x -> Eq X X (act x neu) x)
      act-mul : Pr (X `-> \ x -> G `-> \ g -> G `-> \ h ->
                    Eq X X (act x (mul g h)) (act (act x g) h))
                    
    open EQPRF X

{-
    actinv : Pr (X `-> \ x -> G `-> \ g -> Eq X X (act x (mul g (inv g))) x)
    actinv x g = {!!}
-}

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

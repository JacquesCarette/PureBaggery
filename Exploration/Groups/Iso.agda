module Iso where

open import Basics
open import ExtUni
open import Reasoning

-- type equivalence via explicit morphisms
-- and irrelevant proofs of left/right inverse
-- aka type isomorphism (strictly speaking, quasi-equivalence)
_<=>_ : U -> U -> U
S <=> T
   = (S `> T) `>< \ f
  -> (T `> S) `>< \ g
  -> `Pr ( (S `-> \ s -> Eq S S (g (f s)) s)
       `/\ (T `-> \ t -> Eq T T (f (g t)) t)
         )

-- make it easier to work with equivalences
record _<==>_ (S T : U) : Set where
  constructor iso
  field
    fwd : El (S `> T)
    bwd : El (T `> S)
    fwd-bwd : Pr (S `-> \ s -> Eq S S (bwd (fwd s))  s)
    bwd-fwd : Pr (T `-> \ t -> Eq T T (fwd (bwd t))  t)

  -- deconstructor
  osi : El (S <=> T)
  osi = fwd , bwd , fwd-bwd , bwd-fwd
  isFwd : (t : El T)
          (P : El T -> U)
       -> ((s : El S) -> El (P (fwd s)))
       -> El (P t)
  isFwd t P p = let open EQPRF T in 
    J T (bwd-fwd t ) (\ t _ -> P t) (p (bwd t))

  isBwd : (s : El S)
          (P : El S -> U)
       -> ((t : El T) -> El (P (bwd t)))
       -> El (P s)
  isBwd s P p = let open EQPRF S in 
    J S (fwd-bwd s) (\ s _ -> P s) (p (fwd s))

  flipFwd : (s : El S)
    (P : El S -> El T -> U) ->
    ((t : El T) -> El (P (bwd t) t)) ->
    El (P s (fwd s))
  flipFwd s P p = let open EQPRF S in
    J S (fwd-bwd s) (\ x _ -> P x (fwd s)) (p (fwd s)) 

open _<==>_ public


module _ (S T : U){P : El (S <=> T) -> Set} where
  -- given a property of an iso, a way to prove it for a blue
  -- version, transfer that proof to a given iso
  blueIso : 
    ((q : S <==> T) -> P (osi q))
    -> (f : El (S <=> T)) -> P f
  blueIso q f = q _

-- repacking an iso
iso' : {S T : U} -> El (S <=> T) -> S <==> T
iso' (f , g , f-g , g-f) = iso f g f-g g-f

-------------------------------------------------------------
-- construct some explicit type isomorphisms

-- show Iso is a proof-relevant equivalence, aka groupoid
idIso : (X : U) -> El (X <=> X)
idIso X = id , id , refl X , refl X

invIso : (S T : U) -> El (S <=> T) -> El (T <=> S)
invIso S T (f , g , p , q) = g , f , q , p

compIso : (R S T : U) -> El (R <=> S) -> El (S <=> T) -> El (R <=> T)
compIso R S T (f , g , gf , fg) (h , k , kh , hk)
  = (f - h)
  , (k - g)
  , (\ r -> let open EQPRF R in
       g (k (h (f r))) -[ refl (S `> R) g (k (h (f r))) (f r) (kh (f r)) >
       g (f r)         -[ gf r >
       r               [QED]
    )
  , (\ t -> let open EQPRF T in
       h (f (g (k t))) -[ refl (S `> T) h (f (g (k t))) (k t) (fg (k t)) >
       h (k t)          -[ hk t >
       t                [QED] )

---------
-- May as well build them for blue isos too
-- do it directly, i.e. without going via <=>
idIso' : {X : U} -> X <==> X
idIso' {X} = iso' (idIso X)

invIso' : {S T : U} -> S <==> T -> T <==> S
fwd (invIso' i) = bwd i
bwd (invIso' i) = fwd i
fwd-bwd (invIso' i) = bwd-fwd i
bwd-fwd (invIso' i) = fwd-bwd i

-- except here, for now
compIso' : {R S T : U} -> R <==> S -> S <==> T -> R <==> T
compIso' {R} {S} {T} f g = iso' (compIso R S T (osi f) (osi g))

module _ (R : U) where

  _=[_>_ : forall {S T} -> R <==> S -> S <==> T -> R <==> T
  _=[_>_ = compIso'
  
  _<_]=_ : forall {S T} -> S <==> R -> S <==> T -> R <==> T
  _<_]=_ f g = compIso' (invIso' f) g
  
  _[ISO] : R <==> R
  _[ISO] = idIso'

  infixr 2 _=[_>_ _<_]=_
  infixr 3 _[ISO]

module _ (A : U){S T : El A -> U}
         (f : (a : El A) -> S a <==> T a)
  where
  
  sgIso : (A `>< S) <==> (A `>< T)
  fwd sgIso (a , s) = a , fwd (f a) s
  bwd sgIso (a , t) = a , bwd (f a) t
  fwd-bwd sgIso (a , s) = refl A a , fwd-bwd (f a) s
  bwd-fwd sgIso (a , t) = refl A a , bwd-fwd (f a) t

module _ (A : U)(B : El A -> U)(C : (a : El A) -> El (B a) -> U)
  where
  
  sgAsso : ((A `>< B) `>< (/\ C)) <==> (A `>< \ a -> B a `>< C a)
  fwd sgAsso ((a , b) , c) = a , b , c
  bwd sgAsso (a , b , c) = (a , b) , c
  fwd-bwd sgAsso ((a , b) , c) = refl ((A `>< B) `>< (/\ C)) _
  bwd-fwd sgAsso (a , b , c) = refl (A `>< \ a -> B a `>< C a) _

-- Equality of isos
module _ {R S : U} (f g : El (R <=> S)) where
  private
    f' g' : R <==> S
    f' = iso' f
    g' = iso' g
    
  module _
    (fwd-eq : (r0 : El R) -> Pr (Eq S S (fwd f' r0) (fwd g' r0)))
    (bwd-eq : (s0 : El S) -> Pr (Eq R R (bwd f' s0) (bwd g' s0))) where
    eqIso : Pr (Eq (R <=> S) (R <=> S) f g)
    fst eqIso       r0 r1 r01 = J R r01 (\ r1 _ -> `Pr (Eq S S (fwd f' r0) (fwd g' r1))) (fwd-eq r0)
    fst (snd eqIso) s0 s1 s01 = J S s01 (\ s1 _ -> `Pr (Eq R R (bwd f' s0) (bwd g' s1))) (bwd-eq s0)
    snd (snd eqIso) = _

-- back-and-forth is id
module _ {R S : U} (f : El (R <=> S)) where
  private
    f' : R <==> S
    f' = iso' f
    
  inv-after : Pr (Eq (R <=> R) (R <=> R) (compIso R S R f (invIso R S f)) (idIso R))
  inv-after = eqIso {R} {R} (compIso R S R f (invIso R S f)) (idIso R)
    (fwd-bwd f')
    (fwd-bwd f')

  after-inv : Pr (Eq (S <=> S) (S <=> S) (compIso S R S (invIso R S f) f) (idIso S))
  after-inv = eqIso {S} {S} (compIso S R S (invIso R S f) f) (idIso S)
    (bwd-fwd f')
    (bwd-fwd f')

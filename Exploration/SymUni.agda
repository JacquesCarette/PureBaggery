-- ``Symmetric Universes''
-- wherein we describe universes where we can have containers whose
-- position sets have symmetries and everyone who deals with such
-- containers is obligated to respect those symmetries.

module SymUni where

--------------------------------------------------------------------
-- First, a lot of kit to get started

-- Using proof irrelevance keeps us from using details that we
-- should not care about. [Also brings in complications.]
record Hide (X : Set) : Set where
  constructor hide
  field
    .expose : X
open Hide public

--------------
-- empty, singleton and (exactly) 2 point set along with eliminator
data Zero' : Set where
Zero = Hide Zero'
record One : Set where constructor <>
data Two : Set where `0 `1 : Two
_<01>_ : forall {k}{P : Two -> Set k} -> P `0 -> P `1 -> (b : Two) -> P b
(p0 <01> p1) `0 = p0
(p0 <01> p1) `1 = p1

-- dependent sum, disjoint union (coproduct) and product
record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_
_+_ _*_ : Set -> Set -> Set
S + T = Two >< \ { `0 -> S ; `1 -> T }
S * T = S >< \ _ -> T

-- uncurry
/\_ : {S : Set}{T : S -> Set}{P : S >< T -> Set}
   -> ((s : S)(t : T s) -> P (s , t))
   -> (st : S >< T) -> P st
(/\ k) (s , t) = k s t

-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}
_+N_ : Nat -> Nat -> Nat
ze +N m = m
su n +N m = su (n +N m)


id : forall {k}{X : Set k} -> X -> X
id x = x

-- dependent function composition, pipe style
_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  -> C a (f a)
(f - g) a = g (f a)

-- representation of quotienting by a relation
--   should be in a separate file and only a certain
--   interface exposed, so that no one can inspect the
--   implementation details. We'll just promise to be
--   good for now.

record Equiv (X : Set)(R : X -> X -> Set) : Set where
  field
    eqR : (x : X) -> R x x
    eqS : (x y : X) -> R x y -> R y x
    eqT : (x y z : X) -> R x y -> R y z -> R x z

record Quotient (X : Set)(R : X -> X -> Set)(Q : Equiv X R) : Set where
  constructor `[_]
  field
    rep : X

-----------------------------------------------------------
-- A first universe of descriptions and interpretations
-- P : proofs
-- Pr : interp of P
-- U : types
-- El : interp of U
data P : Set
Pr : P -> Set
data U : Set
El : U -> Set


-- false, true, and, implication, inhabitation and
--  equivalence under the (closure of) a relation
data P where
  `Zero `One : P
  _`/\_ : (S : P)(T : P) -> P
  _`->_ : (S : U)(T : El S -> P) -> P
  `In : (T : U) -> P
  -- `Equiv : (T : U)(R : El T -> El T -> P) -> P
  -- `QC   : (T : U)(R : El T -> El T -> P) -> El T -> El T -> P
  -- It might be tempting to add a code for equality, but it's hard to decode.
  -- `Eq   : (S T : U) -> El S -> El T -> P

-- Straightforward Curry-Howard style representation
Pr `Zero = Zero
Pr `One = One
Pr (A `/\ B) = Pr A * Pr B
Pr (S `-> B) = (s : El S) -> Pr (B s)
Pr (`In T) = Hide (El T)
-- Pr (`Equiv T R) = Equiv (El T) \ i j -> Pr (R i j)
-- Pr (`QC T R i j) = QC (El T) (\ i j -> Pr (R i j)) i j
-- Decoding `Eq makes a not obviously structural recursive call to Pr.
-- Pr (`Eq S T s t) = Pr (Eq S T s t)

infixr 10 _`/\_
infixr 5  _`->_

-- empty, singleton, 2, naturals,
-- sigma, pi, proofs and quotients
data U where
  `Zero `One `Two `Nat : U
  _`><_ _`->_ : (S : U)(T : El S -> U) -> U
  `Pr : P -> U
  `Quotient : (T : U)(R : El T -> El T -> P)
              (Q : Equiv (El T) (\ i j -> Pr (R i j))) -> U
  -- it's tempting to add a (redundant) code for isomorphisms, so as
  -- to make them a record with named fields, but the positivity checker
  -- loses its nerve
  -- _`<=>_ : U -> U -> U

-- nondependent abbreviations for functions, product and coproduct (respectively)
_`>_ _`*_ : U -> U -> U
S `> T = S `-> \ _ -> T
S `* T = S `>< \ _ -> T
infixr 5 _`>_
infixr 10 _`*_

-- Straightforward rep. 
El `Zero = Zero
El `One = One
El `Two = Two
El `Nat = Nat
El (S `>< T) = El S >< \ s -> El (T s)
El (S `-> T) = (s : El S) -> El (T s)
El (`Pr A)   = Pr A -- Hide (Pr A)
El (`Quotient T R Q)  = Quotient (El T) (\ i j -> Pr (R i j)) Q


_`+_ : U -> U -> U
S `+ T = `Two `>< (S <01> T)

-- "ordinary" implication, aka non-dependent
_`=>_ : P -> P -> P
A `=> B = `Pr A `-> \ _ -> B
infixr 5 _`=>_

--------------------------------------------------------------------------

Eq : (S T : U) -> El S -> El T -> P
-- We need to be able to talk about equality of
--  representations
-- Note that P/Pr don't depend on this directly

-- This is Pious heterogeneous equality:
-- "if the types are equal, then so are the values"
Eq `One `One  _  _ = `One
Eq `Two `Two `0 `0 = `One
Eq `Two `Two `0 `1 = `Zero
Eq `Two `Two `1 `0 = `Zero
Eq `Two `Two `1 `1 = `One
Eq `Nat `Nat ze ze = `One
Eq `Nat `Nat ze (su y) = `Zero
Eq `Nat `Nat (su x) ze = `Zero
Eq `Nat `Nat (su x) (su y) = Eq `Nat `Nat x y
Eq (S0 `>< T0) (S1 `>< T1) (s0 , t0) (s1 , t1) =
  Eq S0 S1 s0 s1 `/\ Eq (T0 s0) (T1 s1) t0 t1 
Eq (S0 `-> T0) (S1 `-> T1) f0 f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 S1 s0 s1 `=>
  Eq (T0 s0) (T1 s1) (f0 s0) (f1 s1)
Eq (`Quotient T0 R0 Q0) (`Quotient T1 R1 Q1) `[ t0 ] `[ t1 ] = `In
  -- to cope with heterogeneity, we have to find our way
  -- using R0 on t0 and R1 on t1 to a pair
  -- of representatives which are T0-T1-equal
  (T0 `>< \ m0 -> T1 `>< \ m1 -> 
   `Pr (R0 t0 m0 `/\ Eq T0 T1 m0 m1 `/\ R1 m1 t1))
-- off the type diagonal, Pious equality holds vacuously
Eq _ _ _ _ = `One


-- If we have an element of a (quotient) type with non-dependent
-- witness, then we
-- can get a proof that inhabitation (of that type) implies our
-- witness that the type respected its predicate
postulate
  InPr : (T : U)(A : P) -> El (T `> `Pr A) -> Pr (`In T `=> A)

-- The other direction is easy to prove
PrIn : (T : U)(A : P) -> Pr (`In T `=> A) -> El (T `> `Pr A)
PrIn T A f t = f (hide t)

-- *structural* type equality
-- i.e. this one is false off the diagonal
_<~>_ : U -> U -> P
`Zero <~> `Zero = `One
`One <~> `One = `One
`Two <~> `Two = `One
`Nat <~> `Nat = `One
  -- have to work for the next few, but it is mostly "follow the types"
(S0 `>< T0) <~> (S1 `>< T1) =
  (S0 <~> S1) `/\
  (S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 S1 s0 s1 `=> (T0 s0 <~> T1 s1))
(S0 `-> T0) <~> (S1 `-> T1) = 
  (S1 <~> S0) `/\
  (S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S1 S0 s1 s0 `=> (T0 s0 <~> T1 s1))
`Pr P0 <~> `Pr P1 = (P0 `=> P1) `/\ (P1 `=> P0)
(`Quotient T0 R0 Q0) <~> (`Quotient T1 R1 Q1) = (T0 <~> T1) `/\
   (T0 `-> \ s0 -> T1 `-> \ s1 -> Eq T0 T1 s0 s1 `=>
   (T0 `-> \ t0 -> T1 `-> \ t1 -> Eq T0 T1 t0 t1 `=>
   let P0 = R0 s0 t0 ; P1 = R1 s1 t1 in
   (P0 `=> P1) `/\ (P1 `=> P0)
  ))
_ <~> _ = `Zero


-- coercion: if we have proof that X and Y are the same type,
-- then we can coerce an element of X to an element of Y
coe : (X Y : U)(q : Pr (X <~> Y)) -> El X -> El Y

-- We need to postulate that Eq is well behaved, i.e.
-- reflexive, symmetric, transitive,
-- coherent (if X and Y are structurally equal, so are x:X and
-- y:Y gotten from coe of x)
-- and predicates (provably) respect Eq
postulate
  refl : (X : U)(x : El X) -> Pr (Eq X X x x)
  coh : (X Y : U)(q : Pr (X <~> Y))(x : El X) -> Pr (Eq X Y x (coe X Y q x))
  Resp : {X : U}{x y : El X} -> Pr (Eq X X x y) -> (P : El X -> U) -> Pr (P x <~> P y)

-- Resp implies reflexivity for structural type equality
Refl : (X : U) -> Pr (X <~> X)
Refl X = Resp {`One} _ (\ _ -> X)

-- coercions smell of subtyping
coe `One `One q _ = _
coe `Two `Two q b = b
coe `Nat `Nat q n = n
coe (S0 `>< T0) (S1 `>< T1) (qS , qT) (s0 , t0)
  with sq <- coh S0 S1 qS s0
  with s1 <- coe S0 S1 qS s0
  = s1 , coe (T0 s0) (T1 s1) (qT s0 s1 sq) t0
coe (S0 `-> T0) (S1 `-> T1) (qS , qT) f0 s1
  with sq <- coh S1 S0 qS s1
  with s0 <- coe S1 S0 qS s1
  = coe (T0 s0) (T1 s1) (qT s0 s1 sq) (f0 s0)
coe (`Pr P0) (`Pr P1) q p0 = fst q p0
coe (`Quotient T0 R0 Q0) (`Quotient T1 R1 Q1) (qT , _) `[ t0 ] = `[ coe T0 T1 qT t0 ]

module _
  (T : U)(R : El T -> El T -> P)
  (Q : Equiv (El T) (\ i j -> Pr (R i j)))
  where
  homogQuot : (t0 t1 : El T) -> Pr (R t0 t1) ->
    Pr (Eq (`Quotient T R Q) (`Quotient T R Q) `[ t0 ] `[ t1 ])
  homogQuot t0 t1 r = hide (t1 , t1 , r , refl T t1 , Equiv.eqR Q t1)

HomogTac : (T : U)(x y : El T) -> Set
HomogTac (`Quotient T R Q) `[ x ] `[ y ] = Pr (R x y)
HomogTac _ x y = Zero

homogTac : (T : U)(x y : El T) -> HomogTac T x y -> Pr (Eq T T x y)
homogTac (`Quotient T R Q) `[ x ] `[ y ] r = homogQuot T R Q x y r


-- The J combinator in this setting. This is one place where Resp is needed
module _ (X : U){x y : El X}(q : Pr (Eq X X x y)) where
  J : (P : (y : El X) -> Pr (Eq X X x y) -> U)
   -> El (P x (refl X x))
   -> El (P y q)
  J P p =
    coe (P x (refl X x)) (P y q)
      (Resp {X `>< \ y -> `Pr (Eq X X x y)}
        {x , refl X x}
        {y , q}
        (q , _)
        (\ (y , q) -> P y q))
      p


module EQPRF (X : U) where
  module _ {y z : El X} where
    _-[_>_ : (x : El X) -> Pr (Eq X X x y) -> Pr (Eq X X y z) -> Pr (Eq X X x z)
    x -[ p > q -- to prove Pr (Eq X X x z), use J with whichever of p and q
               -- has x or z on the right, somewhere we'd like a y
               -- q has z on the right
      = J X q (\ z _ -> `Pr (Eq X X x z)) p
    _<_]-_ : (x : El X) -> Pr (Eq X X y x) -> Pr (Eq X X y z) -> Pr (Eq X X x z)
    x < p ]- q -- this time, p has x on the right (J-ing q needs sym)
      = J X p (\ x _ -> `Pr (Eq X X x z)) q
    infixr 2 _-[_>_ _<_]-_
  _[QED] : (x : El X) -> Pr (Eq X X x x)
  _[QED] x = refl X x
  infixr 3 _[QED]
  

-- type equivalence via explicit morphisms
-- and irrelevant proofs of left/right inverse
-- aka type isomorphism (strictly speaking, quasi-equivalence)
_<=>_ : U -> U -> U
S <=> T
   = (S `> T) `>< \ f
  -> (T `> S) `>< \ g
  -> `Pr ( (S `-> \ s -> Eq S S s (g (f s)))
       `/\ (T `-> \ t -> Eq T T t (f (g t)))
         )

-- make it easier to work with equivalences
record _<==>_ (S T : U) : Set where
  constructor iso
  field
    fwd : El (S `> T)
    bwd : El (T `> S)
    fwd-bwd : Pr (S `-> \ s -> Eq S S s (bwd (fwd s)))
    bwd-fwd : Pr (T `-> \ t -> Eq T T t (fwd (bwd t)))

  osi : El (S <=> T)
  osi = fwd , bwd , fwd-bwd , bwd-fwd
  isFwd : (t : El T)
          (P : El T -> U)
       -> ((s : El S) -> El (P (fwd s)))
       -> El (P t)
  isFwd t P p = let open EQPRF T in 
    J T (_ < bwd-fwd t ]- _ [QED]) (\ t _ -> P t) (p (bwd t))

  isBwd : (s : El S)
          (P : El S -> U)
       -> ((t : El T) -> El (P (bwd t)))
       -> El (P s)
  isBwd s P p = let open EQPRF S in 
    J S (_ < fwd-bwd s ]- _ [QED]) (\ s _ -> P s) (p (fwd s))

  flipFwd : (s : El S)
    (P : El S -> El T -> U) ->
    ((t : El T) -> El (P (bwd t) t)) ->
    El (P s (fwd s))
  flipFwd s P p = let open EQPRF S in
    J S (_ < fwd-bwd s ]- _ [QED]) (\ x _ -> P x (fwd s)) (p (fwd s)) 

open _<==>_ public

module _ (S T : U){P : El (S <=> T) -> Set} where
  blueIso : 
    ((q : S <==> T) -> P (osi q))
    -> (f : El (S <=> T)) -> P f
  blueIso q f = q _


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
       r               -[ gf r >
       g (f r)         -[ refl (S `> R) g (f r) (k (h (f r))) (kh (f r)) >
       g (k (h (f r)))  [QED]
    )
  , (\ t -> let open EQPRF T in
       t               -[ hk t >
       h (k t)         -[ refl (S `> T) h (k t) (f (g (k t))) (fg (k t)) >
       h (f (g (k t)))  [QED]
    )

module _ (R : U) where

  _=[_>_ : forall {S T} -> R <==> S -> S <==> T -> R <==> T
  _=[_>_ {S}{T} f g = iso' (compIso R S T (osi f) (osi g))
  
  _<_]=_ : forall {S T} -> S <==> R -> S <==> T -> R <==> T
  _<_]=_ {S}{T} f g = iso' (compIso R S T (invIso S R (osi f)) (osi g))
  
  _[ISO] : R <==> R
  _[ISO] = iso' (idIso R)

  infixr 2 _=[_>_ _<_]=_
  infixr 3 _[ISO]

module _ (A : U)(S T : El A -> U)
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

---------------------------------------------------------
-- An Aut(omorphism) of a subGroup of the group of
-- type automorphisms (a permutation when X is finite).
--
-- Defined to be
-- - identity is in
-- - elements are symmetric
-- - elements compose
Aut : (X : U)(G : El (X <=> X) -> P) -> P
Aut X G =
  G (idIso X) `/\
  ((X <=> X) `-> \ f -> G f `=> G (invIso X X f)) `/\
  ((X <=> X) `-> \ f -> (X <=> X) `-> \ g ->
   G f `=> G g `=> G (compIso X X X f g)
   )

-- and short-form accessors
respId : {X : U} {G : El (X <=> X) -> P} -> Pr (Aut X G) -> Pr (G (idIso X))
respId = fst
respInv : {X : U} {G : El (X <=> X) -> P} -> Pr (Aut X G) -> Pr ((X <=> X) `-> \ f -> G f `=> G (invIso X X f))
respInv = snd - fst
respComp : {X : U} {G : El (X <=> X) -> P} -> Pr (Aut X G) ->
  Pr ((X <=> X) `-> \ f -> (X <=> X) `-> \ g ->
     G f `=> G g `=> G (compIso X X X f g)
     )
respComp = snd - snd

------------------------------------------------------------
-- Universe of description of containers
-- V : Universe
-- Vu : interepretatin of V into U

-- (Should explain why V/U stratification is needed)
data V : Set
Vu : V -> U
Ev : V -> Set
Ev T = El (Vu T)
record Grp : Set

-- Very similar to U except
-- - structural equivalence of types
-- - containers with automorphism
data V where
  `Zero `One `Two `Nat : V
  _`><_ _`->_ : (S : V)(T : Ev S -> V) -> V
  `Pr : P -> V
  _`<=>_ : (S T : V) -> V
  [_<!_] : (Sh : V)(Po : Ev Sh -> Grp)(X : V) -> V

-- Group, seen as elements of automorphism group
-- Note that groups, group actions and induced equivalence relation are all
-- needed here because they are part of the definition of the interpretation
-- of V (i.e. definition of Vu).
record Grp where
  inductive
  field
    Carrier : V
    automok : El (Vu Carrier <=> Vu Carrier) -> P
    closure : Pr (Aut (Vu Carrier) automok)

  private
    X = Vu Carrier
    G = X <=> X
  -- since we refer the components above a lot, give them names
  idAut : Pr (automok (idIso X))
  idAut = respId closure
  symAut : Pr (G `-> (\ f -> automok f `=> automok (invIso X X f)))
  symAut = respInv closure
  compAut : Pr (G `-> \ f -> G `-> \ g ->
                automok f `=> automok g `=> automok (compIso X X X f g))
  compAut = respComp closure

  AutG : U
  AutG = G
  
-- An automorphism group induces an equivalence relation
-- (Statement of this as an obligation)
module GQR (G : Grp)(X : U)(f0 f1 : El (Vu (Grp.Carrier G) `> X)) where
  open Grp G

  GrpQuoRel : U
  GrpQuoRel = AutG `>< \ g ->
                `Pr (automok g `/\ ((Vu Carrier `-> \ p -> Eq X X (f0 p) (f1 (fst g p)))))

  -- and some short-forms for this too
  isGroup : El GrpQuoRel -> El AutG
  isGroup = fst
  respAct : (g : El GrpQuoRel) -> Pr (automok (isGroup g))
  respAct gqr = fst (snd gqr)
  
-- A proof that a group (action) really does induce a quotient
GrpQuo : Grp -> V -> U
GrpQuo G X = let open Grp G in
  `Quotient
    (Vu Carrier `> Vu X)
    (\ f0 f1 -> `In (GQR.GrpQuoRel G (Vu X) f0 f1))
    ( (record
      { eqR = \ f -> hide (idIso (Vu Carrier) , idAut , \ p -> refl (Vu X) (f p))
      ; eqS = \ { f0 f1 (hide g) -> let open GQR G (Vu X) f0 f1 in
          hide
          (invIso (Vu Carrier) (Vu Carrier) (isGroup g)
          , symAut (isGroup g) (respAct g)
          , \ p -> let open EQPRF (Vu X) in
              let aut = isGroup g in
              f1 p
                -[ refl (Vu Carrier `> Vu X) f1 p (fst aut (fst (snd aut) p))
                   (snd (snd (snd aut)) p)
                 >
              f1 (fst (fst g) (fst (snd (fst g)) p))
                < snd (snd g) (fst (snd (fst g)) p) ]-
              (f0 (fst (snd (fst g)) p)) [QED]
          )}
      ; eqT = \ { f0 f1 f2 (hide g01) (hide g12) -> hide
          (compIso (Vu Carrier) (Vu Carrier) (Vu Carrier) (fst g01) (fst g12)
          , compAut (fst g01) (fst g12) (fst (snd g01)) (fst (snd g12))
          , \ p -> let open EQPRF (Vu X) in
              f0 p
                -[ snd (snd g01) p >
              f1 (fst (fst g01) p)
                -[ snd (snd g12) (fst (fst g01) p) >
              f2 (fst (fst g12) (fst (fst g01) p)) [QED]) } }))

Vu `Zero = `Zero
Vu `One = `One
Vu `Two = `Two
Vu `Nat = `Nat
Vu (S `>< T) = Vu S `>< \ s -> Vu (T s)
Vu (S `-> T) = Vu S `-> \ s -> Vu (T s)
Vu (`Pr A) = `Pr A
Vu (S `<=> T) = Vu S <=> Vu T
Vu ([ Sh <! Po ] X) = Vu Sh `>< \ s -> GrpQuo (Po s) X

--------------------------------------------------------------
-- these two are the interface to quotients we should export
--------------------------------------------------------------

Method : (T : U)(P : El T -> U) -> U
Method `Zero P = `One
Method `One P = P <>
Method `Two P = P `0 `* P `1
Method `Nat P = P ze `* (`Nat `-> \ n -> P n `> P (su n))
Method (S `>< T) P = S `-> \ s -> T s `-> \ t -> P (s , t)
Method (S `-> T) P = (S `-> T) `-> \ f -> P f
Method (`Pr p) P = `Pr p `-> \ x -> P x
Method (`Quotient T R Q) P = 
  (T `-> \ t -> P `[ t ]) `>< \ p ->
  `Pr (T `-> \ x -> T `-> \ y -> (R x y `=>
        Eq (P `[ x ]) (P `[ y ]) (p x) (p y)))

elElim : (T : U)(t : El T)(P : El T -> U)
      -> El (Method T P)
      -> El (P t)
elElim `One <> P p = p
elElim `Two `0 P (p0 , _) = p0
elElim `Two `1 P (_ , p1) = p1
elElim `Nat ze P (pz , _) = pz
elElim `Nat (su n) P p@(_ , ps) = ps n (elElim `Nat n P p)
elElim (S `>< T) (s , t) P p = p s t
elElim (S `-> T) f P p = p f
elElim (`Pr r) x P p = p x
elElim (`Quotient T R Q) `[ x ] P (p , _) = p x

[_] : forall {T : U}{R : El T -> El T -> P}{Q : Equiv (El T) (\ i j -> Pr (R i j))}
      -> El T -> El (`Quotient T R Q)
[ x ] = `[ x ]
--------------------------------------------------------------


Fin : Nat -> V
Fin ze     = `Zero
Fin (su n) = `Two `>< (`One <01> Fin n)

module _ (X : U) where
  zePlus : X <==> (`Zero `+ X)
  fwd zePlus x = `1 , x
  bwd zePlus (`1 , x) = x
  fwd-bwd zePlus x = refl X x
  bwd-fwd zePlus (`1 , x) = refl (`Zero `+ X) (`1 , x)
 
module _ (R S T : U) where
  plusAssoLR : El (((R `+ S) `+ T) `> (R `+ (S `+ T)))
  plusAssoLR (`0 , `0 , r) = `0 , r     
  plusAssoLR (`0 , `1 , s) = `1 , `0 , s
  plusAssoLR (`1 , t)      = `1 , `1 , t
  plusAssoRL : El ((R `+ (S `+ T)) `> ((R `+ S) `+ T))
  plusAssoRL (`0 , r)      = `0 , `0 , r
  plusAssoRL (`1 , `0 , s) = `0 , `1 , s
  plusAssoRL (`1 , `1 , t) = `1 , t     
  plusAsso : ((R `+ S) `+ T) <==> (R `+ (S `+ T))
  
  fwd plusAsso = plusAssoLR
  bwd plusAsso = plusAssoRL
  fwd-bwd plusAsso (`0 , `0 , r) = <> , <> , refl R r
  fwd-bwd plusAsso (`0 , `1 , s) = <> , <> , refl S s
  fwd-bwd plusAsso (`1 , t)      = <> , refl T t
  bwd-fwd plusAsso (`0 , r)      = <> , refl R r
  bwd-fwd plusAsso(`1 , `0 , s) = <> , <> , refl S s
  bwd-fwd plusAsso (`1 , `1 , t) = <> , <> , refl T t

sumFinGood : (n m : Nat) ->
  Vu (Fin (n +N m)) <==> (Vu (Fin n) `+ Vu (Fin m))
sumFinGood ze m = zePlus (Vu (Fin m))
sumFinGood (su n) m = 
  (`Two `>< \ b -> Vu ((`One <01> Fin (n +N m)) b))
     =[ sgIso `Two _ _ ((_ [ISO]) <01> sumFinGood n m) >
  (`One `+ (Vu (Fin n) `+ Vu (Fin m)))
     < plusAsso `One (Vu (Fin n)) (Vu (Fin m)) ]=
  ((`One `+ Vu (Fin n)) `+ Vu (Fin m))
     =[ sgIso `Two _ _
     (sgIso `Two _ _ ((_ [ISO]) <01> (_ [ISO])) <01> (_ [ISO])) >
  ((`Two `>< \ b -> Vu ((`One <01> Fin n) b)) `+ Vu (Fin m)) [ISO]


-- Trivial automorphism group over any V
module _ where
  open Grp
  
  Trivial : V -> Grp
  Carrier (Trivial X) = X
  automok (Trivial X) = Eq (Vu X <=> Vu X) (Vu X <=> Vu X) (idIso (Vu X))
  closure (Trivial X)
    = refl (Vu X <=> Vu X) (idIso (Vu X))
    , (\ g gq -> J (Vu X <=> Vu X) {idIso (Vu X)} {g} gq
        (\ g _ -> `Pr (Eq (Vu X <=> Vu X) (Vu X <=> Vu X) (idIso (Vu X)) (invIso (Vu X) (Vu X) g)))
        (refl (Vu X <=> Vu X) (idIso (Vu X))))
    , \ g01 g12 q01 q12 ->  J (Vu X <=> Vu X) {idIso (Vu X)} {g01} q01
        (\ g01 _ -> `Pr (Eq (Vu X <=> Vu X) (Vu X <=> Vu X)
                    (idIso (Vu X)) (compIso (Vu X) (Vu X) (Vu X) g01 g12)))
        q12

-- Lists have shapes indexed by natural numbers and Trivial automorphisms
List : V -> V
List Y = [ `Nat <! Fin - Trivial ] Y

nilL : forall Y -> Ev (List Y)
nilL Y = 0 , `[ (\ ()) ]

oneL : forall Y -> Ev Y -> Ev (List Y)
oneL Y y = 1 , `[ (\ _ -> y) ]

-- Vectors, on the other have, have trivial shape (since we know their length)
-- and still Trivial automorphisms
Vec : Nat -> V -> V
Vec n = [ `One <! (\ _ -> Trivial (Fin n)) ]

nilV : forall Y -> Ev (Vec ze Y)
nilV Y = <> , `[ (λ ()) ]

oneV : forall Y -> Ev Y -> Ev (Vec (su ze) Y)
oneV Y y = <> , `[ (λ _ → y) ]

-- General eliminator for vectors
vecElim : (Y : V)(n : Nat)(ys : Ev (Vec n Y))
  (P : Ev (Vec n Y) -> U)
  (p : (f : El (Vu (Fin n) `> Vu Y)) -> El (P (<> , `[ f ])))
  ->
  El (P ys)
vecElim Y n (<> , ys) P p = elElim (GrpQuo (Trivial (Fin n)) Y) ys (\ ys -> (P (<> , ys)))
  ( p
  , \ f0 f1 -> InPr (GQR.GrpQuoRel (Trivial (Fin n)) (Vu Y) f0 f1)
                     (Eq (P (<> , `[ f0 ])) (P (<> , `[ f1 ])) (p f0) (p f1))
                     (/\ \ g -> /\ \ gq -> J (Vu (Fin n) <=> Vu (Fin n)) {idIso (Vu (Fin n))} {g} gq
                       (\ g _ -> (Vu (Fin n) `->  \ s -> `Pr (Eq (Vu Y) (Vu Y) (f0 s) (f1 (fst g s))))
                              `> `Pr (Eq (P (<> , `[ f0 ])) (P (<> , `[ f1 ])) (p f0) (p f1)))
                       \ h -> refl ((Vu (Fin n) `> Vu Y) `-> \ f -> P (<> , `[ f ])) p f0 f1
                          \ i j ij -> J (Vu (Fin n)) {i}{j} ij
                             (\ j _ -> `Pr (Eq (Vu Y) (Vu Y) (f0 i) (f1 j)))
                             (h i))
  )


-- concatenation of two functions over Fin
catFinFun : {X : Set}(n0 n1 : Nat)(f : Ev (Fin n0) -> X)(g : Ev (Fin n1) -> X)
  -> Ev (Fin (n0 +N n1)) -> X
catFinFun ze      n1 f g i        = g i
catFinFun (su n0) n1 f g (`0 , i) = f (`0 , <>)
catFinFun (su n0) n1 f g (`1 , i) = catFinFun n0 n1 ((`1 ,_) - f) g i

module _ {X : U} where
  catLeft : (n0 n1 : Nat)(f : El (Vu (Fin n0) `> X))(g : El (Vu (Fin n1) `> X))
    (x : Ev (Fin n0)) ->
      Pr (Eq X X (catFinFun n0 n1 f g (bwd (sumFinGood n0 n1) (`0 , x))) (f x))
  catLeft (su n0) n1 f g (`0 , x) = refl X _
  catLeft (su n0) n1 f g (`1 , x) = catLeft n0 n1 ((`1 ,_) - f) g x

  catRight : (n0 n1 : Nat)(f : El (Vu (Fin n0) `> X))(g : El (Vu (Fin n1) `> X))
    (x : Ev (Fin n1)) ->
      Pr (Eq X X (catFinFun n0 n1 f g (bwd (sumFinGood n0 n1) (`1 , x))) (g x))
  catRight ze n1 f g x = refl X _
  catRight (su n0) n1 f g x = catRight n0 n1 ((`1 ,_) - f) g x


-- concatenation of lists. Note how we go through vectors to get the job done
catL : forall Y -> Ev (List Y) -> Ev (List Y) -> Ev (List Y)
catL Y (n0 , c0) (n1 , c1)
  = (n0 +N n1)
  , `[( vecElim Y n0 (<> , c0) (\ _ -> Vu (Fin (n0 +N n1)) `> Vu Y) \ ys0 ->
        vecElim Y n1 (<> , c1) (\ _ -> Vu (Fin (n0 +N n1)) `> Vu Y) \ ys1 ->
        catFinFun n0 n1 ys0 ys1 )]

catL' : forall Y -> Ev (List Y) -> Ev (List Y) -> Ev (List Y)
catL' Y (n0 , c0) (n1 , c1)
  = (n0 +N n1)
  , `[ catFinFun n0 n1
       (\ i -> vecElim Y n0 (<> , c0) (\ _ -> Vu Y) \ f -> f i)
       (\ i -> vecElim Y n1 (<> , c1) (\ _ -> Vu Y) \ f -> f i)
     ]


-- And now for Bags. They have the "full" Symm(etry) Group as Aut, so define that.
module _ where
  open Grp
  
  Symm : V -> Grp
  Carrier (Symm X) = X
  automok (Symm X) _ = `One
  closure (Symm X) = _

-- Shuffles are Unordered tuples

Shuffle : Nat -> V -> V
Shuffle n =  [ `One <! (\ _ -> Symm (Fin n)) ]

shuffleElim : (Y : V)(n : Nat)(ys : Ev (Shuffle n Y))
  (P : Ev (Shuffle n Y) -> U)
  (p : (f : El (Vu (Fin n) `> Vu Y)) -> El (P (<> , `[ f ])))
  (q : (f : El (Vu (Fin n) `> Vu Y))(g : El (Vu (Fin n) <=> Vu (Fin n))) ->
    Pr (Eq (P (<> , `[ f ])) (P (<> , `[ fst g - f ])) (p f) (p (fst g - f)))
    )
  ->
  El (P ys)
shuffleElim Y n (<> , `[ f ]) P p q = p f

module _
  (Y : V)(n : Nat)
  (P : Ev (Shuffle n Y) -> U)
  (p0 : (f : El (Vu (Fin n) `> Vu Y)) -> El (P (<> , `[ f ])))
  {q0 : (f : El (Vu (Fin n) `> Vu Y))(g : El (Vu (Fin n) <=> Vu (Fin n))) ->
    Pr (Eq (P (<> , `[ f ])) (P (<> , `[ fst g - f ])) (p0 f) (p0 (fst g - f)))
    }
  (p1 : (f : El (Vu (Fin n) `> Vu Y)) -> El (P (<> , `[ f ])))
  {q1 : (f : El (Vu (Fin n) `> Vu Y))(g : El (Vu (Fin n) <=> Vu (Fin n))) ->
    Pr (Eq (P (<> , `[ f ])) (P (<> , `[ fst g - f ])) (p1 f) (p1 (fst g - f)))
    }
  (p01 :
    Pr (Eq ((Vu (Fin n) `> Vu Y) `-> \ f -> P (<> , `[ f ]))
           ((Vu (Fin n) `> Vu Y) `-> \ f -> P (<> , `[ f ]))
       p0 p1))
  where
  shuffleElimEq : (ys : Ev (Shuffle n Y)) -> Pr (Eq (P ys) (P ys)
    (shuffleElim Y n ys P p0 q0) (shuffleElim Y n ys P p1 q1))
  shuffleElimEq (<> , `[ ys ]) = J ((Vu (Fin n) `> Vu Y) `-> \ f -> P (<> , `[ f ]))
    p01 (\ p1 _ -> `Pr (Eq (P (<> , `[ ys ])) (P (<> , `[ ys ])) (p0 ys) (p1 ys)))
    (refl (P (<> , `[ ys ])) _)
  

-- Bags are rather the simplest case in this setting!
Bag : V -> V
Bag X = [ `Nat <! Fin - Symm ] X

nilB : forall Y -> Ev (Bag Y)
nilB Y = 0 , `[ (\ ()) ]

oneB : forall Y -> Ev Y -> Ev (Bag Y)
oneB Y y = 1 , `[ (\ _ -> y) ]

finDec : (n : Nat) (P : El (Vu (Fin n)) -> Set)
 (x y : El (Vu (Fin n)))
 -> Pr (Eq (Vu (Fin n)) (Vu (Fin n)) x y) -> P x -> P y
finDec (su n) P (`0 , <>) (`0 , <>) (<> , <>) p = p
finDec (su n) P (`1 , x) (`1 , y) (<> , eq) p = finDec n (\ z -> P (`1 , z)) x y eq p 

{-
finPlusCase : (n m : Nat)
  (P : El (Vu (Fin (n +N m)))
    -> El (Vu (Fin n) `+ Vu (Fin m))
    -> Set)
  -> ((x : El (Vu (Fin n))) ->
       P (bwd (sumFinGood n m) (`0 , x)) (`0 , x))
  -> ((x : El (Vu (Fin m))) ->
       P (bwd (sumFinGood n m) (`1 , x)) (`1 , x))
  -> (s : El (Vu (Fin (n +N m)))) ->
     P s (fwd (sumFinGood n m) s)
finPlusCase ze m P l r s = r s
finPlusCase (su n) m P l r (`0 , <>) = l (`0 , <>)
finPlusCase (su n) m P l r (`1 , s)
  with fwd (sumFinGood n m) s
     | fwd-bwd  (sumFinGood n m) s
... | `0 , z | q = {!l ?!} -- l (`1 , z)
... | `1 , z | q = {!!}
-}

catB : forall Y -> Ev (Bag Y) -> Ev (Bag Y) -> Ev (Bag Y)
catB Y (n0 , c0) (n1 , c1)
  = (n0 +N n1)
  , snd (shuffleElim Y n0 (<> , c0) (\ _ -> Vu (Shuffle (n0 +N n1) Y))
      (\ ys0 -> shuffleElim Y n1 (<> , c1) (\ _ -> Vu (Shuffle (n0 +N n1) Y))
        (\ ys1 -> <> , `[ catFinFun n0 n1 ys0 ys1 ])
         \ ys1 g -> <> , hide
           ( catFinFun n0 n1 ys0 (fst g - ys1)
           , catFinFun n0 n1 ys0 (fst g - ys1)
           , (hide (osi (
               Vu (Fin (n0 +N n1)) =[ sumFinGood n0 n1 >
               (Vu (Fin n0) `+ Vu (Fin n1))
                                            < sgIso `Two _ _ ((_ [ISO]) <01> iso' g) ]=
               (Vu (Fin n0) `+ Vu (Fin n1)) < sumFinGood n0 n1 ]=
               Vu (Fin (n0 +N n1)) [ISO]
               ) , <> , \ n2 -> flipFwd (sumFinGood n0 n1) n2
                  (\ n2 x -> `Pr
      (Eq (Vu Y) (Vu Y) (catFinFun n0 n1 ys0 ys1 n2)
       (catFinFun n0 n1 ys0 (fst g - ys1)
        (fst
         (osi
          ((Vu (Fin n0) `+ Vu (Fin n1)) <
           sgIso `Two (Vu (Fin n0) <01> Vu (Fin n1))
           (Vu (Fin n0) <01> Vu (Fin n1)) ((Vu (Fin n0) [ISO]) <01> iso' g)
           ]=
           (Vu (Fin n0) `+ Vu (Fin n1)) < sumFinGood n0 n1 ]=
           Vu (Fin (n0 +N n1)) [ISO]))
         x))))
           (/\ ((\ i -> let open EQPRF (Vu Y) in
               catFinFun n0 n1 ys0 ys1 (bwd (sumFinGood n0 n1) (`0 , i))
                 -[ catLeft {Vu Y} n0 n1 ys0 _ i >
               ys0 i
                 < catLeft {Vu Y} n0 n1 ys0 _ i  ]-
               catFinFun n0 n1 ys0 (fst g - ys1)
                   (bwd (sumFinGood n0 n1) (`0 , i)) [QED])
            <01> \ j -> let open EQPRF (Vu Y) in
                catFinFun n0 n1 ys0 ys1 (bwd (sumFinGood n0 n1) (`1 , j))
                  -[ catRight {Vu Y} n0 n1 ys0 ys1 j >
                ys1 j
                  -[ refl (Vu (Fin n1) `> Vu Y) ys1 j _ (snd (snd (snd g)) j) >
                ys1 (fst g (fst (snd g) j))
                  < catRight {Vu Y} n0 n1 ys0 (fst g - ys1) (fst (snd g) j) ]-
                catFinFun n0 n1 ys0 (fst g - ys1)
                  (bwd (sumFinGood n0 n1) (`1 , fst (snd g) j)) [QED]))
                 ))
           , refl (Vu (Fin (n0 +N n1)) `> Vu Y) _
           , hide (idIso (Vu (Fin (n0 +N n1))) , <> , \ x -> refl (Vu Y) _)))
      \ ys0 -> blueIso (Vu (Fin n0)) (Vu (Fin n0)) \ q ->
        <> , homogTac (GrpQuo (Symm (Fin (n0 +N n1))) Y)
                `[ catFinFun n0 n1 ys0 _ ]
                `[ catFinFun n0 n1 (fwd q - ys0) _ ]
                (hide (osi (
               Vu (Fin (n0 +N n1)) =[ sumFinGood n0 n1 >
               (Vu (Fin n0) `+ Vu (Fin n1))
                   < sgIso `Two _ _ (q <01> (_ [ISO])) ]=
               (Vu (Fin n0) `+ Vu (Fin n1)) < sumFinGood n0 n1 ]=
               Vu (Fin (n0 +N n1)) [ISO])
                      , <>
                      , \ n2 -> flipFwd (sumFinGood n0 n1) n2
        (\ n2 x -> `Pr
        (Eq (Vu Y) (Vu Y) (catFinFun n0 n1 ys0 (Quotient.rep c1) n2)
       (catFinFun n0 n1 (fwd q - ys0) (Quotient.rep c1)
        (fst
         (osi
          ((Vu (Fin n0) `+ Vu (Fin n1)) <
           sgIso `Two (Vu (Fin n0) <01> Vu (Fin n1))
           (Vu (Fin n0) <01> Vu (Fin n1)) (q <01> (Vu (Fin n1) [ISO]))
           ]=
           (Vu (Fin n0) `+ Vu (Fin n1)) < sumFinGood n0 n1 ]=
           Vu (Fin (n0 +N n1)) [ISO]))
         x))))
        (/\ ((\ i -> let open EQPRF (Vu Y) in
           catFinFun n0 n1 ys0 (Quotient.rep c1)
             (bwd (sumFinGood n0 n1) (`0 , i))
             -[ catLeft {Vu Y} n0 n1 _ _ i >
           ys0 i
             -[ refl (Vu (Fin n0) `> Vu Y) ys0 _ _ (bwd-fwd q i) >
           ys0 (fwd q (bwd q i))
             < catLeft {Vu Y} n0 n1 _ _ (bwd q i) ]-
           catFinFun n0 n1 (fwd q - ys0) (Quotient.rep c1)
             (bwd (sumFinGood n0 n1) (`0 , bwd q i)) [QED])
        <01>
        \ j -> let open EQPRF (Vu Y) in
          catFinFun n0 n1 ys0 (Quotient.rep c1)
        (bwd (sumFinGood n0 n1) (`1 , j))
           -[ catRight {Vu Y} n0 n1 _ _ j >
          (Quotient.rep c1) j
          < catRight {Vu Y} n0 n1 _ _ j ]-
        catFinFun n0 n1 (λ a → ys0 (fwd q a)) (Quotient.rep c1)
        (bwd (sumFinGood n0 n1) (`1 , j)) [QED]))))
  )

-- the above is epic cheating, in that we see exposed representatives
-- (Quotient.rep c1) where we ought to use shuffElim and then prove
-- that what we're trying prove respects the quotient (which it does, but
-- that's not a gimme)

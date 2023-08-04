{-# OPTIONS --irrelevant-projections #-}

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

{-
-- Agda's not happy when expose is used directly, but fine with:
.join : {X : Set} -> Hide (Hide X) -> Hide X
join h = expose h
-}

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

-- Nat is useful for non-trivial examples
data Nat : Set where ze : Nat ; su : Nat -> Nat

id : forall {k}{X : Set k} -> X -> X
id x = x

-- dependent function composition, pipe style
_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  -> C a (f a)
(f - g) a = g (f a)

-- reflexive, symmetric, transitive closure of a binary relation
data QC (X : Set)(R : X -> X -> Set)(x : X) : X -> Set where
  one : {y : X} -> R x y -> QC X R x y
  rfl : QC X R x x
  sym : {y : X} -> QC X R y x -> QC X R x y
  xtv : {y z : X} -> QC X R x y -> QC X R y z -> QC X R x z

{-
PathOverQC : {X : Set}{R : X -> X -> Set}
  (P : X -> Set)(Q : (X >< P) -> (X >< P) -> Set)
  -> {x0 x1 : X} -> QC X R x0 x1
  -> P x0 -> P x1 -> Set
PathOverQC P Q (one r01) p0 p1 = Q (_ , p0) (_ , p1)
PathOverQC P Q {x0} rfl p0 p1 = QC (P x0) (\ _ _ -> Zero) p0 p1  -- BOO! HISS!
PathOverQC P Q (sym x10) p0 p1 = PathOverQC P Q x10 p1 p0
PathOverQC P Q (xtv x01 x12) p0 p2 =
  _ >< \ p1 ->
  PathOverQC P Q x01 p0 p1 >< \ _ ->
  PathOverQC P Q x12 p1 p2
-}

-- representation of quotienting by a relation
--   should be in a separate file and only a certain
--   interface exposed, so that no one can inspect the
--   implementation details. We'll just promise to be
--   good for now.
record _/_ (X : Set)(R : X -> X -> Set) : Set where
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
  `QC   : (T : U)(R : El T -> El T -> P) -> El T -> El T -> P
  -- It might be tempting to add a code for equality, but it's hard to decode.
  -- `Eq   : (S T : U) -> El S -> El T -> P

-- Straightforward Curry-Howard style representation
Pr `Zero = Zero
Pr `One = One
Pr (A `/\ B) = Pr A * Pr B
Pr (S `-> B) = (s : El S) -> Pr (B s)
Pr (`In T) = Hide (El T)
Pr (`QC T R i j) = QC (El T) (\ i j -> Pr (R i j)) i j
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
  _`/_ : (T : U)(R : El T -> El T -> P) -> U

-- Straightforward rep. 
El `Zero = Zero
El `One = One
El `Two = Two
El `Nat = Nat
El (S `>< T) = El S >< \ s -> El (T s)
El (S `-> T) = (s : El S) -> El (T s)
El (`Pr A)   = Pr A -- Hide (Pr A)
El (T `/ R)  = El T / \ x y -> Hide (Pr (R x y)) -- should explain

-- nondependent abbreviations
_`>_ _`*_ : U -> U -> U
S `> T = S `-> \ _ -> T
S `* T = S `>< \ _ -> T
infixr 5 _`>_
infixr 10 _`*_


-- "ordinary" implication, aka non-dependent
_`=>_ : P -> P -> P
A `=> B = `Pr A `-> \ _ -> B
infixr 5 _`=>_

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
Eq (T0 `/ R0) (T1 `/ R1) `[ t0 ] `[ t1 ] = `In
  -- to cope with heterogeneity, we have to find our way
  -- using R0 on t0 and R1 on t1 to a pair
  -- of representatives which are T0-T1-equal
  (T0 `>< \ m0 -> T1 `>< \ m1 -> 
   `Pr (`QC T0 R0 t0 m0 `/\ Eq T0 T1 m0 m1 `/\ `QC T1 R1 m1 t1))
-- off the type diagonal, Pious equality holds vacuously
Eq _ _ _ _ = `One


-- If we have an element of a (quotient) type with non-dependent
-- witness, then we
-- can get a proof that inhabitation (of that type) implies our
-- witness that the type respected its predicate
postulate
  InPr : (T : U)(A : P) -> El (T `-> \ _ -> `Pr A) -> Pr (`In T `=> A)

-- The other direction is easy to prove
PrIn : (T : U)(A : P) -> Pr (`In T `=> A) -> El (T `-> \ _ -> `Pr A)
PrIn T A f t = f (hide t) -- hide (f (hide (hide t)))


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
(T0 `/ R0) <~> (T1 `/ R1) = (T0 <~> T1) `/\
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


-- coercions involve a lot of shuffling data around
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
coe (T0 `/ R0) (T1 `/ R1) q `[ t0 ] = `[ coe T0 T1 (fst q) t0 ]

-- The J combinator in this setting. This is where Resp is needed
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
  


--------------------------------------------------------------
-- these two are the interface to quotients we should export
--------------------------------------------------------------
quotElim : {X : U}{R : El X -> El X -> P}
  {P : El (X `/ R) -> U}
  -> (p : El (X `-> \ x -> P `[ x ]))
  -> El (`Pr (X `-> \ x -> X `-> \ y -> (`QC X R x y `=>
        Eq (P `[ x ]) (P `[ y ]) (p x) (p y))))
  -> (c : El (X `/ R))
  -> El (P c)
quotElim p q `[ x ] = p x

[_] : forall {X}{R : El X -> El X -> P} -> El X -> El (X `/ R)
[ x ] = `[ x ]
--------------------------------------------------------------


-- type equivalence via explicit morphisms
-- and irrelevant proofs of left/right inverse
-- aka type isomorphism (strictly speaking, quasi-equivalence)
_<=>_ : U -> U -> U
S <=> T
   = (S `-> \ _ -> T) `>< \ f
  -> (T `-> \ _ -> S) `>< \ g
  -> `Pr ( (S `-> \ s -> Eq S S s (g (f s)))
       `/\ (T `-> \ t -> Eq T T t (f (g t)))
         )

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


------------------------------------------------------------
-- Universe of description of containers
-- V : Universe
-- Vu : interepretatin of V into U

-- (Should explain why V/U stratification is needed)
data V : Set
Vu : V -> U
Ev : V -> Set
Ev T = El (Vu T)

-- Very similar to U except
-- - structural equivalence of types
-- - containers with automorphism
data V where
  `Zero `One `Two `Nat : V
  _`><_ _`->_ : (S : V)(T : Ev S -> V) -> V
  `Pr : P -> V
  _`<=>_ : (S T : V) -> V
  [_<!_/_/_] : (Sh : V)(Po : Ev Sh -> V)
             (G : (s : Ev Sh) -> El (Vu (Po s) <=> Vu (Po s)) -> P)
             (p : (s : Ev Sh) -> Pr (Aut (Vu (Po s)) (G s)))
             (X : V) -> V

Vu `Zero = `Zero
Vu `One = `One
Vu `Two = `Two
Vu `Nat = `Nat
Vu (S `>< T) = Vu S `>< \ s -> Vu (T s)
Vu (S `-> T) = Vu S `-> \ s -> Vu (T s)
Vu (`Pr A) = `Pr A
Vu (S `<=> T) = Vu S <=> Vu T
Vu ([ Sh <! Po / Gr / gr ] X) =
  Vu Sh `>< \ s -- choose a shape
  ->
  -- then get the lookup functions quotiented by the group
  ((Vu (Po s) `> Vu X) `/ \ f0 f1
    -> (Vu (Po s) <=> Vu (Po s)) `-> \ g
    -> Gr s g `=> (Vu (Po s) `-> \ p -> Eq (Vu X) (Vu X) (f0 p) (f1 (fst g p))))

{- We didn't use gr because QC imposes equivalence closure. Perhaps we should
demand an equivalence rather than extending to one. -}

Fin : Nat -> V
Fin ze     = `Zero
Fin (su n) = `Two `>< (Fin n <01> `One)


Trivial : (X : U) -> Pr (Aut X \ f -> Eq (X <=> X) (X <=> X) f (idIso X))
-- ha ha
Trivial X
  = ( (\ _ _ q -> q)
    , (\ _ _ q -> q)
    , <>)
  , (\ _ (fid , gid , <>) -> gid , fid , <> )
  , \ (f , g , _) (h , k , _)
      (fid , gid , <>) (hid , kid , <>)
    -> (\ x y q -> hid (f x) y (fid x y q))
     , (\ x y q -> gid (k x) y (kid x y q))
     , <>

List : V -> V
List Y = [ `Nat <! Fin
         / (\ n f -> let X = Vu (Fin n) in Eq (X <=> X) (X <=> X) f (idIso X))
         / (\ n -> Trivial (Vu (Fin n))) ] Y


-- Everything is related to everything else, trivially
Liberal : (X : U) -> Pr (Aut X \ f -> `One)
Liberal X = _

-- Symmetric group is exactly the full Automorphism group
SymmetricGroup : (n : Nat) -> El (Vu (Fin n) <=> Vu (Fin n)) -> P
SymmetricGroup n = \ _ -> `One

-- Bags are rather the simplest case in this setting!
Bag : V -> V
Bag X = [ `Nat <! Fin / (\ n f -> `One ) / _ ] X


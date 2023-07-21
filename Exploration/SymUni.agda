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

-- Agda's not happy when expose is used directly, but fine with:
.join : {X : Set} -> Hide (Hide X) -> Hide X
join h = expose h

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

-- Straightforward Curry-Howard style representation
Pr `Zero = Zero
Pr `One = One
Pr (A `/\ B) = Pr A * Pr B
Pr (S `-> B) = (s : El S) -> Pr (B s)
Pr (`In T) = Hide (El T)
Pr (`QC T R i j) = QC (El T) (\ i j -> Pr (R i j)) i j

-- We need to be able to talk about equality of
--  representations
-- Note that P/Pr don't depend on this directly
Eq : (S T : U) -> El S -> El T -> P

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
El (`Pr A)   = Hide (Pr A)
El (T `/ R)  = El T / \ x y -> Hide (Pr (R x y)) -- should explain

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
  S0 `-> \ s0 -> S1 `-> \ s1 -> `Pr (Eq S0 S1 s0 s1) `-> \ _ ->
  Eq (T0 s0) (T1 s1) (f0 s0) (f1 s1)
Eq (T0 `/ R0) (T1 `/ R1) `[ t0 ] `[ t1 ] = `In
  (T0 `>< \ m0 -> T1 `>< \ m1 -> 
   `Pr (`QC T0 R0 t0 m0) `>< \ _ ->
   `Pr (Eq T0 T1 m0 m1) `>< \ _ ->
   `Pr (`QC T1 R1 m1 t1) )
-- off the type diagonal, Pious equality holds vacuously
Eq _ _ _ _ = `One

-- Equality of representatives of given types, which must
-- by done as a proof of said (Pious heterogeneous) equality
--
-- S, T made implicit; Eq makes sure that is fine
record EQ {S T : U}(s : El S)(t : El T) : Set where
  constructor eq
  field [=_=] : Pr (Eq S T s t)
open EQ public

-- "ordinary" implication, aka non-dependent
_`=>_ : P -> P -> P
A `=> B = `Pr A `-> \ _ -> B

-- If we have an element of a (quotient) type with non-dependent
-- witness, then we
-- can get a proof that inhabitation (of that type) implies our
-- witness that the type respected its predicate
postulate
  InPr : (T : U)(A : P) -> El (T `-> \ _ -> `Pr A) -> Pr (`In T `=> A)

-- The other direction is easy to prove
PrIn : (T : U)(A : P) -> Pr (`In T `=> A) -> El (T `-> \ _ -> `Pr A)
PrIn T A f t = hide (f (hide (hide t)))

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
coe : (X Y : U)(q : Hide (Pr (X <~> Y))) -> El X -> El Y

-- We need to postulate that EQ is well behaved, i.e.
-- reflexive, symmetric, transitive,
-- coherent (if X and Y are structurally equal, so are x:X and
-- y:Y gotten from coe of x)
-- and predicates (provably) respect EQ
postulate
  .refl : {X : U}{x : El X} -> EQ x x
  ._-[_>_ : forall {X : U}(x : El X){y z : El X}
    -> Pr (Eq X X x y)
    -> EQ y z
    -> EQ x z
  ._<_]-_ : forall {X : U}(x : El X){y z : El X}
    -> EQ y x
    -> EQ y z
    -> EQ x z
  .coh : (X Y : U)(q : Hide (Pr (X <~> Y)))(x : El X) -> EQ x (coe X Y q x)
  .Resp : {X : U}{x y : El X} -> EQ x y -> (P : El X -> U) -> Pr (P x <~> P y)

._[QED] : {X : U}(x : El X) -> EQ x x
x [QED] = refl

-- coercions involve a lot of shuffling data around
coe `One `One q _ = _
coe `Two `Two q b = b
coe `Nat `Nat q n = n
coe (S0 `>< T0) (S1 `>< T1) (hide q) (s0 , t0)
  with hide sq <- hide (coh S0 S1 (hide (fst q)) s0)
  with s1 <- coe S0 S1 (hide (fst q)) s0
     = s1 , coe (T0 s0) (T1 s1) (hide (snd q s0 s1 (hide [= sq =]))) t0

coe (S0 `-> T0) (S1 `-> T1) (hide q) f0 s1
  with hide sq <- hide (coh S1 S0 (hide (fst q)) s1)
  with s0 <- coe S1 S0 (hide (fst q)) s1
     = coe (T0 s0) (T1 s1) (hide (snd q s0 s1 (hide [= sq =]))) (f0 s0)
coe (`Pr P0) (`Pr P1) (hide q) p0 = hide (fst q p0)
coe (T0 `/ R0) (T1 `/ R1) (hide q) `[ t0 ] = `[ coe T0 T1 (hide (fst q)) t0 ]

-- The J combinator in this setting. This is where Resp is needed
J : {X : U}{x y : El X}(q : Hide (EQ x y))
    (P : (y : El X) -> Hide (EQ x y) -> U)
 -> El (P x (hide refl))
 -> El (P y q)
J {X}{x}{y} (hide q) P p =
  coe (P x (hide refl)) (P y (hide q)) (hide (
    Resp {X `>< \ y -> `Pr (Eq X X x y)}
      {x , hide [= refl{X}{x} =]}{y , hide [= q =]}
      (eq ([= q =] , _))
      (\ (y , hide q) -> P y (hide (eq q))))) p

infixr 2 _-[_>_ _<_]-_
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

-- show Iso is an equivalence relation
idIso : {X : U} -> El (X <=> X)
idIso {X} = id , id , hide ((\ x -> [= refl{X}{x} =]) , (\ x -> [= refl{X}{x} =]))

invIso : {S T : U} -> El (S <=> T) -> El (T <=> S)
invIso (f , g , hide p) = g , f , hide (snd p , fst p)

compIso : {R S T : U} -> El (R <=> S) -> El (S <=> T) -> El (R <=> T)
compIso (f , g , hide p) (h , k , hide q)
  = (f - h)
  , (k - g)
  , hide ((\ r -> 
     [= r              -[ fst p r >
        g (f r)        -[ [= g [QED] =] (f r) (k (h (f r))) (hide (fst q (f r))) >
        g (k (h (f r))) [QED]
     =])
   , \ t ->
     [= t              -[ snd q t >
        h (k t)        -[ [= h [QED] =] (k t) (f (g (k t))) (hide (snd p (k t))) >
        h (f (g (k t))) [QED]
     =])

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
  G idIso `/\
  (((X <=> X) `-> \ f -> `Pr (G f) `-> \ _ -> G (invIso f)) `/\
  ((X <=> X) `-> \ f -> (X <=> X) `-> \ g ->
   `Pr (G f) `-> \ _ -> `Pr (G g) `-> \ _ ->
   G (compIso f g)))

------------------------------------------------------------
-- Universe of description of containers
-- V : Universe
-- Vu : interepretatin of V into U

-- (Should explain why V/U stratification is needed)
data V : Set
Vu : V -> U

-- Very similar to U except
-- - structural equivalence of types
-- - containers with automorphism
data V where
  `Zero `One `Two `Nat : V
  _`><_ _`->_ : (S : V)(T : El (Vu S) -> V) -> V
  `Pr : P -> V
  _`<=>_ : (S T : V) -> V
  [_<!_/_/_] : (Sh : V)(Po : El (Vu Sh) -> V)
             (G : (s : El (Vu Sh)) -> El (Vu (Po s) <=> Vu (Po s)) -> P)
             (p : (s : El (Vu Sh)) -> Hide (Pr (Aut (Vu (Po s)) (G s))))
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
  ((Vu (Po s) `-> \ _ -> Vu X) `/ \ f0 f1
    -> (Vu (Po s) <=> Vu (Po s)) `-> \ g
    -> Gr s g `=> (Vu (Po s) `-> \ p -> Eq (Vu X) (Vu X) (f0 p) (f1 (fst g p))))

{- We didn't use gr because QC imposes equivalence closure. Perhaps we should
demand an equivalence rather than extending to one. -}

Fin : Nat -> V
Fin ze     = `Zero
Fin (su n) = `Two `>< (Fin n <01> `One)

{- need trivial groups for lists
.Trivial : (X : U) -> Pr (Aut X \ f -> Eq (X <=> X) (X <=> X) f (idIso X))
Trivial X = ((\ { x y q -> expose q }) , (\ x y q -> expose q) , _)
      , (\ (f , g , q) y -> {!!})
      , {!!}
-}

-- Everything is related to everything else, trivially
Liberal : (X : U) -> Pr (Aut X \ f -> `One)
Liberal X = _

-- Symmetric group is exactly the full Automorphism group
SymmetricGroup : (n : Nat) -> El (Vu (Fin n) <=> Vu (Fin n)) -> P
SymmetricGroup n = \ _ -> `One

-- Bags are rather the simplest case in this setting!
Bag : V -> V
Bag X = [ `Nat <! Fin / (\ n f -> `One ) / _ ] X

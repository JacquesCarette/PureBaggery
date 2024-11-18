module ExtUni where

open import Basics
open import Quotient

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


-- false, true, and, implication, inhabitation
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

-- n-ary predicates (over U, in P)
ALLCOD : Nat -> U -> Set
ALLCOD ze S = P
ALLCOD (su n) S = El S -> ALLCOD n S
ALL : (n : Nat)(S : U) -> ALLCOD n S -> P
ALL ze S P = P
ALL (su n) S P = S `-> \ s -> ALL n S (P s)

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

-- non-dependent coproduct
_`+_ : U -> U -> U
S `+ T = `Two `>< (S <01> T)

-- "ordinary" implication, aka non-dependent
_`=>_ : P -> P -> P
A `=> B = `Pr A `-> \ _ -> B
infixr 5 _`=>_

-- Predicate representing inhabitation of a (unary) relation R
_`#_ : (X : U) -> (El X -> P) -> P
X `# R = `In (X `>< \ x -> `Pr (R x))

--------------------------------------------------------------------------
postulate irr : (A : P) -> Hide (Pr A) -> Pr A
{-
irr `One (hide p) = _
irr (A `/\ B) (hide p) = irr A (hide (fst p)) , irr B (hide (snd p))
irr (S `-> T) (hide p) s = irr (T s) (hide (p s))
irr (`In T) (hide p) = hide {!expose p!}
-}

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

-- 'omogeneous 'quality
Oq : (T : U) -> El T -> El T -> P
Oq T = Eq T T


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
  refl : (X : U)(x : El X) -> Pr (Oq X x x)
  coh : (X Y : U)(q : Pr (X <~> Y))(x : El X) -> Pr (Eq X Y x (coe X Y q x))
  Resp : {X : U}{x y : El X} -> Pr (Oq X x y) -> (P : El X -> U) -> Pr (P x <~> P y)

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

-- The J combinator in this setting. This is one place where Resp is needed
module _ (X : U){x y : El X}(q : Pr (Oq X x y)) where
  J : (P : (y : El X) -> Pr (Oq X x y) -> U)
   -> El (P x (refl X x))
   -> El (P y q)
  J P p =
    coe (P x (refl X x)) (P y q)
      (Resp {X `>< \ y -> `Pr (Oq X x y)}
        {x , refl X x}
        {y , q}
        (q , _)
        (\ (y , q) -> P y q))
      p

  subst : (P : El X -> U) -> El (P x `> P y)
  subst P = J (\ y _ -> P y)

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

-- Fin

_<_ : Nat -> Nat -> P
x < ze = `Zero
ze < su y = `One
su x < su y = x < y

Fin : Nat -> U
Fin n = `Nat `>< \ i -> `Pr (i < n)


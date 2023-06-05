module SymUni where

record Hide (X : Set) : Set where
  constructor hide
  field
    .expose : X

data Zero' : Set where
Zero = Hide Zero'
record One : Set where constructor <>
data Two : Set where `0 `1 : Two
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

id : forall {k}{X : Set k} -> X -> X
id x = x

_-_ : forall {i j k}{A : Set i}{B : A -> Set j}{C : (a : A) -> B a -> Set k}
  (f : (a : A) -> B a)
  (g : {a : A}(b : B a) -> C a b)
  (a : A)
  -> C a (f a)
(f - g) a = g (f a)

data P : Set
Pr : P -> Set
data U : Set
El : U -> Set

data P where
  `Zero `One : P
  _`/\_ : (S : P)(T : P) -> P
  _`->_ : (S : U)(T : El S -> P) -> P

Pr `Zero = Zero
Pr `One = One
Pr (P `/\ Q) = Pr P * Pr Q
Pr (S `-> P) = (s : El S) -> Pr (P s)

Eq : (S T : U) -> El S -> El T -> P

data U where
  `Zero `One `Two : U
  _`><_ _`->_ : (S : U)(T : El S -> U) -> U
  `Pr : P -> U

El `Zero = Zero
El `One = One
El `Two = Two
El (S `>< T) = El S >< \ s -> El (T s)
El (S `-> T) = (s : El S) -> El (T s)
El (`Pr P)   = Hide (Pr P)

Eq `One `One  _  _ = `One
Eq `Two `Two `0 `0 = `One
Eq `Two `Two `0 `1 = `Zero
Eq `Two `Two `1 `0 = `Zero
Eq `Two `Two `1 `1 = `One
Eq (S0 `>< T0) (S1 `>< T1) (s0 , t0) (s1 , t1) =
  Eq S0 S1 s0 s1 `/\ Eq (T0 s0) (T1 s1) t0 t1 
Eq (S0 `-> T0) (S1 `-> T1) f0 f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> `Pr (Eq S0 S1 s0 s1) `-> \ _ ->
  Eq (T0 s0) (T1 s1) (f0 s0) (f1 s1) 
Eq _ _ _ _ = `One

record EQ (S T : U)(s : El S)(t : El T) : Set where
  constructor eq
  field [=_=] : Pr (Eq S T s t)
open EQ public

_<~>_ : U -> U -> P
`Zero <~> `Zero = `One
`One <~> `One = `One
`Two <~> `Two = `One
(S0 `>< T0) <~> (S1 `>< T1) =
  (S0 <~> S1) `/\ (
  S0 `-> \ s0 -> S1 `-> \ s1 -> `Pr (Eq S0 S1 s0 s1) `-> \ _ ->
  T0 s0 <~> T1 s1 )
(S0 `-> T0) <~> (S1 `-> T1) = 
  (S1 <~> S0) `/\ (
  S0 `-> \ s0 -> S1 `-> \ s1 -> `Pr (Eq S1 S0 s1 s0) `-> \ _ ->
  T0 s0 <~> T1 s1 )
`Pr P0 <~> `Pr P1 = (`Pr P0 `-> \ _ -> P1) `/\ (`Pr P1 `-> \ _ -> P0)
_ <~> _ = `Zero

coe : (X Y : U)(q : Hide (Pr (X <~> Y))) -> El X -> El Y

postulate
  .refl : {X : U}{x : El X} -> EQ X X x x
  ._-[_>_ : forall {X : U}(x : El X){y z : El X}
    -> Pr (Eq X X x y)
    -> EQ X X y z
    -> EQ X X x z
  ._<_]-_ : forall {X : U}(x : El X){y z : El X}
    -> EQ X X y x
    -> EQ X X y z
    -> EQ X X x z
  ._[QED] : {X : U}(x : El X) -> EQ X X x x
  .coh : (X Y : U)(q : Hide (Pr (X <~> Y)))(x : El X) -> EQ X Y x (coe X Y q x)
  .Resp : {X : U}{x y : El X} -> EQ X X x y -> (P : El X -> U) -> Pr (P x <~> P y)

coe `One `One q _ = _
coe `Two `Two q b = b
coe (S0 `>< T0) (S1 `>< T1) (hide q) (s0 , t0)
  with hide sq <- hide (coh S0 S1 (hide (fst q)) s0)
  with s1 <- coe S0 S1 (hide (fst q)) s0
     = s1 , coe (T0 s0) (T1 s1) (hide (snd q s0 s1 (hide [= sq =]))) t0

coe (S0 `-> T0) (S1 `-> T1) (hide q) f0 s1
  with hide sq <- hide (coh S1 S0 (hide (fst q)) s1)
  with s0 <- coe S1 S0 (hide (fst q)) s1
     = coe (T0 s0) (T1 s1) (hide (snd q s0 s1 (hide [= sq =]))) (f0 s0)
coe (`Pr P0) (`Pr P1) (hide q) p0 = hide (fst q p0)

J : {X : U}{x y : El X}(q : Hide (EQ X X x y))
    (P : (y : El X) -> Hide (EQ X X x y) -> U)
 -> El (P x (hide refl))
 -> El (P y q)
J {X}{x}{y} (hide q) P p =
  coe (P x (hide refl)) (P y (hide q)) (hide (
    Resp {X `>< \ y -> `Pr (Eq X X x y)}
      {x , hide [= refl =]}{y , hide [= q =]}
      (eq ([= q =] , _))
      (\ (y , hide q) -> P y (hide (eq q))))) p

infixr 2 _-[_>_ _<_]-_
infixr 3 _[QED]

_<=>_ : U -> U -> U
S <=> T
   = (S `-> \ _ -> T) `>< \ f
  -> (T `-> \ _ -> S) `>< \ g
  -> `Pr ( (S `-> \ s -> Eq S S s (g (f s)))
       `/\ (T `-> \ t -> Eq T T t (f (g t)))
         )

idIso : (X : U) -> El (X <=> X)
idIso X = id , id , hide ((\ x -> [= refl =]) , (\ x -> [= refl =]))

invIso : (S T : U) -> El (S <=> T) -> El (T <=> S)
invIso S T (f , g , hide p) = g , f , hide (snd p , fst p)

compIso : (R S T : U) -> El (R <=> S) -> El (S <=> T) -> El (R <=> T)
compIso R S T (f , g , hide p) (h , k , hide q)
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

Aut : (X : U)(G : El (X <=> X) -> P) -> P
Aut X G =
  G (idIso X) `/\
  (((X <=> X) `-> \ f -> `Pr (G f) `-> \ _ -> G (invIso X X f)) `/\
  ((X <=> X) `-> \ f -> (X <=> X) `-> \ g ->
   `Pr (G f) `-> \ _ -> `Pr (G g) `-> \ _ ->
   G (compIso X X X f g)))

data V : Set
Vu : V -> U

data V where
  `Zero `One `Two : V
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
Vu (S `>< T) = Vu S `>< \ s -> Vu (T s)
Vu (S `-> T) = Vu S `-> \ s -> Vu (T s)
Vu (`Pr P) = `Pr P
Vu (S `<=> T) = Vu S <=> Vu T
Vu ([ S <! P / G / p ] X) =
  Vu S `>< \ s -> Vu (P s) `-> \ p -> Vu X
  -- LIES!
  

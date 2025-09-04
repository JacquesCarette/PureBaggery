module UniversesInductiveTables where

open import String

open import Basics

data Kind : Set where
  Data Extensional Props : Kind

-- only two of the universes can have extensional functions
canHazPi : Kind -> Set
canHazPi Extensional = One
canHazPi Props       = One
canHazPi _           = Zero

-- only some places have enumerations (Listable, really), namely not Props
canHazEnum : Kind -> Set
canHazEnum Props = Zero
canHazEnum _     = One

-- a couple of universes have (internal!!) lists
canHazList : Kind -> Set
canHazList Data = One
canHazList Extensional = One
canHazList _ = Zero

-- we don't want this to be polymorphic
-- evidence of where a in L actually is
data _-in_ (a : String) : (L : List String) -> Set where
  ze : {as : List String} -> a -in (a ,- as)
  su : {b : String} {as : List String} -> a -in as -> a -in (b ,- as)

-- is a in L ?
_-In_ : (a : String) -> (L : List String) -> Set
a -In [] = Zero
a -In (x ,- l) with primStringEquality a x
... | `0 = a -In l
... | `1 = One

-- when we know a is in l, we can (fairly silently) get to know where something is
--  (which, magically, is going to be a, but we don't / can't promise that)
$ : (a : String) -> {l : List String} -> {_ : a -In l} -> <: _-in l :>
$ a {x ,- l} {p} with primStringEquality a x
... | `0 = (_ >><< su) ($ a {l} {p})
... | `1 = _ , ze

-- Introduce the Finite universe on its own
data UF : Set
ElF : UF -> Set

data UF where
  -- Closed under tagging
  _`$<_ : (xs : List String {-UF-}) -> (T : <: _-in xs :> {-ElF S-} -> UF) -> UF

  -- Zero and One with eta
  -- `0
  `1 : UF

  -- enumerations with no eta
  -- `E : List String -> UF

ElF (xs `$< T) = <: _-in xs :> {-ElF S-} >< \ s -> ElF (T s)
-- ElF `0 = Zero
ElF `1 = One
-- ElF (`E l) =  <: _-in l :>

-- expand out a list of strings into a type-level tuple of positions into that list
-- TODO? could re-jig this to use the String interface instead of the positional one
data Tuple (xs : List String) (T : <: _-in xs :> -> Set) : Set
Tuple' : (xs : List String) (T : <: _-in xs :> -> Set) -> Set
data Tuple xs T where
  <_> : Tuple' xs T -> Tuple xs T
Tuple' [] T = One
Tuple' (x ,- xs) T = T (_ , ze) * Tuple xs \ (_ , i) -> T (_ , su i)

mapTuple : (xs : List String) {T0 T1 : <: _-in xs :> -> Set} (f : [: T0 -:> T1 :] ) ->
  Tuple xs T0 -> Tuple xs T1
mapTuple [] f < <> > = < <> >
mapTuple (x ,- xs) f < t , ts > = < f _ t , mapTuple xs (\ (_ , i) -> f (_ , su i)) ts >

-- tabulation for enumeration
tab : (xs : List String) {T : <: _-in xs :> -> Set} -> [: T :] -> Tuple xs T
tab [] f = < <> >
tab (x ,- xs) f = < f (_ , ze) , (tab xs (\ (_ , i) -> f (_ , su i))) >

-- projection for inverting tab
proj : (xs : List String) {T : <: _-in xs :> -> Set} -> Tuple xs T -> [: T :]
proj (x ,- xs) < t , ts > (_ , ze) = t
proj (x ,- xs) < t , ts > (_ , su i) = proj xs ts (_ , i)

_#>_ : (S : UF) -> (R : ElF S -> Set) -> Set
(xs `$< T) #> R = Tuple xs \ x -> T x #> \ t -> R (x , t)
`1 #> R = R <>

-- Some External kit for tabulated functions


-- tabulation for finite functions
fflam : (S : UF) {R : ElF S -> Set} -> (f : [: R :]) -> (S #> R)
fflam (xs `$< T) f = tab xs \ x -> fflam (T x) \ t -> f (x , t)
fflam `1 f = f <>

-- using such tabulated functions
ffapp : (S : UF) {R : ElF S -> Set} -> (S #> R) -> [: R :]
ffapp (xs `$< T) rs (x , t) = ffapp (T x) (proj xs rs x) t
ffapp `1 r <> = r

_`>F<_ : (S : UF)(T : ElF S -> UF) -> UF
(xs `$< S) `>F< T = xs `$< \ x -> S x `>F< \ s -> T (x , s)
`1 `>F< T = T <>

pair : (S : UF){T : ElF S -> UF}(s : ElF S)(t : ElF (T s)) -> ElF (S `>F< T)
pair (xs `$< T) (x , s) t = x , pair (T x) s t
pair `1 <> t = t

pfst : (S : UF){T : ElF S -> UF}(p : ElF (S `>F< T)) -> ElF S
pfst (xs `$< T) (x , p) = x , pfst (T x) p
pfst `1 p = <>

psnd : (S : UF){T : ElF S -> UF}(p : ElF (S `>F< T)) -> ElF (T (pfst S p))
psnd (xs `$< T) (x , p) = psnd (T x) p
psnd `1 t = t

-- Internal versions of pair, Tuple, tabulated functions,
-- tabulation, projection, lam and app
-- which were basically already there
_`*_ : UF -> UF -> UF
S `* T = S `>F< (kon T)

`Tuple : (l : List String) (T : <: _-in l :> -> UF) -> UF
`Tuple [] T = `1
`Tuple (x ,- xs) T = T (_ , ze) `* `Tuple xs \ (_ , i) -> T (_ , su i)

-- tabulation for enumeration
`tab : (xs : List String) {T : <: _-in xs :> -> UF} -> [: T - ElF :] -> ElF (`Tuple xs T)
`tab [] f = <>
`tab (x ,- xs) {T} f = pair (T (_ , ze)) (f (_ , ze)) (`tab xs (\ (_ , i) -> f (_ , su i)))

-- projection for inverting tab
`proj : (xs : List String) {T : <: _-in xs :> -> UF} -> ElF (`Tuple xs T) -> [: T - ElF :]
`proj (x ,- xs) {T} t0ts (_ , ze) = pfst (T (_ , ze)) t0ts
`proj (x ,- xs) {T} t0ts (_ , su i) = `proj xs (psnd (T (_ , ze)) t0ts) (_ , i)

_`#>_ : (S : UF) -> (R : ElF S -> UF) -> UF
(xs `$< T) `#> R = `Tuple xs \ x -> T x `#> \ t -> R (x , t)
`1 `#> R = R <>

-- tabulation for finite functions
`fflam : (S : UF) {T : ElF S -> UF} -> (f : [: T - ElF :]) -> ElF (S `#> T)
`fflam (xs `$< T) f = `tab xs \ x -> `fflam (T x) \ t -> f (x , t)
`fflam `1 f = f <>

-- using such tabulated functions
`ffapp : (S : UF) {T : ElF S -> UF} -> ElF (S `#> T) -> [: T - ElF :]
`ffapp (xs `$< T) rs (x , t) = `ffapp (T x) (`proj xs rs x) t
`ffapp `1 r <> = r

-- TODO at some point, we'll need to know the above are all compatible

data Mu (Ix : Set) (Sh : Ix -> Set) (Pos : (i : Ix) -> Sh i -> UF)
  (posix : (i : Ix) (s : Sh i) (p : ElF (Pos i s)) -> Ix) (i : Ix) : Set where
  con : (s : Sh i) -> (Pos i s #> \ p -> Mu Ix Sh Pos posix (posix i s p)) -> Mu Ix Sh Pos posix i
  
-- And now the polymorphic universes
data U (k : Kind) : Set
El : forall {k : Kind} -> U k -> Set

-- Convention: capital letters for big things
data U k where
  -- All universes are closed under Sigma
  _`><_ : (S : U k) -> (T : El S -> U k) -> U k

  -- only some universes have Zero and One
  `0 `1 : U k

  -- Higher-order functions
  _`->_ : {_ : canHazPi k} -> (S : U Extensional) -> (T : El S -> U k) -> U k

  -- Tabulated functions
  _`#>>_ : (S : UF) -> (T : ElF S -> U k) -> U k

  -- enumerations
  `E : {_ : canHazEnum k} -> List String -> U k

  -- lists
  `List : {_ : canHazList k} -> U k -> U k

  -- fixed points (of indexed containers). For now, Finite positions.
  `Mu : (Ix : U Extensional) -> (Sh : El Ix -> U k) ->
    (Pos : (i : El Ix) (s : El (Sh i)) -> UF) ->
    (posix : (i : El Ix) (s : El (Sh i)) (p : ElF (Pos i s)) -> El Ix) ->
    El Ix -> U k

  -- Making things out of proofs
  `Prf : U Props -> U k

El (S `>< T) = El S >< \ s -> El (T s)
El `0 = Zero
El `1 = One
El (S `-> T) = (s : El S) -> El (T s)
El (S `#>> T) = S #> \ s -> El (T s)
El (`E l) = <: _-in l :>
El (`List S) = List (El S)
El (`Mu Ix Sh Pos posix i) = Mu (El Ix) (\ i -> El (Sh i)) Pos posix i
El (`Prf p) = El p

-- Some useful kit for (at least) proofs
_`/\_ : U Props -> U Props -> U Props
P0 `/\ P1 = P0 `>< (kon P1)

_`=>_ : U Props -> U Props -> U Props
P0 `=> P1 = `Prf P0 `-> (kon P1)

UFINITE UPROPS UDATA UEXTENSIONAL : Fam Set
UFINITE = fam UF ElF
UPROPS = fam (U Props) El
UDATA = fam (U Data) El
UEXTENSIONAL = fam (U Extensional) El


----------------------------------------------------------------------------
-- Now we have to construct value equality

-- We can embed UF types into U Data, but we need a backwards map
-- to cope with the dependency inherent in `><
F2D : (S : UF) -> U Data >< \ T -> El T -> ElF S
F2D (xs `$< T) .fst = `E xs `>< \ x -> F2D (T x) .fst
F2D (xs `$< T) .snd (x , t) = x , F2D (T x) .snd t
F2D `1 .fst = `1
F2D `1 .snd = _



Enum-Eq : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> U Props
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , ze) = `1
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , su j) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , ze) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , su j) = Enum-Eq xs (_ , i) ys (_ , j)

Enum-refl : (xs : List String)(xi : <: _-in xs :>) -> El (Enum-Eq xs xi xs xi)
Enum-refl (x ,- xs) (_ , ze) = <>
Enum-refl (x ,- xs) (_ , su i) = Enum-refl xs (_ , i)

Enum-EqDec : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> Decision UPROPS
Enum-EqDec xs xi ys yj .Naw = Enum-Eq xs xi ys yj `=> `0
Enum-EqDec xs xi ys yj .Aye = Enum-Eq xs xi ys yj
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , ze) .decide = `1 , _
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , su _) .decide = `0 , \ ()
Enum-EqDec (_ ,- _) (_ , su _) (_ ,- _) (_ , ze) .decide = `0 , \ ()
Enum-EqDec (_ ,- xs) (_ , su i) (_ ,- ys) (_ , su j) .decide = Enum-EqDec xs (_ , i) ys (_ , j) .decide
-- would normally expect to say something more detailed and positional, so let's
Enum-EqDec (_ ,- _) (_ , ze) (_ ,- _) (_ , ze) .exclude naw aye = naw aye
Enum-EqDec (_ ,- xs) (_ , su i) (_ ,- ys) (_ , su j) .exclude naw aye =
  Enum-EqDec xs (_ , i) ys (_ , j) .exclude naw aye


-- UF value equality
EqF : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> U Props
EqF (xs0 `$< T0) (x0 , t0) (xs1 `$< T1) (x1 , t1) =
  Enum-Eq xs0 x0 xs1 x1 `/\ EqF (T0 x0) t0 (T1 x1) t1
EqF _ _ _ _ = `1

EqFDec : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> Decision UPROPS
EqFDec T0 t0 T1 t1 .Naw = EqF T0 t0 T1 t1 `=> `0  -- can we do better?
EqFDec T0 t0 T1 t1 .Aye = EqF T0 t0 T1 t1
EqFDec T0 t0 T1 t1 .exclude naw aye = naw aye
EqFDec (xs0 `$< T0) (x0 , t0) (xs1 `$< T1) (x1 , t1) .decide with Enum-EqDec xs0 x0 xs1 x1 .decide
... | `0 , r = `0 , fst - r
... | `1 , q with EqFDec (T0 x0) t0 (T1 x1) t1 .decide
... | `0 , r = `0 , snd - r
... | `1 , r = `1 , q , r
EqFDec (xs `$< T) t0 `1 t1 .decide = `1 , _
EqFDec `1 t0 (xs `$< T) t1 .decide = `1 , _
EqFDec `1 t0 `1 t1 .decide = `1 , _

-- transport is tricky
f2d : (S : UF) -> let S' , f = F2D S
   in (s : ElF S)
   -> El S' >< \ s' -> El (EqF S s S (f s'))
f2d (xs `$< T) (x , t) .fst = x , f2d (T x) t .fst
f2d (xs `$< T) (x , t) .snd = (Enum-refl xs x) , (f2d (T x) t .snd)
f2d `1 <> = _


-- when we are two enumerations related pointwise?
Enum-Rel : (xs ys : List String) (R : <: _-in xs :> -> <: _-in ys :> -> U Props) -> U Props
Enum-Rel (x ,- xs) (y ,- ys) R = R (x , ze) (y , ze) `/\ Enum-Rel xs ys \ (_ , i) (_ , j) -> R (_ , su i) (_ , su j)
Enum-Rel _         _         _ = `1

-- when are elements of two finite types "pointwise" related?
ElF-Rel : (S0 S1 : UF) -> (ElF S0 -> ElF S1 -> U Props) -> U Props
ElF-Rel (xs0 `$< T0) (xs1 `$< T1) R = Enum-Rel xs0 xs1 \ x0 x1 -> ElF-Rel (T0 x0) (T1 x1) \ t0 t1 -> R (x0 , t0) (x1 , t1)
ElF-Rel (xs `$< T) `1 R = `1
ElF-Rel `1 (xs `$< T) R = `1
ElF-Rel `1 `1 R = R <> <>

List-Rel : {k : Kind} (T0 T1 : U k) (R : El T0 -> El T1 -> U Props)
  -> List (El T0) -> List (El T1) -> U Props
List-Rel T0 T1 R [] [] = `1
List-Rel T0 T1 R (x ,- xs) (y ,- ys) = R x y `/\ List-Rel T0 T1 R xs ys
List-Rel _ _ _ _ _ = `0 -- for once!


-- Propositional equality across the universes
-- Pious equality (true at different types)
--   (some cases are 'just true', left to catch-all, but commented out for
--    documentary evidence that that is what we meant)
{-# TERMINATING #-}
-- TODO: beat the termination checker by inlining
Eq : {k : Kind} (T0 : U k) -> El T0 -> (T1 : U k) -> El T1 -> U Props
-- forcing Agda to match on the types first to be lazier in the values;
-- otherwise EqDec chokes
Eq _ _ `0 _ = `1
Eq {Props} T0 t0 T1 t1 = `1 -- proofs are all equal, by fiat
Eq (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  Eq S0 s0 S1 s1 `/\ Eq (T0 s0) t0 (T1 s1) t1
-- Eq `1 <> `1 <> = `1
Eq (S0 `-> T0) f0 (S1 `-> T1) f1 =
  S0 `-> \ s0 -> S1 `-> \ s1 -> Eq S0 s0 S1 s1 `=> Eq (T0 s0) (f0 s0) (T1 s1) (f1 s1) 
Eq (S0 `#>> T0) f0 (S1 `#>> T1) f1 =
  ElF-Rel S0 S1 \ s0 s1 -> Eq (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)
Eq (`E xs) t0 (`E ys) t1 = Enum-Eq xs t0 ys t1
Eq (`List T0) ts0 (`List T1) ts1 = List-Rel T0 T1 (\ t0 t1 -> Eq T0 t0 T1 t1) ts0 ts1
-- in particular, strictness on (con s0 f0) must not stop the second Mu being found
Eq (`Mu I0 Sh0 Pos0 posix0 i0) (con s0 f0) (`Mu I1 Sh1 Pos1 posix1 i1) (con s1 f1) =
  Eq (Sh0 i0) s0 (Sh1 i1) s1
  `/\ ElF-Rel (Pos0 i0 s0) (Pos1 i1 s1) \ p0 p1 ->
        Eq (`Mu I0 Sh0 Pos0 posix0 (posix0 i0 s0 p0)) (ffapp (Pos0 i0 s0) f0 p0)
           (`Mu I1 Sh1 Pos1 posix1 (posix1 i1 s1 p1)) (ffapp (Pos1 i1 s1) f1 p1)
-- Eq (`Prf T0) t0 (`Prf T1) t1 
Eq _ _ _ _ = `1


EqDec : (T0 : U Data)(t0 : El T0)(T1 : U Data)(t1 : El T1) -> Decision UPROPS
EnumDec : (xs ys : List String)(D : <: _-in xs :> -> <: _-in ys :> -> Decision UPROPS) -> Decision UPROPS
TabDec : (S0 : UF)(S1 : UF) -> (ElF S0 -> ElF S1 -> Decision UPROPS) -> Decision UPROPS

EnumDec xs ys D .Naw = (Enum-Rel xs ys \ xi yj -> D xi yj . Aye) `=> `0
EnumDec xs ys D .Aye = Enum-Rel xs ys \ xi yj -> D xi yj . Aye
EnumDec [] [] D .decide = `1 , _
EnumDec [] (x ,- ys) D .decide = `1 , _
EnumDec (x ,- xs) [] D .decide = `1 , _
EnumDec (x ,- xs) (y ,- ys) D .decide with D (x , ze) (y , ze) .decide
... | `0 , r = `0 , \ (z , _) -> D (x , ze) (y , ze) .exclude r z
... | `1 , q with EnumDec xs ys (\ (_ , i) (_ , j) -> D (_ , su i) (_ , su j)) .decide
... | `0 , r = `0 , \ (_ , s) -> EnumDec xs ys (\ (_ , i) (_ , j) -> D (_ , su i) (_ , su j)) .exclude r s
... | `1 , r = `1 , q , r
EnumDec xs ys D .exclude naw aye = naw aye

TabDec S0 S1 D .Naw = ElF-Rel S0 S1 (\ s0 s1 -> D s0 s1 .Aye) `=> `0
TabDec S0 S1 D .Aye = ElF-Rel S0 S1 (\ s0 s1 -> D s0 s1 .Aye)
TabDec S0 S1 D .exclude naw aye = naw aye
TabDec (xs0 `$< T0) (xs1 `$< T1) D .decide =
 EnumDec xs0 xs1 (\ x0 x1 -> TabDec (T0 x0) (T1 x1) \ t0 t1 -> D (x0 , t0) (x1 , t1)) .decide
TabDec (xs `$< T) `1 D .decide = `1 , _
TabDec `1 (xs `$< T) D .decide = `1 , _
TabDec `1 `1 D .decide with D <> <> .decide   -- sheer kludgery
... | `0 , r = `0 , D <> <> .exclude r
... | `1 , r = `1 , r

EqDec T0 t0 T1 t1 .Naw = Eq T0 t0 T1 t1 `=> `0
EqDec T0 t0 T1 t1 .Aye = Eq T0 t0 T1 t1

-- signals on the diagonal
EqDec (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) .decide with EqDec S0 s0 S1 s1 .decide
... | `0 , r = `0 , fst - r
... | `1 , q with EqDec (T0 s0) t0 (T1 s1) t1 .decide
... | `0 , r = `0 , snd - r
... | `1 , r = `1 , q , r

EqDec `1 <> `1 <> .decide = `1 , _

EqDec (S0 `#>> T0) f0 (S1 `#>> T1) f1 .decide =
  (TabDec S0 S1 \ s0 s1 -> EqDec (T0 s0) (ffapp S0 f0 s0) (T1 s1) (ffapp S1 f1 s1)) .decide

EqDec (`E xs) xi (`E ys) yj .decide = Enum-EqDec xs xi ys yj .decide

EqDec (`List T0) t0s (`List T1) t1s .decide = listEq? t0s t1s where
  listEq? : (t0s : El (`List T0))(t1s : El (`List T1)) ->
    el UPROPS (EqDec (`List T0) t0s (`List T1) t1s .Naw) +
    el UPROPS (EqDec (`List T0) t0s (`List T1) t1s .Aye)
  listEq? [] [] = `1 , _
  listEq? [] (t1 ,- t1s) = `0 , id
  listEq? (t0 ,- t0s) [] = `0 , id
  listEq? (t0 ,- t0s) (t1 ,- t1s) with EqDec T0 t0 T1 t1 .decide | listEq? t0s t1s
  ... | `0 , p | b , q = `0 , \ (x , _) -> p x
  ... | `1 , p | `0 , q = `0 , \ (_ , x) -> q x
  ... | `1 , p | `1 , q = `1 , p , q

EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1) t1 .decide
  = muEq? i0 t0 i1 t1 where
  Mu0 : El Ix0 -> U Data
  Mu0 = `Mu Ix0 Sh0 Pos0 posix0
  Mu1 : El Ix1 -> U Data
  Mu1 = `Mu Ix1 Sh1 Pos1 posix1
  muEq? : (i0 : El Ix0)(t0 : El (Mu0 i0))(i1 : El Ix1)(t1 : El (Mu1 i1))
      -> let P =  EqDec (Mu0 i0) t0 (Mu1 i1) t1 .Aye
      in el UPROPS (P `=> `0)
       + el UPROPS P
  kEq? : (P0 : UF)(pi0 : ElF P0 -> El Ix0)
         (k0 : P0 #> \ p -> El (Mu0 (pi0 p)))
         (P1 : UF)(pi1 : ElF P1 -> El Ix1)
         (k1 : P1 #> \ p -> El (Mu1 (pi1 p)))
      -> let P = ElF-Rel P0 P1 \ p0 p1 ->
                  EqDec (Mu0 (pi0 p0)) (ffapp P0 k0 p0)
                        (Mu1 (pi1 p1)) (ffapp P1 k1 p1) .Aye
      in el UPROPS (P `=> `0)
       + el UPROPS P

  muEq? i0 (con s0 k0) i1 (con s1 k1) with EqDec (Sh0 i0) s0 (Sh1 i1) s1 .decide
  ... | `0 , q = `0 , fst - q
  ... | `1 , q with kEq? (Pos0 i0 s0) (posix0 i0 s0) k0 (Pos1 i1 s1) (posix1 i1 s1) k1
  ... | `0 , r = `0 , snd - r
  ... | `1 , r = `1 , q , r
  
  kEq? (xs `$< T) pi0 k0 `1 pi1 k1 = `1 , _
  kEq? `1 pi0 k0 (xs `$< T) pi1 k1 = `1 , _
  kEq? ([] `$< T0) pi0 k0 ([] `$< T1) pi1 k1 = `1 , _
  kEq? ([] `$< T0) pi0 k0 ((x ,- xs1) `$< T1) pi1 k1 = `1 , _
  kEq? ((x ,- xs0) `$< T0) pi0 k0 ([] `$< T1) pi1 k1 = `1 , _
  kEq? ((x0 ,- xs0) `$< T0) pi0 < t0 , k0 > ((x1 ,- xs1) `$< T1) pi1 < t1 , k1 >
    with kEq? (T0 (_ , ze)) (((_ , ze) ,_) - pi0) t0 (T1 (_ , ze)) (((_ , ze) ,_) - pi1) t1
  ... | `0 , q = `0 , fst - q
  ... | `1 , q with kEq? (xs0 `$< \ (_ , i) -> T0 (_ , su i)) (\ ((_ , i) , t) -> pi0 ((_ , su i) , t)) k0
                         (xs1 `$< \ (_ , i) -> T1 (_ , su i)) (\ ((_ , i) , t) -> pi1 ((_ , su i) , t)) k1
  ... | `0 , r = `0 , snd - r
  ... | `1 , r = `1 , q , r
  kEq? `1 i0 t0 `1 i1 t1 = muEq? (i0 <>) t0 (i1 <>) t1

{-
with EqDec (Sh0 (i0 <>)) s0 (Sh1 (i1 <>)) s1 .decide
  ... | `0 , q = `0 , fst - q
  ... | `1 , q with kEq? (Pos0 (i0 <>) s0) (posix0 (i0 <>) s0) k0 (Pos1 (i1 <>) s1) (posix1 (i1 <>) s1) k1
  ... | `0 , r = `0 , snd - r
  ... | `1 , r = `1 , q , r
-}


EqDec (`Prf _) _ (`Prf _) _ .decide = `1 , _

-- noises off
EqDec (_ `>< _) _ `1 _ .decide = `1 , _
EqDec (_ `>< _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`E _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`List _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `>< _) _ (`Prf _) _ .decide = `1 , _
EqDec `1 _ (_ `>< _) _ .decide = `1 , _
EqDec `1 _ (_ `#>> _) _ .decide = `1 , _
EqDec `1 _ (`E _) _ .decide = `1 , _
EqDec `1 _ (`List _) _ .decide = `1 , _
EqDec `1 _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec `1 _ (`Prf _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (_ `>< _) _ .decide = `1 , _
EqDec (_ `#>> _) _ `1 _ .decide = `1 , _
EqDec (_ `#>> _) _ (`E _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`List _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (_ `#>> _) _ (`Prf _) _ .decide = `1 , _
EqDec (`E _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`E _) _ `1 _ .decide = `1 , _
EqDec (`E _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`E _) _ (`List _) _ .decide = `1 , _
EqDec (`E _) _ (`Mu _ _ _ _ _₁) _ .decide = `1 , _
EqDec (`E _) _ (`Prf _) _ .decide = `1 , _
EqDec (`List _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`List _) _ `1 _ .decide = `1 , _
EqDec (`List _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`List _) _ (`E _) _ .decide = `1 , _
EqDec (`List _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _
EqDec (`List _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ `1 _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`E _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`List _) _ .decide = `1 , _
EqDec (`Mu _ _ _ _ _) _ (`Prf _) _ .decide = `1 , _
EqDec (`Prf _) _ (_ `>< _) _ .decide = `1 , _
EqDec (`Prf _) _ `1 _ .decide = `1 , _
EqDec (`Prf _) _ (_ `#>> _) _ .decide = `1 , _
EqDec (`Prf _) _ (`E _) _ .decide = `1 , _
EqDec (`Prf _) _ (`List _) _ .decide = `1 , _
EqDec (`Prf _) _ (`Mu _ _ _ _ _) _ .decide = `1 , _

EqDec T0 t0 T1 t1 .exclude naw aye = naw aye


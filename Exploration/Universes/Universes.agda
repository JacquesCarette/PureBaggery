module Universes where

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
  -- Closed under Sigma
  _`><_ : (S : UF) -> (T : ElF S -> UF) -> UF

  -- Zero and One with eta
  `0 `1 : UF

  -- enumerations with no eta
  `E : List String -> UF

ElF (S `>< T) = ElF S >< \ s -> ElF (T s)
ElF `0 = Zero
ElF `1 = One
ElF (`E l) =  <: _-in l :>

-- expand out a list of strings into a type-level tuple of positions into that list
-- TODO? could re-jig this to use the String interface instead of the positional one
Tuple : (xs : List String) (T : <: _-in xs :> -> Set) -> Set
Tuple [] T = One
Tuple (x ,- xs) T = T (_ , ze) * Tuple xs \ (_ , i) -> T (_ , su i)

mapTuple : (xs : List String) {T0 T1 : <: _-in xs :> -> Set} (f : [: T0 -:> T1 :] ) ->
  Tuple xs T0 -> Tuple xs T1
mapTuple [] f <> = <>
mapTuple (x ,- xs) f (t , ts) = f _ t , mapTuple xs (\ (_ , i) -> f (_ , su i)) ts

-- Some External kit for tabulated functions
_#>_ : (S : UF) -> (T : ElF S -> Set) -> Set
(R `>< S) #> T = R #> \ r -> S r #> \ s -> T (r , s) 
`0 #> T = One
`1 #> T = T <>
`E l #> T = Tuple l T

-- tabulation for enumeration
tab : (xs : List String) {T : <: _-in xs :> -> Set} -> [: T :] -> Tuple xs T
tab [] f = <>
tab (x ,- xs) f = (f (_ , ze)) , (tab xs (\ (_ , i) -> f (_ , su i)))

-- projection for inverting tab
proj : (xs : List String) {T : <: _-in xs :> -> Set} -> Tuple xs T -> [: T :]
proj (x ,- xs) (t , ts) (_ , ze) = t
proj (x ,- xs) (t , ts) (_ , su i) = proj xs ts (_ , i)

-- tabulation for finite functions
fflam : (S : UF) {T : ElF S -> Set} -> (f : [: T :]) -> (S #> T)
fflam (R `>< S) f = fflam R \ r -> fflam (S r) \ s -> f (r , s)
fflam `0 f = <>
fflam `1 f = f <>
fflam (`E l) f = tab l f

-- using such tabulated functions
ffapp : (S : UF) {T : ElF S -> Set} -> (S #> T) -> [: T :]
ffapp (S `>< T) f  (s , t) = ffapp (T s) (ffapp S f s) t
ffapp `0        <> ()
ffapp `1        t  <>      = t
ffapp (`E xs)   ts i       = proj xs ts i

-- Internal versions of pair, Tuple, tabulated functions,
-- tabulation, projection, lam and app
-- which were basically already there
_`*_ : UF -> UF -> UF
S `* T = S `>< (kon T)

`Tuple : (l : List String) (T : <: _-in l :> -> UF) -> UF
`Tuple [] T = `1
`Tuple (x ,- xs) T = T (_ , ze) `* `Tuple xs \ (_ , i) -> T (_ , su i)

_`#>_ : (S : UF) -> (T : ElF S -> UF) -> UF
(R `>< S) `#> T = R `#> \ r -> S r `#> \ s -> T (r , s)
`0 `#> T = `1
`1 `#> T = T <>
`E l `#> T = `Tuple l T

-- tabulation for enumeration
`tab : (xs : List String) {T : <: _-in xs :> -> UF} -> [: T - ElF :] -> ElF (`Tuple xs T)
`tab [] f = <>
`tab (x ,- xs) f = (f (_ , ze)) , (`tab xs (\ (_ , i) -> f (_ , su i)))

-- projection for inverting tab
`proj : (xs : List String) {T : <: _-in xs :> -> UF} -> ElF (`Tuple xs T) -> [: T - ElF :]
`proj (x ,- xs) (t , ts) (_ , ze) = t
`proj (x ,- xs) (t , ts) (_ , su i) = `proj xs ts (_ , i)

-- tabulation for finite functions
`fflam : (S : UF) {T : ElF S -> UF} -> (f : [: T - ElF :]) -> ElF (S `#> T)
`fflam (R `>< S) f = `fflam R \ r -> `fflam (S r) \ s -> f (r , s)
`fflam `0 f = <>
`fflam `1 f = f <>
`fflam (`E l) f = `tab l f

-- using such tabulated functions
`ffapp : (S : UF) {T : ElF S -> UF} -> ElF (S `#> T) -> [: T - ElF :]
`ffapp (S `>< T) f  (s , t) = `ffapp (T s) (`ffapp S f s) t
`ffapp `0        <> ()
`ffapp `1        t  <>      = t
`ffapp (`E xs)   ts i       = `proj xs ts i

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

----------------------------------------------------------------------------
-- Now we have to construct value equality

-- when we are two enumerations related pointwise?
Enum-Rel : (xs ys : List String) (R : <: _-in xs :> -> <: _-in ys :> -> U Props) -> U Props
Enum-Rel (x ,- xs) (y ,- ys) R = R (x , ze) (y , ze) `/\ Enum-Rel xs ys \ (_ , i) (_ , j) -> R (_ , su i) (_ , su j)
Enum-Rel _         _         _ = `1

Enum-Eq : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> U Props
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , ze) = `1
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , su j) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , ze) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , su j) = Enum-Eq xs (_ , i) ys (_ , j)

-- when are elements of two finite types "pointwise" related?
ElF-Rel : (S0 S1 : UF) -> (ElF S0 -> ElF S1 -> U Props) -> U Props
ElF-Rel (S0 `>< T0) (S1 `>< T1) R =
  ElF-Rel S0 S1 \ s0 s1 -> ElF-Rel (T0 s0) (T1 s1) \ t0 t1 -> R (s0 , t0) (s1 , t1)
-- ElF-Rel `0 `0 R = {!!}
ElF-Rel `1 `1 R = R <> <>
ElF-Rel (`E xs) (`E ys) R = Enum-Rel xs ys R
ElF-Rel _ _ _ = `1

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
-- TODO: beat the termination checker
Eq : {k : Kind} (T0 : U k) -> El T0 -> (T1 : U k) -> El T1 -> U Props
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
Eq (`Mu I0 Sh0 Pos0 posix0 i0) (con s0 f0) (`Mu I1 Sh1 Pos1 posix1 i1) (con s1 f1) =
  Eq (Sh0 i0) s0 (Sh1 i1) s1
  `/\ ElF-Rel (Pos0 i0 s0) (Pos1 i1 s1) \ p0 p1 ->
        Eq (`Mu I0 Sh0 Pos0 posix0 (posix0 i0 s0 p0)) (ffapp (Pos0 i0 s0) f0 p0)
           (`Mu I1 Sh1 Pos1 posix1 (posix1 i1 s1 p1)) (ffapp (Pos1 i1 s1) f1 p1)
-- Eq (`Prf T0) t0 (`Prf T1) t1 
Eq _ _ _ _ = `1

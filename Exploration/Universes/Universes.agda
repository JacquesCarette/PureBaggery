module Universes where

open import String

open import Basics
open import Thinnings

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

-- LATER: use these even more pervasively down below
-- mapping down an -in
zee : {x : String} {xs : List String} -> <: _-in (x ,- xs) :>
zee = _ , ze

-- could be golfed to _ >><< su
suu : {x : String} {xs : List String} -> <: _-in xs :> ->  <: _-in (x ,- xs) :>
suu (_ , i) = (_ , su i)

-- when we know a is in l, we can (fairly silently) get to know where something is
--  (which, magically, is going to be a, but we don't / can't promise that)
$ : (a : String) -> {l : List String} -> {_ : a -In l} -> <: _-in l :>
$ a {x ,- l} {p} with primStringEquality a x
... | `0 = suu ($ a {l} {p})
... | `1 = zee

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
Tuple (x ,- xs) T = T zee * Tuple xs (suu - T)

mapTuple : (xs : List String) {T0 T1 : <: _-in xs :> -> Set} (f : [: T0 -:> T1 :] ) ->
  Tuple xs T0 -> Tuple xs T1
mapTuple [] f <> = <>
mapTuple (x ,- xs) f (t , ts) = f _ t , mapTuple xs (suu - f) ts

-- Some External kit for tabulated functions
-- While this wrapping-unwrapping seems pointless, later on it helps us
-- point Agda to "look here" to see something that is indeed getting smaller.
data _#>_  (S : UF)(T : ElF S -> Set) : Set
_#>'_ : (S : UF) -> (T : ElF S -> Set) -> Set
data _#>_ S T where
  <_> : S #>' T -> S #> T
(R `>< S) #>' T = R #> \ r -> S r #> \ s -> T (r , s) 
`0 #>' T = One
`1 #>' T = T <>
`E l #>' T = Tuple l T

-- tabulation for enumeration
tab : (xs : List String) {T : <: _-in xs :> -> Set} -> [: T :] -> Tuple xs T
tab [] f = <>
tab (x ,- xs) f = f zee , tab xs (suu - f)

-- projection for inverting tab
proj : (xs : List String) {T : <: _-in xs :> -> Set} -> Tuple xs T -> [: T :]
proj (x ,- xs) (t , ts) (_ , ze) = t
proj (x ,- xs) (t , ts) (_ , su i) = proj xs ts (_ , i)

-- tabulation for finite functions
fflam : (S : UF) {T : ElF S -> Set} -> (f : [: T :]) -> (S #> T)
fflam (R `>< S) f = <( fflam R \ r -> fflam (S r) \ s -> f (r , s) )>
fflam `0 f = < <> >
fflam `1 f = < f <> >
fflam (`E l) f = < tab l f >

-- using such tabulated functions
ffapp : (S : UF) {T : ElF S -> Set} -> (S #> T) -> [: T :]
ffapp (S `>< T) < f >  (s , t) = ffapp (T s) (ffapp S f s) t
ffapp `0        < <> > ()
ffapp `1        < t >  <>      = t
ffapp (`E xs)   < ts > i       = proj xs ts i

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
F2D (S `>< T) =
  let S' , f = F2D S in
  (S' `>< \ s' -> fst (F2D (T (f s')))) , \ (s' , t') ->
  let T' , g = F2D (T (f s')) in f s' , g t'
F2D `0 = `0 , \ ()
F2D `1 = `1 , _
F2D (`E xs) = `E xs , id

Enum-Eq : (xs : List String) -> <: _-in xs :> -> (ys : List String) -> <: _-in ys :> -> U Props
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , ze) = `1
Enum-Eq (x ,- xs) (_ , ze) (y ,- ys) (_ , su j) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , ze) = `0
Enum-Eq (x ,- xs) (_ , su i) (y ,- ys) (_ , su j) = Enum-Eq xs (_ , i) ys (_ , j)

Enum-refl : (xs : List String)(xi : <: _-in xs :>) -> El (Enum-Eq xs xi xs xi)
Enum-refl (x ,- xs) (_ , ze) = <>
Enum-refl (x ,- xs) (_ , su i) = Enum-refl xs (_ , i)

-- UF value equality
EqF : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> U Props
EqF (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) =
  EqF S0 s0 S1 s1 `/\ EqF (T0 s0) t0 (T1 s1) t1
-- EqF `1 t0 `1 t1 = {!!}
EqF (`E xs) xi (`E ys) yj = Enum-Eq xs xi ys yj
EqF _ _ _ _ = `1


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

EqFDec : (T0 : UF)(t0 : ElF T0)(T1 : UF)(t1 : ElF T1) -> Decision UPROPS
EqFDec T0 t0 T1 t1 .Naw = EqF T0 t0 T1 t1 `=> `0  -- can we do better?
EqFDec T0 t0 T1 t1 .Aye = EqF T0 t0 T1 t1
EqFDec (S0 `>< T0) (s0 , t0) (S1 `>< T1) (s1 , t1) .decide with EqFDec S0 s0 S1 s1 .decide
... | `0 , r = `0 , fst - r
... | `1 , q with EqFDec (T0 s0) t0 (T1 s1) t1 .decide
... | `0 , r = `0 , snd - r
... | `1 , r = `1 , q , r
EqFDec (_ `>< _) _ `1 _ .decide = `1 , _
EqFDec (_ `>< _) _ (`E _) _ .decide = `1 , _
EqFDec `1 _ (_ `>< _) _ .decide = `1 , _
EqFDec `1 <> `1 <> .decide = `1 , _
EqFDec `1 _ (`E _) _ .decide = `1 , _
EqFDec (`E _) _ (_ `>< _) t1 .decide = `1 , _
EqFDec (`E _) _ `1 _ .decide = `1 , _
EqFDec (`E xs) xi (`E ys) yj .decide = Enum-EqDec xs xi ys yj .decide
-- would normally expect to say something more detailed and positional, but that would be long
EqFDec T0 t0 T1 t1 .exclude naw aye = naw aye

{-
-- transport is tricky
f2d : (S : UF) -> let S' , f = F2D S
   in (s : ElF S)
   -> El S' >< \ s' -> El (EqF S s S (f s'))
f2d (S `>< T) (s , t) =
  let s' , sq = f2d S s in let t' , tq = f2d (T s) t in
  (s' , {!!}) , {!!}
f2d `1 s = _
f2d (`E xs) xi = xi , Enum-refl xs xi
-}

-- when we are two enumerations related pointwise?
Enum-Rel : (xs ys : List String) (R : <: _-in xs :> -> <: _-in ys :> -> U Props) -> U Props
Enum-Rel (x ,- xs) (y ,- ys) R = R (x , ze) (y , ze) `/\ Enum-Rel xs ys \ (_ , i) (_ , j) -> R (_ , su i) (_ , su j)
Enum-Rel _         _         _ = `1

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


-- Should this be indexed over a position set and pack functions from positions *inside*?
data PoStack (Ix : U Extensional) : Set where
  poNil : El Ix -> PoStack Ix
  poCons : (S : UF)(T : ElF S -> PoStack Ix) -> PoStack Ix

-----------------------------------------------------------------------------------
-- The next gazillions of lines help us show that we have decidable equality for the universe
-- of Data.
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
TabDec (S0 `>< T0) (S1 `>< T1) D .decide =
  TabDec S0 S1 (\ s0 s1 -> TabDec (T0 s0) (T1 s1) \ t0 t1 -> D (s0 , t0) (s1 , t1))
  .decide
TabDec (S0 `>< T) `0 D .decide = `1 , _
TabDec (S0 `>< T) `1 D .decide = `1 , _
TabDec (S0 `>< T) (`E x) D .decide = `1 , _
TabDec `0 (S1 `>< T) D .decide = `1 , _
TabDec `0 `0 D .decide = `1 , _
TabDec `0 `1 D .decide = `1 , _
TabDec `0 (`E x) D .decide = `1 , _
TabDec `1 (S1 `>< T) D .decide = `1 , _
TabDec `1 `0 D .decide = `1 , _
TabDec `1 `1 D .decide with D <> <> .decide   -- sheer kludgery
... | `0 , r = `0 , D <> <> .exclude r
... | `1 , r = `1 , r
TabDec `1 (`E x) D .decide = `1 , _
TabDec (`E x) (S1 `>< T) D .decide = `1 , _
TabDec (`E x) `0 D .decide = `1 , _
TabDec (`E x) `1 D .decide = `1 , _
TabDec (`E xs) (`E ys) D .decide = EnumDec xs ys D .decide
TabDec S0 S1 D .exclude naw aye = naw aye

{-
TabDec : (S0 : UF)(T0 : ElF S0 -> U Data)(f0 : S0 #> (T0 - El))
         (S1 : UF)(T1 : ElF S1 -> U Data)(f1 : S1 #> (T1 - El))
      -> Decision
-- Naw and Aye are forced by the use site
TabDec S0 T0 f0 S1 T1 f1 .Naw = _
TabDec S0 T0 f0 S1 T1 f1 .Aye = _
TabDec (R0 `>< S0) T0 f0 (R1 `>< S1) T1 f1 .decide = {!!}
-- ... but it doesn't lift neatly through the currying-out of the `><
-}

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
  = poStkEq? (poNil i0) t0 (poNil i1) t1 where
  {- Seems like what we want, but we generalize it (below)
     and make more of it transparently (to Agda) first-order while
     at it.
  muEq? : (i0 : El Ix0) (t0 : El (`Mu Ix0 Sh0 Pos0 posix0 i0))
          (i1 : El Ix1) (t1 : El (`Mu Ix1 Sh1 Pos1 posix1 i1))
       ->
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Naw)
        +
        el UPROPS
        (EqDec (`Mu Ix0 Sh0 Pos0 posix0 i0) t0 (`Mu Ix1 Sh1 Pos1 posix1 i1)
         t1 .Aye)
  -}

  elPoS0 : PoStack Ix0 -> U Data
  elPoS0 (poNil i0) = `Mu Ix0 Sh0 Pos0 posix0 i0
  elPoS0 (poCons S T) = S `#>> \ s -> elPoS0 (T s)

  elPoS1 : PoStack Ix1 -> U Data
  elPoS1 (poNil i1) = `Mu Ix1 Sh1 Pos1 posix1 i1
  elPoS1 (poCons S T) = S `#>> \ s -> elPoS1 (T s)

  poStkEq? : (p0 : PoStack Ix0) (t0 : El (elPoS0 p0))(p1 : PoStack Ix1) (t1 : El (elPoS1 p1))
          ->  El (Eq (elPoS0 p0) t0 (elPoS1 p1) t1 `=> `0)
           +  El (Eq (elPoS0 p0) t0 (elPoS1 p1) t1)
  
  kEq? : (P0 : UF)(pstk0 : ElF P0 -> PoStack Ix0) -- can we hide this function inside PoStack?
         (k0 : P0 #> (pstk0 - elPoS0 - El))
         (P1 : UF)(pstk1 : ElF P1 -> PoStack Ix1)
         (k1 : P1 #> (pstk1 - elPoS1 - El))
    -> el UPROPS (ElF-Rel P0 P1 (\ p0 p1 -> EqDec
          (elPoS0 (pstk0 p0)) (ffapp P0 k0 p0)
          (elPoS1 (pstk1 p1)) (ffapp P1 k1 p1)
        .Aye) `=> `0)
     + el UPROPS (ElF-Rel P0 P1 \ p0 p1 -> EqDec
          (elPoS0 (pstk0 p0)) (ffapp P0 k0 p0)
          (elPoS1 (pstk1 p1)) (ffapp P1 k1 p1)
        .Aye)
  tupEq? : ∀ xs0 (pstk0 : ElF (`E xs0) → PoStack Ix0)
           (k0 : `E xs0 #>' (pstk0 - elPoS0 - El)) xs1
           (pstk1 : ElF (`E xs1) → PoStack Ix1)
           (k1 : `E xs1 #>' (pstk1 - elPoS1 - El)) →
         el UPROPS
         (ElF-Rel (`E xs0) (`E xs1)
          (λ p0 p1 →
             EqDec (elPoS0 (pstk0 p0)) (ffapp (`E xs0) < k0 > p0)
             (elPoS1 (pstk1 p1)) (ffapp (`E xs1) < k1 > p1) .Aye)
          `=> `0)
         +
         el UPROPS
         (ElF-Rel (`E xs0) (`E xs1)
          (λ p0 p1 →
             EqDec (elPoS0 (pstk0 p0)) (ffapp (`E xs0) < k0 > p0)
             (elPoS1 (pstk1 p1)) (ffapp (`E xs1) < k1 > p1) .Aye))

  poStkEq? (poNil _) _ (poCons _ _) _ = `1 , _
  poStkEq? (poCons _ _) _ (poNil _) _ = `1 , _
  
  poStkEq? (poCons S0 T0) k0 (poCons S1 T1) k1 =
    kEq? S0 T0 k0 S1 T1 k1

  poStkEq? (poNil i0) (con s0 k0) (poNil i1) (con s1 k1) with EqDec (Sh0 i0) s0 (Sh1 i1) s1 .decide
  ... | `0 , p = `0 , \ (x , _) -> p x
  ... | `1 , p
    with kEq? (Pos0 i0 s0) (posix0 i0 s0 - poNil) k0 (Pos1 i1 s1) (posix1 i1 s1 - poNil) k1
  ... | `0 , q = `0 , \ (_ , x) -> q x
  ... | `1 , q = `1 , p , q


  kEq? (S0 `>< T0) pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? (S0 `>< T0) pstk0 k0 `1 pstk1 k1 = `1 , _
  kEq? (S0 `>< T0) pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 `1 pstk1 k1 = `1 , _
  kEq? `0 pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? `1 pstk0 k0 (`E x) pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 (P1 `>< T) pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 `0 pstk1 k1 = `1 , _
  kEq? (`E x) pstk0 k0 `1 pstk1 k1 = `1 , _

  -- here is the same problem as with TabDec Mk I
  -- k0 has an S0 outer layer whose children are not Mus, but rather T0s of Mus
  kEq? (S0 `>< T0) pstk0 < k0 > (S1 `>< T1) pstk1 < k1 > = 
    kEq? S0 (\ s0 -> poCons (T0 s0) \ t0 -> pstk0 (s0 , t0)) k0
         S1 (\ s1 -> poCons (T1 s1) \ t1 -> pstk1 (s1 , t1)) k1
  
  kEq? `0 pstk0 k0 `0 pstk1 k1 = `1 , _
  
  kEq? `1 pstk0 < t0 > `1 pstk1 < t1 > = poStkEq? (pstk0 <>) t0 (pstk1 <>) t1
  
  kEq? (`E xs0) pstk0 < k0 > (`E xs1) pstk1 < k1 > = tupEq? xs0 pstk0 k0 xs1 pstk1 k1
  
  tupEq? [] pstk0 k0 [] pstk1 k1 = `1 , _
  tupEq? [] pstk0 k0 (x ,- xs1) pstk1 k1 = `1 , _
  tupEq? (x ,- xs0) pstk0 k0 [] pstk1 k1 = `1 , _
  tupEq? (x0 ,- xs0) pstk0 (t0 , k0) (x1 ,- xs1) pstk1 (t1 , k1)
    with poStkEq? (pstk0 (_ , ze)) t0 (pstk1 (_ , ze)) t1
       | tupEq? xs0 (\ (_ , i) -> pstk0 (_ , su i)) k0 xs1 (\ (_ , i) -> pstk1 (_ , su i)) k1
  ... | `0 , q | c , r = `0 , fst - q
  ... | `1 , q | `0 , r = `0 , snd - r
  ... | `1 , q | `1 , r = `1 , q , r
  
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

-- End gazillion
-------------------------------------------------------------------------------

-- Baby steps towards differential structure

-- Enumerating (elements of) UF
enum-Enum-work : (xs ys : List String) -> (<: _-in xs :> -> <: _-in ys :>) -> List <: _-in ys :>
enum-Enum-work []        ys shuffle = []
enum-Enum-work (x ,- xs) ys shuffle = shuffle zee ,- enum-Enum-work xs ys (suu - shuffle)

enum-Enum-work-works : (xs ys : List String)
  -> (f : <: _-in xs :> -> <: _-in ys :>)
  -> {x : String}(i : x -in xs)
  -> (f (x , i) ,- []) <= enum-Enum-work xs ys f
enum-Enum-work-works xs ys f ze = f zee ,- no
enum-Enum-work-works xs ys f (su i) = f zee ^- enum-Enum-work-works _ ys (suu - f) i

enum-Enum : (xs : List String) -> List <: _-in xs :>
enum-Enum xs = enum-Enum-work xs xs id

enum-Enum-enums : (xs : List String){x : String}(i : x -in xs)
  -> ((x , i) ,- []) <= enum-Enum xs
enum-Enum-enums xs i = enum-Enum-work-works xs xs id i

enum-UF : (T : UF) -> List (ElF T)
enum-UF (S `>< T) = enum-UF S >>L= \s -> enum-UF (T s) >>L= \ t -> (s , t) ,- []
enum-UF `0 = []
enum-UF `1 = <> ,- []
enum-UF (`E x) = enum-Enum x

-- Later: elements of (enum-UF) are distinct, findable and ordered
--  and every selection of 2 elements has those elements in order.

findit : (T : UF) (t : ElF T) -> (t ,- []) <= enum-UF T
findit (S `>< T) (s , t) with enum-UF S | findit S s
... | e | i =
  thin-loc-bind i
    (\ { s (.s ,- []) -> (s , t) ,- [] })
    (\ s _ -> enum-UF (T s) >>!= (\ t _ -> (s , t) ,- []))
    \ { s {.s ,- []} {j} v -> let i' = findit (T s) t in
      thin-loc-bind i'
        (\ { t (.t ,- []) -> (s , t) ,- [] })
        (\ t' _ -> (s , t') ,- [])
        \ { t {.t ,- []} {j} v -> io }}
findit `1 <> = <> ,- []
findit (`E x) (_ , i) = enum-Enum-enums x i

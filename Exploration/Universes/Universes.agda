module Universes where

open import String

open import Basics

data Kind : Set where
  Finite Data Extensional Props : Kind

-- only two of the universes can have extensional functions
canHazPi : Kind -> Set
canHazPi Extensional = One
canHazPi Props       = One
canHazPi _           = Zero

-- we rule out tabulated functions in Finite
-- (which has implications for containers)
canHazTab : Kind -> Set
canHazTab Finite = Zero
canHazTab _      = One

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

-- expand out a list of strings into a type-level tuple of positions into that list
-- TODO? could re-jig this to use the String interface instead of the positional one
Tuple : (l : List String) (T : <: _-in l :> -> Set) -> Set
Tuple [] T = One
Tuple (x ,- l) T = T (_ , ze) * Tuple l \ (_ , i) -> T (_ , su i)

data U (k : Kind) : Set
El : forall {k : Kind} -> U k -> Set
data Mu (Ix : Set) (Sh : Ix -> Set) (Pos : (i : Ix) -> Sh i -> U Finite)
  (posix : (i : Ix) (s : Sh i) (p : El (Pos i s)) -> Ix) (i : Ix) : Set
_#>_ : (S : U Finite) -> (T : El S -> Set) -> Set

-- Convention: capital letters for big things
data U k where
  -- All universes are closed under Sigma
  _`><_ : (S : U k) -> (T : El S -> U k) -> U k

  -- only some universes have Zero and One
  `0 `1 : U k

  -- Extensional functions
  _`->_ : {_ : canHazPi k} -> (S : U Extensional) -> (T : El S -> U k) -> U k

  -- Tabulated functions
  _`#>_ : {_ : canHazTab k} -> (S : U Finite) -> (T : El S -> U k) -> U k

  -- enumerations
  `E : {_ : canHazEnum k} -> List String -> U k

  -- lists
  `List : {_ : canHazList k} -> U k -> U k

  -- fixed points (of indexed containers). For now, Finite positions.
  `Mu : {_ : canHazTab k} -> (Ix : U Extensional) -> (Sh : El Ix -> U k) ->
    (Pos : (i : El Ix) (s : El (Sh i)) -> U Finite) ->
    (posix : (i : El Ix) (s : El (Sh i)) (p : El (Pos i s)) -> El Ix) ->
    El Ix -> U k
    
-- it is positive, but convincing Agda of this is likely very painful if even possible
{-# NO_POSITIVITY_CHECK #-}
data Mu Ix Sh Pos posix i where
  con : (s : Sh i) -> (Pos i s #> \ p -> Mu Ix Sh Pos posix (posix i s p)) -> Mu Ix Sh Pos posix i
  
El (S `>< T) = El S >< \ s -> El (T s)
El `0 = Zero
El `1 = One
El (S `-> T) = (s : El S) -> El (T s)
El (S `#> T) = S #> \ s -> El (T s)
El (`E l) = <: _-in l :>
El (`List S) = List (El S)
El (`Mu Ix Sh Pos posix i) = Mu (El Ix) (\ i -> El (Sh i)) Pos posix i

-- Interpretation of tabulated functions
(R `>< S) #> T = R #> \ r -> S r #> \ s -> T (r , s) 
`0 #> T = One
`1 #> T = T <>
`E l #> T = Tuple l T

-- Experiment, i.e. does $ compute properly. To be deleted later.
Foo : U Finite
foo : El Foo

Foo = `E ("fred" ,- "jim" ,- "sheila" ,- [])
foo = $ "sheila"  -- this normalizes properly


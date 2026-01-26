module TabulatedFunctions where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite

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

-- Internal versions of Tuple, tabulated functions,
-- tabulation, projection, lam and app
-- which were basically already there
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

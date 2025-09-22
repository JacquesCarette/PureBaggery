module Universes where

open import String

open import Basics
open import Thinnings
open import Membership
open import Finite
open import TabulatedFunctions

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


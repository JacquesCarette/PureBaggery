module Finite where

open import String

open import Basics
open import Thinnings
open import Membership

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


-- Internal versions of pair
_`*_ : UF -> UF -> UF
S `* T = S `>< (kon T)

-- a handy helper for tagged types
`ctors : List (String * UF) -> UF
`ctors cTs = `E (list fst cTs) `>< fetch cTs where
  -- move this out ?
  fetch : (cTs : List (String * UF))
          (i : <: _-in list fst cTs :>)
       -> UF
  fetch ((c , T) ,- _) (_ , ze) = T
  fetch (_ ,- cTs) (_ , su i) = fetch cTs (_ , i)

-- ...whence, binary sums...
_`+F_ : UF -> UF -> UF
D `+F E = `ctors (("inl" , D) ,- ("inr" , E) ,- [])

pattern inl d = ("inl" , ze) , d
pattern inr e = ("inr" , su ze) , e

-- ...whence binary digits
`2 : UF
`2 = `1 `+F `1

pattern ff = inl <>
pattern tt = inr <>



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

-- for UF, we need the embedding defined mutually
-- with the removal, to make Sigma work properly
_-sans_ : (T : UF)(t : ElF T) -> UF
sans-embed : (T : UF)(t : ElF T) -> ElF (T -sans t) -> ElF T
(S `>< T) -sans (s , t) = `ctors (
  ("diffLeft"  , ((S -sans s) `>< \ s' -> T (sans-embed S s s'))) ,-
  ("diffRight" , (T s -sans t)) ,- [])
`1 -sans <> = `0
`E xs -sans i = `E (xs -bar i)
sans-embed (S `>< T) (s , t) ((_ , ze) , s' , t') =
  sans-embed S s s' , t'
sans-embed (S `>< T) (s , t) ((_ , su ze) , t') =
  s , sans-embed (T s) t t'
sans-embed (`E xs) i (_ , j) = _ , thin-in j (bar-subset xs i)

{-
-- aha we may struggle to push this through for Sigma
me-or-not : (T : UF)(me : ElF T)(x : ElF T)
  -> ElF (`ctors (("self" , `1) ,- ("other" , T -sans me) ,- []))
me-or-not (S `>< T) (sme , tme) (sx , tx)
  with me-or-not S sme sx
... | (."self" , ze) , <> = {!!}
  -- want to call me-or-not (T sme) tme tx
  -- but need sme = sx
... | (."other" , su ze) , s'
  = $ "other" , $ "diffLeft" , s' , {!!} -- want tx but need coherence
me-or-not `1 <> <> = $ "self" , <>
me-or-not (`E xs) i j = {!!}
-}


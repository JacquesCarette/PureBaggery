module UniversalAlgebra where

open import Basics

-- the usual: signatures, terms, equations, algebras, etc
-- we're guessing we'll need multi-sorted sufficiently soon to go right ahead
-- with that.

-- building up to being able to induce container morphisms

-- Signature
--   use 't' as short for 't'arget
module Signature (Sort : Set) where

  -- pow-ish in output sorts, fam-ish in input sorts
  record Sig : Set₁ where
    field
      Opr : Sort -> Set
      arity : (t : Sort) -> Opr t -> List Sort

  module _ (sig : Sig) where
    open Sig sig

    module _ (R : Sort -> Set) where
      -- helper because we need Agda to see through the recursion
      SortArity : List Sort -> Set -> Set
      SortArity [] T        = T
      SortArity (s ,- ss) T = R s -> SortArity ss T
      
      OprType : (t : Sort) -> Opr t -> Set
      OprType t o = SortArity (arity t o) (R t)

      -- Operations (i.e. Model) for raw Signature
      Operations : Set
      Operations = (t : Sort) -> (o : Opr t) -> OprType t o

      -- can't use 'cataList' because Agda's positivity checker will be
      -- unhappy below
      SortTuple : List Sort -> Set
      SortTuple [] = One
      SortTuple (t ,- ts) = R t * SortTuple ts

      OprSource : (t : Sort) -> Opr t -> Set
      OprSource t o = SortTuple (arity t o)

      sortCurry : (ss : List Sort) -> (T : Set) -> (SortTuple ss -> T) -> SortArity ss T
      sortCurry []        T f = f <>
      sortCurry (s ,- ss) T f = \ r -> sortCurry ss T ((r ,_) - f)

    module _ (V : Sort -> Set) where
      -- Free such thing over a set V of variables and a Sort
      data FreeOprModel (t : Sort) : Set where
        opr : (o : Opr t) -> OprSource FreeOprModel t o -> FreeOprModel t
        var : (v : V t)                                 -> FreeOprModel t

      freeOper : Operations FreeOprModel
      freeOper t o = sortCurry FreeOprModel (arity t o) (FreeOprModel t) (opr o)

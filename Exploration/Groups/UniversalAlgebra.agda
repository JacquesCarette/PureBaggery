module UniversalAlgebra where

open import Basics

-- the usual: signatures, terms, equations, algebras, etc
-- we're guessing we'll need multi-sorted sufficiently soon to go right ahead
-- with that.

-- building up to being able to induce container morphisms

-- Signature
--   use 't' as short for 't'arget
module Signature (Sort : Set) where

  module _ (R : Sort -> Set) where

    -- can't use 'cataList' because Agda's positivity checker will be
    -- unhappy below
    SortTuple : List Sort -> Set
    SortTuple []        = One
    SortTuple (t ,- ts) = R t * SortTuple ts

    SortDepArity : (ss : List Sort) -> (SortTuple ss -> Set) -> Set
    SortDepArity [] f = f <>
    SortDepArity (x ,- ss) f = (r : R x) -> SortDepArity ss \ rs -> f (r , rs)
    
    -- helper because we need Agda to see through the recursion
    SortArity : List Sort -> Set -> Set
    SortArity ss T = SortDepArity ss (kon T)

    project : {ss : List Sort} -> SortTuple ss -> [: (_-in ss) -:> R :]
    project (r , _) ze = r
    project (_ , ts) (su vr) = project ts vr

    tabulate : {ss : List Sort} -> [: (_-in ss) -:> R :] -> SortTuple ss
    tabulate {[]} f = <>
    tabulate {x ,- ss} f = f ze , tabulate (su - f)

    sortDepCurry : (ss : List Sort) -> (T : SortTuple ss -> Set) ->
      ((rs : SortTuple ss) -> T rs) -> SortDepArity ss T
    sortDepCurry []        T f = f <>
    sortDepCurry (s ,- ss) T f = \ r -> sortDepCurry ss ((r ,_) - T) ((r ,_) - f)
    
    sortCurry : (ss : List Sort) -> (T : Set) -> (SortTuple ss -> T) -> SortArity ss T
    sortCurry ss T f = sortDepCurry ss (kon T) f

    sortApply : (ss : List Sort) -> (T : Set) -> SortArity ss T -> (SortTuple ss -> T)
    sortApply [] T t <> = t
    sortApply (s ,- ss) T f (t , ts) = sortApply ss T (f t) ts

  mapSortTuple : {S T : Sort -> Set}
              -> [: S -:> T :]
              -> [: SortTuple S -:> SortTuple T :]
  mapSortTuple f {[]} <> = <>
  mapSortTuple f {i ,- is} (s , ss) = f s , mapSortTuple f ss

  -- pow-ish in output sorts, fam-ish in input sorts
  record Sig : Set₁ where
    field
      Opr : Sort -> Set
      arity : (t : Sort) -> Opr t -> List Sort

  module _ (sig : Sig) where
    open Sig sig

    module _ (R : Sort -> Set) where
      
      OprType : (t : Sort) -> Opr t -> Set
      OprType t o = SortArity R (arity t o) (R t)

      -- Operations (i.e. Model) for raw Signature
      Operations : Set
      Operations = {i : Sort} -> (o : Opr i) -> OprType i o

      OprSource : (t : Sort) -> Opr t -> Set
      OprSource t o = SortTuple R (arity t o)


    module _ (V : List Sort) where
      -- Free such thing over a set V of variables and a Sort
      data FreeOprModel (t : Sort) : Set where
        opr : (o : Opr t) -> OprSource FreeOprModel t o -> FreeOprModel t
        var : (v : t -in V)                             -> FreeOprModel t

      eval : {R : Sort -> Set} -> Operations R
        -> SortTuple  R V
        -> [: FreeOprModel -:> R :]
      evals : {R : Sort -> Set} -> Operations R
        -> SortTuple R V
        -> [: SortTuple FreeOprModel -:> SortTuple R :]
      eval ops ga (opr o ts) = sortApply _ (arity _ o) _ (ops o) (evals ops ga ts)
      eval ops ga (var v) = project _ ga v
      evals ops ga {[]} <> = <>
      evals ops ga {i ,- is} (t , ts) = eval ops ga t , evals ops ga ts

    freeSubst : {V W : List Sort}
             -> SortTuple (FreeOprModel W) V
             -> [: FreeOprModel V -:> FreeOprModel W :]
    freeSubsts : {V W : List Sort}
             -> SortTuple (FreeOprModel W) V
             -> [: SortTuple (FreeOprModel V) -:> SortTuple (FreeOprModel W) :]
    freeSubst sg {i} (opr o ts) = opr o (freeSubsts sg ts)
    freeSubst sg (var v) = project _ sg v
    freeSubsts sg {[]} <> = <>
    freeSubsts sg {i ,- is} (t , ts) = freeSubst sg t , freeSubsts sg ts

  record Theory (sig : Sig) : Set1 where
    field
      EqnSig : Sig
    open Sig EqnSig
    field
      leftModel  : {i : Sort} -> (o : Opr i)
        -> OprType EqnSig (FreeOprModel sig (arity i o)) i o
      rightModel : {i : Sort} -> (o : Opr i)
        -> OprType EqnSig (FreeOprModel sig (arity i o)) i o

  module FreeOper (sig : Sig){V : List Sort} where
    open Sig sig  
    _! : Operations sig (FreeOprModel sig V)
    _! {i} o = sortCurry (FreeOprModel sig V) (arity i o) (FreeOprModel sig V i) (opr o)


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
  
    -- helper because we need Agda to see through the recursion
    SortArity : List Sort -> Set -> Set
    SortArity [] T        = T
    SortArity (s ,- ss) T = R s -> SortArity ss T

    -- can't use 'cataList' because Agda's positivity checker will be
    -- unhappy below
    SortTuple : List Sort -> Set
    SortTuple []        = One
    SortTuple (t ,- ts) = R t * SortTuple ts

    sortCurry : (ss : List Sort) -> (T : Set) -> (SortTuple ss -> T) -> SortArity ss T
    sortCurry []        T f = f <>
    sortCurry (s ,- ss) T f = \ r -> sortCurry ss T ((r ,_) - f)

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


    module _ (V : Sort -> Set) where
      -- Free such thing over a set V of variables and a Sort
      data FreeOprModel (t : Sort) : Set where
        opr : (o : Opr t) -> OprSource FreeOprModel t o -> FreeOprModel t
        var : (v : V t)                                 -> FreeOprModel t

      eval : {R : Sort -> Set} -> Operations R
        -> [: V -:> R :]
        -> [: FreeOprModel -:> R :]
      evals : {R : Sort -> Set} -> Operations R
        -> [: V -:> R :]
        -> [: SortTuple FreeOprModel -:> SortTuple R :]
      eval ops ga (opr o ts) = sortApply _ (arity _ o) _ (ops o) (evals ops ga ts)
      eval ops ga (var v) = ga v
      evals ops ga {[]} <> = <>
      evals ops ga {i ,- is} (t , ts) = eval ops ga t , evals ops ga ts

    freeSubst : {V W : Sort -> Set}
             -> [:              V -:> FreeOprModel W :]
             -> [: FreeOprModel V -:> FreeOprModel W :]
    freeSubsts : {V W : Sort -> Set}
             -> [:              V -:> FreeOprModel W :]
             -> [: SortTuple (FreeOprModel V) -:> SortTuple (FreeOprModel W) :]
    freeSubst sg {i} (opr o ts) = opr o (freeSubsts sg ts)
    freeSubst sg (var v) = sg v
    freeSubsts sg {[]} <> = <>
    freeSubsts sg {i ,- is} (t , ts) = freeSubst sg t , freeSubsts sg ts

    record Equation (s : Sort) : Set1 where
      field
        Vars : Sort -> Set
        lhs rhs : FreeOprModel Vars s

    -- HERE!
    {- make Vars give a List Sort, not a Set, so that lhs and rhs can be
       derivable operations;
       consider something less flat than List Sort
       indeed, build equations as a signature of derived operations with
         left and right models in FreeOprModel for the signature the
         equations are about
    -}

    record Theory : Set1 where
      field
        Eqns : Sort -> Set
        eqn : (s : Sort) -> Eqns s -> Equation s

      PreModel : {R : Sort -> Set}(Q : (s : Sort) -> R s -> R s -> Set)
           -> Operations R -> Set
      PreModel {R} Q ops = (s : Sort)(q : Eqns s) ->
        let open Equation (eqn s q) in
        (ga : [: Vars -:> R :]) -> Q s (eval Vars ops ga lhs) (eval Vars ops ga rhs)

  module FreeOper (sig : Sig){V : Sort -> Set} where
    open Sig sig  
    _! : Operations sig (FreeOprModel sig V)
    _! {i} o = sortCurry (FreeOprModel sig V) (arity i o) (FreeOprModel sig V i) (opr o)


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

    SortDepArity : (ss : List Sort) -> (All R ss -> Set) -> Set
    SortDepArity [] f = f <>
    SortDepArity (x ,- ss) f = (r : R x) -> SortDepArity ss \ rs -> f (r , rs)
    
    -- helper because we need Agda to see through the recursion
    SortArity : List Sort -> Set -> Set
    SortArity ss T = SortDepArity ss (kon T)

    sortDepCurry : (ss : List Sort) -> (T : All R ss -> Set) ->
      ((rs : All R ss) -> T rs) -> SortDepArity ss T
    sortDepCurry []        T f = f <>
    sortDepCurry (s ,- ss) T f = \ r -> sortDepCurry ss ((r ,_) - T) ((r ,_) - f)
    
    sortCurry : (ss : List Sort) -> (T : Set) -> (All R ss -> T) -> SortArity ss T
    sortCurry ss T f = sortDepCurry ss (kon T) f

    sortApply : (ss : List Sort) -> (T : Set) -> SortArity ss T -> (All R ss -> T)
    sortApply [] T t <> = t
    sortApply (s ,- ss) T f (t , ts) = sortApply ss T (f t) ts

  Sig : Set
  Sig = Sort  -- for each output sort
     -> List  -- we list the operations without naming them, but rather
          (List Sort)  -- giving their arities

  -- signature extension, i.e. big extends wee
  _<Sig=_ : Sig -> Sig -> Set
  wee <Sig= big = (t : Sort) -> wee t <= big t

  ExtensionOf : Sig -> Set
  ExtensionOf wee = (t : Sort) -> <: wee t <=_ :> 

  -- projecting out of extensions
  extBig : {wee : Sig} -> ExtensionOf wee -> Sig
  extBig = _- fst

  extIsBigger : {wee : Sig} -> (ext : ExtensionOf wee) -> wee <Sig= extBig ext
  extIsBigger = _- snd
  
  module _ (sig : Sig) where

    [_]-_>>_ : (Sort -> Set) -> List Sort -> Sort -> Set
    [ R ]- ss >> t = SortArity R ss (R t)

    -- Operations (i.e. Model) for raw Signature
    Operations : (Sort -> Set) -> Set
    Operations R = (t : Sort) -> All ([ R ]-_>> t) (sig t)

    _-op_ : forall {R} -> Operations R -> forall {ss t} -> ss -in sig t -> [ R ]- ss >> t
    ops -op o = project (ops _) o

    module _ (V : List Sort) where
      -- Free such thing over a set V of variables and a Sort
      data FreeOprModel (t : Sort) : Set where
        opr : forall {ss} -> ss -in sig t -> All FreeOprModel ss -> FreeOprModel t
        var : (v : t -in V)                                      -> FreeOprModel t

      eval : {R : Sort -> Set} -> Operations R
        -> All  R V
        -> [: FreeOprModel -:> R :]
      evals : {R : Sort -> Set} -> Operations R
        -> All R V
        -> [: All FreeOprModel -:> All R :]
      eval ops ga (opr {ss} o ms) = sortApply _ ss _ (ops -op o) (evals ops ga ms)
      eval ops ga (var v) = project ga v
      evals ops ga {[]} <> = <>
      evals ops ga {i ,- is} (t , ts) = eval ops ga t , evals ops ga ts

    freeSubst : {V W : List Sort}
             -> All (FreeOprModel W) V
             -> [: FreeOprModel V -:> FreeOprModel W :]
    freeSubsts : {V W : List Sort}
             -> All (FreeOprModel W) V
             -> [: All (FreeOprModel V) -:> All (FreeOprModel W) :]
    freeSubst sg {i} (opr o ts) = opr o (freeSubsts sg ts)
    freeSubst sg (var v) = project sg v
    freeSubsts sg {[]} <> = <>
    freeSubsts sg {i ,- is} (t , ts) = freeSubst sg t , freeSubsts sg ts

  -- #$%#$ termination checker is too dumb, need to unwind mapAll
  embed : {wee big : Sig} {V : List Sort} -> (ext : wee <Sig= big) ->
    [: FreeOprModel wee V -:> FreeOprModel big V :]
  embeds : {wee big : Sig} {V : List Sort} -> (ext : wee <Sig= big) ->
    [: All (FreeOprModel wee V) -:> All (FreeOprModel big V) :]
    
  -- embed ext (opr c ts) = opr (c -< ext _) (mapAll (embed ext) ts)
  embed ext (opr c ts) = opr (c -< ext _) (embeds ext ts)
  embed ext (var v)    = var v

  embeds ext {[]}      <>       = <>
  embeds ext {s ,- ss} (t , ts) = embed ext t , embeds ext ts
  
  module TheoryKit (sig : Sig) where
    -- additional kit: take number (in context) and return 'opr' constructor
    infix 5 _!_
    _!_ : {V : List Sort} {t : Sort} -> (i : Nat) ->
       {ir : InRange i (sig t)} ->
       All (FreeOprModel sig V) (findInRange i (sig t) ir) ->
       FreeOprModel sig V t
    i ! x = opr (sing i) x

    -- sigh, can't call it 'abstract'
    abstr : {V : List Sort} {t : Sort} ->
       let mod = FreeOprModel sig V t in
       (All (FreeOprModel sig V) V -> mod * mod) ->
       mod * mod
    abstr f = f (mapAll var coords)

  record Theory (sig : Sig) : Set1 where
    field
      EqnSig : Sig

      equationStatements : (t : Sort) ->
        All
        (\ ga -> let Term = FreeOprModel sig ga t in Term * Term)
        (EqnSig t)

  -- HEREish too
  -- Need to talk about how to do Theory Extension based on a Signature
  -- extension. We'll also want to talk about the case where the new
  -- thing is derivable. And the contravariant thing on models too.
  
-- TODO: theory inclusion, which was the whole point of switching to lists and thinnings

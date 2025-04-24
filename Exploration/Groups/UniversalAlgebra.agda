module UniversalAlgebra where

open import Basics
open import Thinnings

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
    

    sortDepCurry : (ss : List Sort) -> (T : All R ss -> Set)
      -> [: T :] -> SortDepArity ss T
    sortDepCurry []        T f = f <>
    sortDepCurry (s ,- ss) T f = \ r -> sortDepCurry ss ((r ,_) - T) ((r ,_) - f)
    
    sortCurry : (ss : List Sort) -> (T : Set) -> (All R ss -> T) -> SortArity ss T
    sortCurry ss T f = sortDepCurry ss (kon T) f

    sortApply : (ss : List Sort) -> (T : Set) -> SortArity ss T -> (All R ss -> T)
    sortApply [] T t <> = t
    sortApply (s ,- ss) T f (t , ts) = sortApply ss T (f t) ts

  module _ {R : Sort -> Set} where
    unc : forall {ss : List Sort}{T : All R ss -> Set}
      -> SortDepArity R ss T -> [: T :]
    unc {[]} t <> = t
    unc {s ,- ss} f (r , rs) = unc {ss} (f r) rs

  Sig : Set
  Sig = Sort  -- for each output sort
     -> List  -- we list the operations without naming them, but rather
          (List Sort)  -- giving their arities

  -- signature extension, i.e. big extends wee
  _<Sig=_ : Sig -> Sig -> Set
  wee <Sig= big = (t : Sort) -> wee t <= big t

  SigExtension : Sig -> Set
  SigExtension wee = (t : Sort) -> <: wee t <=_ :> 

  -- projecting out of extensions
  extBig : {wee : Sig} -> SigExtension wee -> Sig
  extBig = _- fst

  extIsBigger : {wee : Sig} -> (ext : SigExtension wee) -> wee <Sig= extBig ext
  extIsBigger = _- snd

  extComp : {wee : Sig} -> (ext : SigExtension wee) -> (s : Sort)
    -> <: _<= _ :> >< \ ( _ , ph) -> snd (ext s) /#\ ph
  extComp ext s = snd (ext s) -not
  
  extCompSig : {wee : Sig} -> SigExtension wee -> Sig
  extCompSig ext s = fst (fst (extComp ext s))

  extCompSmall : {wee : Sig} -> (ext : SigExtension wee) -> extCompSig ext <Sig= extBig ext
  extCompSmall ext s = snd (fst (extComp ext s))
  
  extPart : {wee : Sig} -> (ext : SigExtension wee) -> (s : Sort) -> extIsBigger ext s /#\ extCompSmall ext s
  extPart ext s = snd (extComp ext s)
  
  module _ (sig : Sig) where

    module _ (V : List Sort) where
      -- Free such thing over a set V of variables and a Sort
      data FreeOprModel (t : Sort) : Set where
        opr : forall {ss} -> ss -in sig t -> All FreeOprModel ss -> FreeOprModel t
        var : (v : t -in V)                                      -> FreeOprModel t
        
    freeSubst : {V W : List Sort}
             -> All (FreeOprModel W) V
             -> [! FreeOprModel V -:> FreeOprModel W !]
    freeSubsts : {V W : List Sort}
             -> All (FreeOprModel W) V
             -> [! All (FreeOprModel V) -:> All (FreeOprModel W) !]
    freeSubst sg {i} (opr o ts) = opr o (freeSubsts sg ts)
    freeSubst sg (var v) = project sg v
    freeSubsts sg {[]} <> = <>
    freeSubsts sg {i ,- is} (t , ts) = freeSubst sg t , freeSubsts sg ts

  -- #$%#$ termination checker is too dumb, need to unwind mapAll
  embed : {wee big : Sig} {V : List Sort} -> (ext : wee <Sig= big) ->
    [! FreeOprModel wee V -:> FreeOprModel big V !]
  embeds : {wee big : Sig} {V : List Sort} -> (ext : wee <Sig= big) ->
    [! All (FreeOprModel wee V) -:> All (FreeOprModel big V) !]
    
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

  Eqns : (sig : Sig)(ES : List (List Sort)) -> Sort -> Set
  Eqns sig ES t =
    All
    (\ ga -> let Term = FreeOprModel sig ga t in Term * Term)
    ES

  record Theory (sig : Sig) : Set1 where
    field
      EqnSig : Sig

      eqns : forall t -> Eqns sig (EqnSig t) t

  record TheoryExtension {sig : Sig}(thy : Theory sig)(ext : SigExtension sig) : Set where
    open Theory
    field
      EqnSigExt : SigExtension (thy .EqnSig)
      eqnsExt   : forall t -> Eqns (extBig ext) ((extIsBigger EqnSigExt t -not) .fst .fst) t

    -- ``flatten'' the extension of thy into a Theory
    extTheory : Theory (extBig ext)
    extTheory .EqnSig = extBig EqnSigExt
    extTheory .eqns t =
      mapAll (embed (extIsBigger ext) >><< embed (extIsBigger ext)) (thy .eqns t)
      /< (extIsBigger EqnSigExt t -not) .snd >\
      eqnsExt t

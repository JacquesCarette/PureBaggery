
{-# OPTIONS --allow-unsolved-metas #-}
module Representables where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Algebras
open import ProductsForAlgebras
open import Actions as ACT -- to deal with a name conflict
open import Iso
open import GroupsWeLike
open import ActionsWeLike

-- Representable Container description with a group action that wiggles the positions
record Representable : Set where
  field
    {Wiggles} : U
    Positions : U
    Grp  : Group Wiggles
    Act : ACTION.Action Grp Positions

-- Extension of a representable
module REPRESENTABLE (R : Representable) where
  open Representable R renaming (Wiggles to W; Grp to G; Positions to Pos; Act to A)

  open Algebras.Group G
  open ACTION G

  -- we should be trying to construct an endofunctor on (U , `>)
  -- for element data stored at P positions, wiggled by G

  FObjUQuot : U -> UQuot
  FObjUQuot X = record { Carrier = Pos `> X ; Rel = _~G~_ ; EquivR = ActEquiv }
    where open ACTION.Action (faction G A {X})
  

  FObj : U -> U
  FObj X = `UQuot (FObjUQuot X)

  module ReprQuot (T : U) where
    open ACTION.Action (faction G A {T}) public
    open Quot (Pos `> T) _~G~_ ActEquiv public
    
  FArr : (S T : U) -> El (S `> T) -> El (FObj S `> FObj T)
  FArr S T f [c] = elElim (FObj S) [c] (\ _ -> FObj T)
    ( (\ c -> `[ c - f ])
    , \ c0 c1 cq -> homogQuot (c0 - f) (c1 - f)
       (mapHide (id >><< (\ q -> \ p0 p1 pq -> refl (S `> T) f _ _ (q p0 p1 pq))) cq)
    ) where
        open ReprQuot T

  FId : (X : U) -> Pr (Oq (FObj X `> FObj X) (FArr X X id) id)
  FId X = homogTac (FObj X `> FObj X) (FArr X X id) id
    (\ [c] -> quotElimP [c] (\ [c] -> Oq (FObj X) (FArr X X id [c]) (id [c]))
      (\ c -> homogQuot (c - id) c (hide (neu , (homogTac (Pos `> X) (act c neu) c \ p ->
        act-neu c p p (refl Pos p) ))))
    )
    where
      open ReprQuot X

  FComp : (R S T : U)(f : El (R `> S))(g : El (S `> T))
    -> Pr (Oq (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g))
  FComp R S T f g = homogTac (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g)
    \ [c] -> QR.quotElimP [c]
      (\ [c] -> Oq (FObj T) (FArr R T (f - g) [c]) ((FArr R S f - FArr S T g) [c]))
      \ c -> QT.homogQuot (c - (f - g)) ((c - f) - g) (hide (neu , homogTac (Pos `> T)
        (QT.act (c - (f - g)) neu) ((c - f) - g) \ p ->
          QT.act-neu (c - (f - g)) p p (refl Pos p)))
    where
        module QR = ReprQuot R
        module QT = ReprQuot T

  -- from a representable, get a version of it filled with its own positions
  positionTable : El (FObj Pos)
  positionTable = `[ id ]
  
-- Representable Morphism
record _=Repr=>_ (R S : Representable) : Set where
  private
    module R = Representable R
    module S = Representable S
  field
    groupAct=> : R.Act =Action=> S.Act
    
-- Iso of Representables
record _<=Repr=>_ (R S : Representable) : Set where
  private
    module R = Representable R
    module S = Representable S
  field
    groupActIso : R.Act <=Action=> S.Act

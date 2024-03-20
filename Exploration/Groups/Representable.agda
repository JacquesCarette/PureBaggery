module Representable where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Group

module _ (W P : U)(G : Group W)(A : ACTION.Action G P)
  where

  open Group.Group G
  open ACTION G

  -- we should be trying to construct an endofunctor on (U , `>)
  -- for element data stored at P positions, wiggled by G

  FObj : U -> U
  FObj X = `Quotient (P `> X) _~G~_ ActEquiv where
    open Action (faction A {X})
   
  FArr : (S T : U) -> El (S `> T) -> El (FObj S `> FObj T)
  FArr S T f [c] = elElim (FObj S) [c] (\ _ -> FObj T)
    ( (\ c -> `[ c - f ])
    , \ c0 c1 cq -> homogQuot (c0 - f) (c1 - f)
       (mapHide (id >><< (\ q -> \ p0 p1 pq -> refl (S `> T) f _ _ (q p0 p1 pq))) cq)
    ) where
        open Action (faction A {T})
        open Quot (P `> T) _~G~_ ActEquiv

  FId : (X : U) -> Pr (Oq (FObj X `> FObj X) (FArr X X id) id)
  FId X = homogTac (FObj X `> FObj X) (FArr X X id) id
    (\ [c] -> quotElimP [c] (\ [c] -> Oq (FObj X) (FArr X X id [c]) (id [c]))
      (\ c -> homogQuot (c - id) c (hide (neu , (homogTac (P `> X) (act c neu) c \ p ->
        act-neu c p p (refl P p) ))))
    )
    where
      open Action (faction A {X})
      open Quot (P `> X) _~G~_ ActEquiv

  FComp : (R S T : U)(f : El (R `> S))(g : El (S `> T))
    -> Pr (Oq (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g))
  FComp R S T f g = homogTac (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g)
    \ [c] -> QR.quotElimP [c]
      (\ [c] -> Oq (FObj T) (FArr R T (f - g) [c]) ((FArr R S f - FArr S T g) [c]))
      \ c -> QT.homogQuot (c - (f - g)) ((c - f) - g) (hide (neu , homogTac (P `> T)
        (AT.act (c - (f - g)) neu) ((c - f) - g) \ p ->
          AT.act-neu (c - (f - g)) p p (refl P p)))
    where
        module AR = Action (faction A {R})
        module QR = Quot (P `> R) AR._~G~_ AR.ActEquiv
        module AT = Action (faction A {T})
        module QT = Quot (P `> T) AT._~G~_ AT.ActEquiv

module Reasoning where

open import Basics
open import Quotient
open import ExtUni

module _ (X : U) where

{-
  record HomEq (x y : El X) : Set where
    constructor hoq
    field
      homEq : Pr (Eq X X x y)
  open HomEq public      

  HOMEQ : (x y : El X) -> HomEq x y -> Pr (Eq X X x y)
  HOMEQ _ _ = homEq
-}

-- combinators for equational reasoning
module EQPRF (X : U) where
  module _ {y z : El X} where
    _-[_>_ : (x : El X) -> Pr (Eq X X x y) -> Pr (Eq X X y z) -> Pr (Eq X X x z)
    x -[ p > q -- to prove Pr (Eq X X x z), use J with whichever of p and q
               -- has x or z on the right, somewhere we'd like a y
               -- q has z on the right
      = J X q (\ z _ -> `Pr (Eq X X x z)) p
    _<_]-_ : (x : El X) -> Pr (Eq X X y x) -> Pr (Eq X X y z) -> Pr (Eq X X x z)
    x < p ]- q -- this time, p has x on the right (J-ing q needs sym)
      = J X p (\ x _ -> `Pr (Eq X X x z)) q
    infixr 2 _-[_>_ _<_]-_
  _[QED] : (x : El X) -> Pr (Eq X X x x)
  _[QED] x = refl X x
  infixr 3 _[QED]
  -- sometimes it's simpler to just flip a proof around
  !_ : {x y : El X} -> Pr (Eq X X x y) -> Pr (Eq X X y x)
  ! p = _ < p ]- _ [QED]

  -- frequent pattern
  cong : {x y : El X} (f : El (X `> X)) -> Pr (Eq X X x y) -> Pr (Eq X X (f x) (f y))
  cong {x} {y} f x~y = refl (X `> X) f x y x~y

{-
module _ {X : U} where

  open EQPRF X

  _~[_>_ : forall x {y z}
    -> Pr (Eq X X x y)
    -> HomEq X y z
    -> HomEq X x z
  x ~[ p > hoq q = hoq (x -[ p > q)
  _<_]~_ : forall x {y z}
    -> Pr (Eq X X y x)
    -> HomEq X y z
    -> HomEq X x z
  x < p ]~ hoq q = hoq (x < p ]- q)
  infixr 2 _~[_>_ _<_]~_
  _[qed] : forall z -> HomEq X z z
  z [qed] = hoq (z [QED])
-}

module _
  (T : U)(R : El T -> El T -> P)
  (Q : Equiv (El T) (\ i j -> Pr (R i j)))
  where
  open Equiv Q

  homogQuot : (t0 t1 : El T) -> Pr (R t0 t1) ->
    Pr (Eq (`Quotient T R Q) (`Quotient T R Q) `[ t0 ] `[ t1 ])
  homogQuot t0 t1 r = hide (t1 , t1 , r , refl T t1 , eqR t1)

  eqQ : (x y : El T) -> Pr (Eq T T x y) -> Pr (R x y)
  eqQ x y q = J T q (\ y _ -> `Pr (R x y)) (eqR x)

  module EQUIVPRF where

    _~[_>_ : forall x {y z}
      -> Pr (R x y)
      -> Pr (R y z)
      -> Pr (R x z)
    x ~[ p > q = eqT _ _ _ p q
    _<_]~_ : forall x {y z}
      -> Pr (R y x)
      -> Pr (R y z)
      -> Pr (R x z)
    x < p ]~ q = eqT _ _ _ (eqS _ _ p) q
    infixr 2 _~[_>_ _<_]~_
    _[qed] : forall z -> Pr (R z z)
    z [qed] = eqR _

HomogTac : (T : U)(x y : El T) -> Set
HomogTac (`Quotient T R Q) `[ x ] `[ y ] = Pr (R x y)
HomogTac _ x y = Zero

homogTac : (T : U)(x y : El T) -> HomogTac T x y -> Pr (Eq T T x y)
homogTac (`Quotient T R Q) `[ x ] `[ y ] r = homogQuot T R Q x y r


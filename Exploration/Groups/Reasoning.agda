module Reasoning where

open import Basics
open import Quotient
open import ExtUni
open import Nary

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

-- combinators for equational reasoning (over U)
module EQPRF (X : U) where
  module _ {y z : El X} where
    _-[_>_ : (x : El X) -> Pr (Oq X x y) -> Pr (Oq X y z) -> Pr (Oq X x z)
    x -[ p > q -- to prove Pr (Oq X x z), use J with whichever of p and q
               -- has x or z on the right, somewhere we'd like a y
               -- q has z on the right
      = J X q (\ z _ -> `Pr (Oq X x z)) p
    _<_]-_ : (x : El X) -> Pr (Oq X y x) -> Pr (Oq X y z) -> Pr (Oq X x z)
    x < p ]- q -- this time, p has x on the right (J-ing q needs sym)
      = J X p (\ x _ -> `Pr (Oq X x z)) q
    infixr 2 _-[_>_ _<_]-_
  _[QED] : (x : El X) -> Pr (Oq X x x)
  _[QED] x = refl X x
  infixr 3 _[QED]
  -- sometimes it's simpler to just flip a proof around
  !_ : {x y : El X} -> Pr (Oq X x y) -> Pr (Oq X y x)
  ! p = _ < p ]- _ [QED]

  -- frequent pattern; unfortunately the Y can rarely be inferred, so explicit
  cong : (Y : U){x y : El Y} (f : El (Y `> X)) -> Pr (Oq Y x y) -> Pr (Oq X (f x) (f y))
  cong Y {x} {y} f x~y = refl (Y `> X) f x y x~y

  trans : (x y z : El X) ->
    Pr (Oq X x y) -> Pr (Oq X y z) -> Pr (Oq X x z)
  trans x y z xy yz = x -[ xy > y -[ yz > z [QED]  

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

module Quot
  (T : U)(R : El T -> El T -> P)
  (Q : Equiv (El T) (\ i j -> Pr (R i j)))
  where
  open Equiv Q
  `Q = `Quotient T R Q

  homogQuot : (t0 t1 : El T) -> Pr (R t0 t1) ->
    Pr (Oq `Q `[ t0 ] `[ t1 ])
  homogQuot t0 t1 r = hide (t1 , t1 , r , refl T t1 , eqR t1)

  -- when doing things in a quotient, we can assume a representative
  quotElimP : (x0 : El `Q ) -> (M : El `Q -> P) ->
    ((t : El T) -> Pr (M `[ t ])) ->
    Pr (M x0)
  quotElimP x0 M holds = elElim `Q x0 (\ x0 -> `Pr (M x0)) (holds , _)

  quotElimPN : (n : Nat) -> (M : N-ary-Rel n P (El `Q)) -> Pr (N-ary-RelNP T `Q `[_] n M `=>
    N-ary-RelNP `Q `Q id n M)
  quotElimPN ze M hyp = hyp
  quotElimPN (su n) M hyp x = quotElimP x (\ x -> N-ary-RelNP `Q `Q id n (M x))
    \ t -> quotElimPN n (M `[ t ]) (hyp t)
  
  eqQ : (x y : El T) -> Pr (Oq T x y) -> Pr (R x y)
  eqQ x y q = J T q (\ y _ -> `Pr (R x y)) (eqR x)

  unHomogQuot : (t0 t1 : El T)
    -> Pr (Oq `Q `[ t0 ] `[ t1 ])
    -> Pr (R t0 t1)
  unHomogQuot t0 t1 q = irr (R t0 t1) (mapHide (help t0 t1) q) where
    help : (t0 t1 : El T)
       -> El (T `>< \ m0 -> T `>< \ m1 -> `Pr (R t0 m0 `/\ Eq T T m0 m1 `/\ R m1 t1))
       -> Pr (R t0 t1)
    help t0 t1 (m0 , m1 , r0 , mq , r1) = J T mq (\ m1 _ -> `Pr (R m1 t1 `=> R t0 t1))
      (\ r1 -> eqT t0 m0 t1 r0 r1)
      r1

  LiftingOK : (n : Nat)(f : El (N-ary n T)) -> P
  LiftingOK ze     f = `One
  LiftingOK (su n) f
    =   (T `-> \ t0 -> T `-> \ t1 -> R t0 t1 `=> FunRelated T R n (f t0) (f t1))
    `/\ (T `-> \ t -> LiftingOK n (f t))

  lifting : (n : Nat)(f : El (N-ary n T))(OK : Pr (LiftingOK n f))
         -> El (N-ary n `Q)
  liftLater : (n : Nat)(f g : El (N-ary n T))(fOK : Pr (LiftingOK n f))(gOK : Pr (LiftingOK n g))
    -> Pr (FunRelated T R n f g)
    -> Pr (Oq (N-ary n `Q)
         (lifting n f fOK) (lifting n g gOK))
  lifting ze f OK = `[ f ]
  lifting (su n) f (OKnow , OKlater) x = elElim `Q x (\ _ -> N-ary n `Q)
    ( (\ t -> lifting n (f t) (OKlater t))
    , \ t0 t1 tr -> liftLater n (f t0) (f t1) (OKlater t0) (OKlater t1) (OKnow t0 t1 tr)
    )
  liftLater ze f g fOK gOK fg = homogQuot f g fg
  liftLater (su n) f g fOK gOK fg t0 t1 tq = J `Q tq
    (\ t1 _ -> `Pr (Oq (N-ary n `Q) (lifting (su n) f fOK t0) (lifting (su n) g gOK t1)))
    (elElim `Q t0
      (\ t0 ->  `Pr (Oq (N-ary n `Q) (lifting (su n) f fOK t0) (lifting (su n) g gOK t0)))
      ( (\ t -> liftLater n (f t) (g t) (snd fOK t) (snd gOK t) (fg t))
      , _))

  -- uses Q implicitly through eqT
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

-- Tactic for homogeneous quotients and function types
HomogTac : (T : U)(x y : El T) -> P
  -- this is a bit wicked, unpacking representatives; should elim properly
HomogTac (`Quotient T R Q) `[ x ] `[ y ] = R x y
HomogTac (S `-> T) f g = S `-> \ s -> Oq (T s) (f s) (g s)
HomogTac _ x y = `Zero

homogTac : (T : U)(x y : El T) -> Pr (HomogTac T x y) -> Pr (Oq T x y)
  -- this is a bit wicked, unpacking representatives; should elim properly
homogTac (`Quotient T R Q) `[ x ] `[ y ] r = Quot.homogQuot T R Q x y r
homogTac (S `-> T) f g r x y q =
  J S q (\ y _ -> `Pr (Eq (T x) (T y) (f x) (g y))) (r x)


module Representable where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Group
open import Iso
open import GroupsWeLike
open import Numbers

module Representable (W P : U)(G : Group W)(A : ACTION.Action G P)
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

Jumble : U -> U -> U
Jumble P X = FObj X where
  open Representable (P <=> P) P (Automorphism P) (AutAct P)


{-
move these somewhere more appropriate?
-}

_<_ : Nat -> Nat -> P
x < ze = `Zero
ze < su y = `One
su x < su y = x < y

Fin : Nat -> U
Fin n = `Nat `>< \ i -> `Pr (i < n)

finL : (n m : Nat) -> El (Fin n `> Fin (n +N m))
finL n m (i , p) = i , slackR i n m p where
  slackR : (i n m : Nat) -> Pr ((i < n) `=> (i < (n +N m)))
  slackR ze (su n) m p = <>
  slackR (su i) (su n) m p = slackR i n m p

finR : (n m : Nat) -> El (Fin m `> Fin (n +N m))
finR n m (i , p) = (n +N i) , shiftL n i m p where
  shiftL : (n i m : Nat) -> Pr ((i < m) `=> ((n +N i) < (n +N m)))
  shiftL ze i m p = p
  shiftL (su n) i m p = shiftL n i m p

finCase : (n m : Nat)(i : El (Fin (n +N m)))(F : El (Fin (n +N m)) -> U)
  -> ((j : El (Fin n)) -> El (F (finL n m j)))
  -> ((k : El (Fin m)) -> El (F (finR n m k)))
  -> El (F i)
finCase ze m ip F fl fr = fr ip
finCase (su n) m (ze , p) F fl fr = fl (ze , <>)
finCase (su n) m (su i , p) F fl fr = finCase n m (i , p) (\ (i , p) -> F (su i , p))
  (\ (j , p) -> fl (su j , p))
  fr

Bag : U -> U
Bag X = `Nat `>< \ n -> Jumble (Fin n) X

module _ (X : U) where

  nilB : El (Bag X)
  nilB = 0 , `[ snd - naughtE ]

  oneB : El (X `> Bag X)
  oneB x = 1 , `[ (\ _ -> x) ]

  _+B_ : El (Bag X `> Bag X `> Bag X)
  (n , [f]) +B (m , [g]) = (n +N m) , elElim (Jumble (Fin n) X) [f] (\ _ -> Jumble (Fin (n +N m)) X)
    ( (\ f -> elElim (Jumble (Fin m) X) [g] (\ _ -> Jumble (Fin (n +N m)) X)
        ( (\ g -> `[ (\ ip -> finCase n m ip (\ _ -> X) f g) ])
        , {!!})
        )
    , {!!}
    )

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

finCase : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> ((j : El (Fin n)) -> El (F (finL n m j)))
  -> ((k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin (n +N m))) -> El (F i)
finCase ze m F fl fr = fr
finCase (su n) m F fl fr (ze , p) = fl (ze , <>)
finCase (su n) m F fl fr (su i , p) = finCase n m ((su >><< id) - F)
  ((su >><< id) - fl)
  fr
  (i , p)

finCaseL : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> (l : (j : El (Fin n)) -> El (F (finL n m j)))
  -> (r : (k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin n)) -> Pr (Oq (F (finL n m i)) (finCase n m F l r (finL n m i)) (l i))
finCaseL (su n) m F l r (ze , <>) = refl (F (finL (su n) m (ze , <>))) (l (ze , <>))
finCaseL (su n) m F l r (su i , p) = finCaseL n m ((su >><< id) - F)
  ((su >><< id) - l)
  r
  (i , p)

finCaseR : (n m : Nat)(F : El (Fin (n +N m)) -> U)
  -> (l : (j : El (Fin n)) -> El (F (finL n m j)))
  -> (r : (k : El (Fin m)) -> El (F (finR n m k)))
  -> (i : El (Fin m)) -> Pr (Oq (F (finR n m i)) (finCase n m F l r (finR n m i)) (r i))
finCaseR ze m F l r ip = refl (F ip) (r ip)
finCaseR (su n) m F l r = finCaseR n m ((su >><< id) - F)
  ((su >><< id) - l)
  r

FinAut : Nat -> U
FinAut n = Fin n <=> Fin n

FinEn : Nat -> U
FinEn n = Fin n `> Fin n

module FINSUM (n n' m m' : Nat)(h : El (Fin n `> Fin n'))(k : El (Fin m `> Fin m')) where
  _<+N>_ : El (Fin (n +N m) `> Fin (n' +N m'))
  _<+N>_ = finCase n m (\ _ -> Fin (n' +N m')) (h - finL n' m') (k - finR n' m')
  
  sumLeft : (i : El (Fin n)) -> Pr (Oq (Fin (n' +N m')) (_<+N>_ (finL n m i)) (finL n' m' (h i)))
  sumLeft = finCaseL n m (\ _ -> Fin (n' +N m')) (h - finL n' m') (k - finR n' m')

  sumRight : (i : El (Fin m)) -> Pr (Oq (Fin (n' +N m')) (_<+N>_ (finR n m i)) (finR n' m' (k i)))
  sumRight = finCaseR n m (\ _ -> Fin (n' +N m')) (h - finL n' m') (k - finR n' m')

module FINSUMAUT (n m : Nat) where
  open FINSUM n n m m

  finCaseAut : El (FinAut n `> FinAut m `> FinAut (n +N m))
  finCaseAut (f , fop , fq0 , fq1) (g , gop , gq0 , gq1)
    = (f <+N> g)
    , (fop <+N> gop)
    , (finCase n m (\ ip -> `Pr (Oq (Fin (n +N m)) ((fop <+N> gop) ((f <+N> g) ip)) ip))
        (\ jp -> vert (leftLemma f fop g gop fq0 jp))
        (\ kp -> vert (rightLemma f fop g gop gq0 kp)))
    , (finCase n m (\ ip -> `Pr (Oq (Fin (n +N m)) ((f <+N> g) ((fop <+N> gop) ip)) ip))
        (\ jp -> vert (leftLemma fop f gop g fq1 jp))
        (\ kp -> vert (rightLemma fop f gop g gq1 kp)))
    where
    open EQPRF (Fin (n +N m))
    leftLemma : (h hop : El (FinEn n))(k kop : El (FinEn m))
      -> ((i : El (Fin n)) -> Pr (Oq (Fin n) (hop (h i)) i))
      -> (i : El (Fin n)) -> (hop <+N> kop) ((h <+N> k) (finL n m i)) == (finL n m i)
    leftLemma h hop k kop hhopq i = 
      ((hop <+N> kop) ((h <+N> k) (finL n m i)))
        ==[ congB (Fin (n +N m)) (hop <+N> kop) (sumLeft h k i) >
      ((hop <+N> kop) (finL n m (h i)))
        ==[ bleu (sumLeft hop kop (h i)) >
      (finL n m (hop (h i)))
        ==[ congB (Fin n) (finL n m) (hhopq i) >
      (finL n m i) [==]
    rightLemma : (h hop : El (FinEn n))(k kop : El (FinEn m))
      -> ((i : El (Fin m)) -> Pr (Oq (Fin m) (kop (k i)) i))
      -> (i : El (Fin m)) -> (hop <+N> kop) ((h <+N> k) (finR n m i)) == (finR n m i)
    rightLemma h hop k kop kkopq i =
      ((hop <+N> kop) ((h <+N> k) (finR n m i)))
        ==[ congB (Fin (n +N m)) (hop <+N> kop) (sumRight h k i) >
      ((hop <+N> kop) (finR n m (k i)))
        ==[ bleu (sumRight hop kop (k i)) >
      (finR n m (kop (k i)))
        ==[ congB (Fin m) (finR n m) (kkopq i) >
      (finR n m i) [==]

Bag : U -> U
Bag X = `Nat `>< \ n -> Jumble (Fin n) X

module _ (X : U) where

  open EQPRF X

  nilB : El (Bag X)
  nilB = 0 , `[ snd - naughtE ]

  oneB : El (X `> Bag X)
  oneB x = 1 , `[ (\ _ -> x) ]

  _+B_ : El (Bag X `> Bag X `> Bag X)
  (n , [f]) +B (m , [g]) = (n +N m) , elElim (Jumble (Fin n) X) [f] (\ _ -> Jumble (Fin (n +N m)) X)
    ( (\ f -> elElim (Jumble (Fin m) X) [g] (\ _ -> Jumble (Fin (n +N m)) X)
        ( (\ g -> `[ finCase n m (\ _ -> X) f g ])
        , \ h k -> mapHide (\ (fm@(flr , frl , fq0 , fq1) , q) -> finCaseAut (idIso (Fin n)) fm , 
                homogTac (Fin (n +N m) `> X) _ _ (
                  finCase n m (\ i -> `Pr (Oq X
                     (ACTION.Action.act
                      (ACTION.faction (Automorphism (Fin (n +N m)))
                       (AutAct (Fin (n +N m))) {X})
                       (finCase n m (\ _ -> X) f h)
                          (finCaseAut (idIso (Fin n)) fm) i)
                          (finCase n m (\ _ -> X) f k i)))
                    {!!}
                    \ i -> let iH = q i i (refl (Fin m) i) in vert (
                      (finCase n m (\ _ -> X) f h ((id <+N> frl) (finR n m i)))
                        ==[ congB (Fin (n +N m)) (finCase n m (\ _ -> X) f h) (sumRight id frl i) >
                      (finCase n m (\ _ -> X) f h (finR n m (frl i)))
                        ==[ bleu (finCaseR n m (\ _ -> X) f h (frl i)) >
                      (h (frl i))
                        ==[ bleu iH >
                      k i
                        < bleu (finCaseR n m (\ _ -> X) f k i) ]==
                      (finCase n m (\ _ -> X) f k (finR n m i)) [==])))
               - homogTac (Jumble (Fin (n +N m)) X)
                  `[ finCase n m (\ _ -> X) f h ]
                  `[ finCase n m (\ _ -> X) f k ])
        )
    , {!!}
    )
    where
      open FINSUM n n m m
      open FINSUMAUT n m

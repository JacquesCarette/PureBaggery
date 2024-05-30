module Representable where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Group
open import Iso
open import GroupsWeLike
open import Numbers

record Representable : Set where
  field
    {Wiggles} : U
    Positions : U
    Grp  : Group Wiggles
    Act : ACTION.Action Grp Positions

-- Extension of a representable
module REPRESENTABLE (R : Representable) where
  open Representable R renaming (Wiggles to W; Grp to G; Positions to Pos; Act to A)

  open Group.Group G
  open ACTION G

  -- we should be trying to construct an endofunctor on (U , `>)
  -- for element data stored at P positions, wiggled by G

  FQuot : U -> UQuot
  FQuot X = record { Carrier = Pos `> X ; Rel = _~G~_ ; EquivR = ActEquiv }
    where open Action (faction A {X})
  

  FObj : U -> U
  FObj X = `UQuot (FQuot X)
   
  FArr : (S T : U) -> El (S `> T) -> El (FObj S `> FObj T)
  FArr S T f [c] = elElim (FObj S) [c] (\ _ -> FObj T)
    ( (\ c -> `[ c - f ])
    , \ c0 c1 cq -> homogQuot (c0 - f) (c1 - f)
       (mapHide (id >><< (\ q -> \ p0 p1 pq -> refl (S `> T) f _ _ (q p0 p1 pq))) cq)
    ) where
        open Action (faction A {T})
        open Quot (Pos `> T) _~G~_ ActEquiv

  FId : (X : U) -> Pr (Oq (FObj X `> FObj X) (FArr X X id) id)
  FId X = homogTac (FObj X `> FObj X) (FArr X X id) id
    (\ [c] -> quotElimP [c] (\ [c] -> Oq (FObj X) (FArr X X id [c]) (id [c]))
      (\ c -> homogQuot (c - id) c (hide (neu , (homogTac (Pos `> X) (act c neu) c \ p ->
        act-neu c p p (refl Pos p) ))))
    )
    where
      open Action (faction A {X})
      open Quot (Pos `> X) _~G~_ ActEquiv

  FComp : (R S T : U)(f : El (R `> S))(g : El (S `> T))
    -> Pr (Oq (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g))
  FComp R S T f g = homogTac (FObj R `> FObj T) (FArr R T (f - g)) (FArr R S f - FArr S T g)
    \ [c] -> QR.quotElimP [c]
      (\ [c] -> Oq (FObj T) (FArr R T (f - g) [c]) ((FArr R S f - FArr S T g) [c]))
      \ c -> QT.homogQuot (c - (f - g)) ((c - f) - g) (hide (neu , homogTac (Pos `> T)
        (AT.act (c - (f - g)) neu) ((c - f) - g) \ p ->
          AT.act-neu (c - (f - g)) p p (refl Pos p)))
    where
        module AR = Action (faction A {R})
        module QR = Quot (Pos `> R) AR._~G~_ AR.ActEquiv
        module AT = Action (faction A {T})
        module QT = Quot (Pos `> T) AT._~G~_ AT.ActEquiv

-- Representable Morphism
record _=Repr=>_ (R S : Representable) : Set where
  private
    module R = Representable R
    module S = Representable S
  field
    groupAct=> : R.Act =Action=> S.Act
    
record ContainerDesc : Set where
  constructor _<|_
  field
    Shape : U
    Store : El Shape -> Representable

  [_]C : U -> U
  [_]C X = Shape `>< \ s -> let open REPRESENTABLE (Store s) in FObj X

  -- and [_]C is a Functor (all the hard work is in REPRESENTABLE)

  
open ContainerDesc public
open Representable public

record _=CtrD=>_ (C D : ContainerDesc) : Set where
  private
    module C = ContainerDesc C
    module D = ContainerDesc D
  open REPRESENTABLE
  field
    shape=> : El (C.Shape `> D.Shape)
    store<= : forall c -> D.Store (shape=> c) =Repr=> C.Store c

  -- induced action on containers
  [_]C=> : (X : U) -> El ([ C ]C X `> [ D ]C X)
  [_]C=> X (s , f) = shape=> s ,
    UQlifting (FQuot (C.Store s) X ,- []) (FQuot (D.Store (shape=> s)) X)
    (carrier=> -_)
    ((\ f0 f1 -> mapHide (mor >><< \ {g} pq p0 p1 pr → 
      f0 (carrier=> (dact p0 (inv GD (mor g))))  < cong WD (dact p0 - (carrier=> - f0)) (inv-pres g) ]-
      f0 (carrier=> (dact p0 (mor (inv GC g))))  < cong PC f0 (act-pres p0 (inv GC g)) ]-
      f0 (cact (carrier=> p0) (inv GC g))        -[ pq (carrier=> p0) (carrier=> p1) (EQPRF.cong PC PD carrier=> pr) >
      f1 (carrier=> p1)                          [QED]))
      , _)
    f
    where
      open _=Repr=>_ (store<= s)
      open _=Action=>_ groupAct=>
      open _=Group=>_ group=>
      open Group.Group
      open ACTION.Action
      open EQPRF X
      PC = Positions (C.Store s)
      PD = Positions (D.Store (shape=> s))
      GC = Grp (C.Store s)
      GD = Grp (D.Store (shape=> s))
      cact = act (Act (C.Store s))
      dact = act (Act (D.Store (shape=> s)))
      WD = Wiggles (D.Store (shape=> s))

  -- and it is natural (TODO)

Rep : U -> Representable
Wiggles (Rep S) = _
Positions (Rep S) = S
Grp (Rep S) = Trivial
Act (Rep S) = IdentityAct Trivial S

KC : U -> ContainerDesc
Shape (KC X) = `One
Store (KC X) _ = Rep `Zero

OneC = KC `One

IC : ContainerDesc
Shape IC = `One
Store IC _ = Rep `One
  
_*C_ : ContainerDesc -> ContainerDesc -> ContainerDesc
Shape ((Sh0 <| St0) *C (Sh1 <| St1)) = Sh0 `* Sh1
Wiggles (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = _
Positions (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = Positions (St0 sh0) `+ Positions (St1 sh1)
Grp (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = Grp (St0 sh0) *Group* Grp (St1 sh1)
Act (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = pairActsOnSum _ _ (Act (St0 sh0)) (Act (St1 sh1))

module _ (S T : ContainerDesc) where

  open REPRESENTABLE
  open Group.Group
  open ACTION.Action

  pairC : (X : U) -> (([ S ]C X `* [ T ]C X) <==> [ S *C T ]C X)
  fwd (pairC X) ((s , f) , (t , g))
    = (s , t)
    , UQlifting (FQuot (Store S s) X ,- FQuot (Store T t) X ,- []) (FQuot (Store (S *C T) (s , t)) X)
      (\ f g -> /\ (f <01> g))
      ((\ f0 f1 fr g -> mapHide (\ (w , wr) -> (w , neu (Grp (Store T t))) , 
          homogTac ((Positions (Store S s) `+ Positions (Store T t)) `> X) _ _
            (/\ ((\ p -> wr p p (refl (Positions (Store S s)) p))
            <01> \ p -> refl (Positions (Store T t) `> X) g _ _
                    (act-eq-neu (Act (Store T t)) _ p (invneu (Grp (Store T t)))))))
          fr)
       , \ f -> (\ g0 g1 -> mapHide \ (w , wr) -> (neu (Grp (Store S s)) , w) ,
          homogTac ((Positions (Store S s) `+ Positions (Store T t)) `> X) _ _
          (/\ ((\ p -> refl (Positions (Store S s) `> X) f _ _ (act-eq-neu (Act (Store S s)) _ p (invneu (Grp (Store S s)))))
          <01> \ p -> wr p p (refl (Positions (Store T t)) p))))
              , _)
      f
      g
  bwd (pairC X) ((s , t) , h)
    = (s , UQlifting (FQuot (Store (S *C T) (s , t)) X ,- []) (FQuot (Store S s) X)
           (\ h p -> h (`0 , p))
           ( (\ f0 f1 -> mapHide \ ((ws , wt) , q) -> ws , \ p0 p1 pq -> q (`0 , p0) (`0 , p1) (_ , pq))
           , _)
           h)
    , (t ,  UQlifting (FQuot (Store (S *C T) (s , t)) X ,- []) (FQuot (Store T t) X)
           (\ h p -> h (`1 , p))
           ( (\ f0 f1 -> mapHide \ ((ws , wt) , q) -> wt , \ p0 p1 pq -> q (`1 , p0) (`1 , p1) (_ , pq))
           , _)
           h)
    
  fwd-bwd (pairC X) ((s , f) , (t , g))
    = (refl (Shape S) s , elElim (FObj (Store S s) X) f (\ f -> `Pr (Oq (FObj (Store S s) X)
                            (snd (fst (bwd (pairC X) (fwd (pairC X) ((s , f) , t , g))))) f))
                            ( (\ f -> homogTac (FObj (Store S s) X)
                                      (snd (fst (bwd (pairC X) (fwd (pairC X) ((s , `[ f ]) , t , g)))))
                                      `[ f ]
                               (hide (neu (Grp (Store S s)) , 
                                   homogTac (Positions (Store S s) `> X) _ _ \ p ->
                                     EQPRF.cong X (Positions (Store S s)) f
                                      (act-eq-neu (Act (Store S s)) (inv (Grp (Store S s)) (neu (Grp (Store S s)))) p
                                        (invneu (Grp (Store S s))))) ))
                            , _) )
    , (refl (Shape T) t ,   elElim (FObj (Store T t) X) g (\ g -> `Pr (Oq (FObj (Store T t) X)
                            (snd (snd (bwd (pairC X) (fwd (pairC X) ((s , f) , t , g))))) g))
                            (((\ g -> homogTac (FObj (Store T t) X)
                                      (snd (snd (bwd (pairC X) (fwd (pairC X) ((s , f) , t , `[ g ])))))
                                      `[ g ]
                               (hide (neu (Grp (Store T t)) , 
                                   homogTac (Positions (Store T t) `> X) _ _ \ p ->
                                     EQPRF.cong X (Positions (Store T t)) g
                                      (act-eq-neu (Act (Store T t)) (inv (Grp (Store T t)) (neu (Grp (Store T t)))) p
                                        (invneu (Grp (Store T t))))) )))
                            , _))
  bwd-fwd (pairC X) ((s , t) , h)
    = refl (Shape S `* Shape T) (s , t)
    , elElim (FObj (Store (S *C T) (s , t)) X) h (\ h -> `Pr (Oq (FObj (Store (S *C T) (s , t)) X)
        (snd (fwd (pairC X) (bwd (pairC X) ((s , t) , h)))) h))
       ( (\ h -> homogTac (FObj (Store (S *C T) (s , t)) X)
                  (snd (fwd (pairC X) (bwd (pairC X) ((s , t) , `[ h ])))) `[ h ]
           (hide (neu (Grp (Store S s) *Group* Grp (Store T t))
                 , homogTac (Positions (Store (S *C T) (s , t)) `> X) _ _
                   (/\ ((\ p -> EQPRF.cong X (Positions (Store S s)) ((`0 ,_) - h) (
                      act-eq-neu (Act (Store S s)) (inv (Grp (Store S s)) (neu (Grp (Store S s)))) p
                                        (invneu (Grp (Store S s)))))
                   <01> \ p -> EQPRF.cong X (Positions (Store T t)) ((`1 ,_) - h)
                                      (act-eq-neu (Act (Store T t)) (inv (Grp (Store T t)) (neu (Grp (Store T t)))) p
                                        (invneu (Grp (Store T t)))))))))
       , _)


JumbleR : U -> Representable
JumbleR P = record { Positions = P ; Grp = Automorphism P ; Act = AutAct P }

JUQuot : U -> U -> UQuot
JUQuot P X = FQuot X where
  open REPRESENTABLE (JumbleR P)
  
Jumble : U -> U -> U
Jumble P X = `UQuot (JUQuot P X)

module _ (X : U){P Q : U}(pq : P <==> Q) where
  open EQPRF X

  isoPmapJumble : El (Jumble P X `> Jumble Q X)
  isoPmapJumble [f] = elElim (Jumble P X) [f] (\ _ -> Jumble Q X)
    ( (\ f -> `[ bwd pq - f ])
    , \ h k hk -> homogTac (Jumble Q X) `[ bwd pq - h ] `[ bwd pq - k ]
      (mapHide (\ (pr , hkP) -> osi (via (iso' {P}{P} pr) pq) ,
        homogTac (Q `> X) _ _ \ x -> vert (
            h (bwd pq (fwd pq (bwd (iso' {P}{P} pr) (bwd pq x))))
              ==[ congB P h (fwd-bwd pq _) >
            h (bwd (iso' {P}{P} pr) (bwd pq x))
              ==[ bleu (hkP (bwd pq x) (bwd pq x) (refl P _)) >
            k (bwd pq x)
              [==])
        ) hk)
    )

module _ (X : U){P Q : U}(pq : P <==> Q) where
  open EQPRF X

  isoPisoJumbleP : Jumble P X <==> Jumble Q X
  fwd isoPisoJumbleP = isoPmapJumble X pq
  bwd isoPisoJumbleP = isoPmapJumble X (invIso' pq)
  fwd-bwd isoPisoJumbleP [f] = elElim (Jumble P X) [f]
    (\ [f] -> `Pr (Oq (Jumble P X) (bwd isoPisoJumbleP (fwd isoPisoJumbleP [f])) [f]))
    ( (\ f -> homogTac (Jumble P X) (bwd isoPisoJumbleP (fwd isoPisoJumbleP `[ f ])) `[ f ]
        (hide (idIso P , homogTac (P `> X) ((fwd pq - bwd pq) - f) f
          \ p -> vert (congB P f (fwd-bwd pq p)))))
    , _
    )
  bwd-fwd isoPisoJumbleP [f] = elElim (Jumble Q X) [f]
    (\ [f] -> `Pr (Oq (Jumble Q X) (fwd isoPisoJumbleP (bwd isoPisoJumbleP [f])) [f]))
    ( (\ f -> homogTac (Jumble Q X) (fwd isoPisoJumbleP (bwd isoPisoJumbleP `[ f ])) `[ f ]
        (hide (idIso Q , homogTac (Q `> X) ((bwd pq - fwd pq) - f) f
          \ q -> vert (congB Q f (bwd-fwd pq q)))))
    , _
    )
    
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

module FINSUMADD (n m : Nat) where
  finSumAdd : Fin (n +N m) <==> (Fin n `+ Fin m)
  fwd finSumAdd = finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_)
  bwd finSumAdd = /\ (finL n m <01> finR n m)
  fwd-bwd finSumAdd = finCase n m (\ s -> `Pr (Oq (Fin (n +N m)) (bwd finSumAdd (fwd finSumAdd s)) s))
    (\ j -> let open EQPRF (Fin (n +N m)) in vert (
            (bwd finSumAdd (finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) (finL n m j)))
              ==[ congB (Fin n `+ Fin m) {fwd finSumAdd (finL n m j)} {`0 , j}
                      (bwd finSumAdd) (finCaseL n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) j ) >
            (bwd finSumAdd (`0 , j))
              ==[ reflB >
             finL n m j [==]))
    \ k -> let open EQPRF (Fin (n +N m)) in vert (
            (bwd finSumAdd (finCase n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) (finR n m k)))
              ==[ congB (Fin n `+ Fin m) {fwd finSumAdd (finR n m k)} {`1 , k}
                      (bwd finSumAdd) (finCaseR n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) k ) >
            (bwd finSumAdd (`1 , k))
              ==[ reflB >
             finR n m k [==])
  bwd-fwd finSumAdd (`0 , j) = finCaseL n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) j
  bwd-fwd finSumAdd (`1 , k) = finCaseR n m (\ _ -> (Fin n `+ Fin m)) (`0 ,_) (`1 ,_) k
  
module FINSUMAUT (n m : Nat) where
  open FINSUMADD n m

  finCaseAut : El (FinAut n `> FinAut m `> FinAut (n +N m))
  finCaseAut f g = osi (
    Fin (n +N m) =[ finSumAdd >
    Fin n `+ Fin m =[ sgIso `Two (iso' f <01> iso' g) >
    Fin n `+ Fin m < finSumAdd ]=
    Fin (n +N m) [ISO])

BagC : ContainerDesc
Shape BagC = `Nat
Store BagC n = JumbleR (Fin n)


Bag : U -> U
Bag = [ BagC ]C -- `Nat `>< \ n -> Jumble (Fin n) X


module _ (X : U) where

  open EQPRF X
  open _=CtrD=>_

  nilBCM : OneC =CtrD=> BagC
  shape=> nilBCM _ = 0
  _=Action=>_.carrier=> (_=Repr=>_.groupAct=> (store<= nilBCM _)) = snd
  _=SemiGroup=>_.mor (_=Monoid=>_.semigroup=> (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= nilBCM _))))) _ = id , id , (snd - naughtE) , (snd - naughtE)
  _=SemiGroup=>_.mul-pres (_=Monoid=>_.semigroup=> (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= nilBCM _))))) _ _ = (snd - naughtE) , (snd - naughtE) , _
  _=Monoid=>_.neu-pres (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= nilBCM _)))) = (snd - naughtE) , (snd - naughtE) , _
  _=Action=>_.act-pres (_=Repr=>_.groupAct=> (store<= nilBCM _)) = _

  nilB : El (Bag X)
  nilB = [ nilBCM ]C=> X (_ , `[ naughtE ])
  -- 0 , `[ snd - naughtE ]

  oneBCM : IC =CtrD=> BagC
  shape=> oneBCM _ = 1
  _=Action=>_.carrier=> (_=Repr=>_.groupAct=> (store<= oneBCM _)) = _
  _=SemiGroup=>_.mor (_=Monoid=>_.semigroup=> (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= oneBCM _))))) _ = id , id , (\ { (ze , p) -> _ }) , \ { (ze , p) -> _ }
  _=SemiGroup=>_.mul-pres (_=Monoid=>_.semigroup=> (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= oneBCM _))))) _ _ = (\ { (ze , _) (ze , _) -> _ }) , (\ { (ze , _) (ze , _) -> _ }) , _
  _=Monoid=>_.neu-pres (_=Group=>_.monoid=> (_=Action=>_.group=> (_=Repr=>_.groupAct=> (store<= oneBCM _)))) = (\ { (ze , _) (ze , _) -> _ }) , (\ { (ze , _) (ze , _) -> _ }) , _
  _=Action=>_.act-pres (_=Repr=>_.groupAct=> (store<= oneBCM _)) = _

  oneB : El (X `> Bag X)
  oneB x = 1 , `[ (\ _ -> x) ]
{-
  module _ (n m : Nat) where
    open FINSUMAUT n m
    Jumble+ : El (Jumble (Fin n) X `> Jumble (Fin m) X `> Jumble (Fin (n +N m)) X)
    Jumble+ = UQlifting (JUQuot (Fin n) X ,- JUQuot (Fin m) X ,- []) (JUQuot (Fin (n +N m)) X)
      (finCase n m (\ _ -> X))
      ((\ f0 f1 fr g -> mapHide
         (\ (fm , q) -> finCaseAut fm (idIso (Fin m))
         , homogTac (Fin (n +N m) `> X) _ _ {!!} )
        fr)
      , \ f ->
        (\ g0 g1 gr -> mapHide {!!} gr)
        , _
      )
-}
{-
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
                    (\ j -> vert (  -- we're identity on the left, so it's pushing finL through finCase
                      finCase n m (\ _ -> X) f h
                       (finCase n m (\ _ -> Fin (n +N m)) (finL n m) _ (finL n m j))
                        ==[ congB (Fin (n +N m)) (finCase n m (\ _ -> X) f h)
                            (finCaseL n m (\ _ -> Fin (n +N m)) (finL n m) _ j) >
                      finCase n m (\ _ -> X) f h (finL n m j)
                        ==[ bleu (finCaseL n m (\ _ -> X) f h j) >
                      f j
                        < bleu (finCaseL n m (\ _ -> X) f k j) ]==
                      (finCase n m (\ _ -> X) f k (finL n m j))
                        [==]))
                    (\ i -> let iH = q i i (refl (Fin m) i) in vert (
                        -- on the right, we actually need the relatedness of h and k
                      (finCase n m (\ _ -> X) f h ((id <+N> frl) (finR n m i)))
                        ==[ congB (Fin (n +N m)) (finCase n m (\ _ -> X) f h) (sumRight id frl i) >
                      (finCase n m (\ _ -> X) f h (finR n m (frl i)))
                        ==[ bleu (finCaseR n m (\ _ -> X) f h (frl i)) >
                      (h (frl i))
                        ==[ bleu iH >
                      k i
                        < bleu (finCaseR n m (\ _ -> X) f k i) ]==
                      (finCase n m (\ _ -> X) f k (finR n m i)) [==]))))
               - homogTac (Jumble (Fin (n +N m)) X)
                  `[ finCase n m (\ _ -> X) f h ]
                  `[ finCase n m (\ _ -> X) f k ])
        )
    , \ h k -> mapHide \ (fn@(flr , frl , fq0 , fq1) , q) ->
        {!!} , {!!} , {!!}
    )
    where
      open FINSUM n n m m
      open FINSUMAUT n m
-}

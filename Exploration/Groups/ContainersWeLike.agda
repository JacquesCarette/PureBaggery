module ContainersWeLike where

open import Basics
open import ExtUni
open import Containers
open import Representables
open import RepresentablesWeLike
open import Fin
open import Algebras
open import ProductsForAlgebras
open import Actions
open import ActionsWeLike
open import Iso
open import Reasoning
open import Quotient

-- container with one shape
NaperianContainer : Representable -> ContainerDesc
NaperianContainer r .Shape = `One
NaperianContainer r .Store _ = r

-- Konstant, One and Identity containers
KC XC : U -> ContainerDesc
Shape (KC X) = X
Store (KC X) _ = AsFunFrom `Zero

XC = AsFunFrom - NaperianContainer

OneC IC : ContainerDesc
OneC = XC `Zero
IC   = XC `One

ListC : ContainerDesc
ListC .Shape = `Nat
ListC .Store n = AsFunFrom (Fin n)

-- products of containers
_*C_ : ContainerDesc -> ContainerDesc -> ContainerDesc
Shape ((Sh0 <| St0) *C (Sh1 <| St1)) = Sh0 `* Sh1
Wiggles (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = _
Positions (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = Positions (St0 sh0) `+ Positions (St1 sh1)
Grp (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = Grp (St0 sh0) *Group* Grp (St1 sh1)
Act (Store ((Sh0 <| St0) *C (Sh1 <| St1)) (sh0 , sh1)) = pairActsOnSum _ _ (Act (St0 sh0)) (Act (St1 sh1))

-- Move?
-- iso between product of types and product of containers

module _ (S T : ContainerDesc) where

  open REPRESENTABLE
  open Algebras.Group
  open ACTION.Action

  pairC : (X : U) -> (([ S ]C X `* [ T ]C X) <==> [ S *C T ]C X)
  fwd (pairC X) ((s , f) , (t , g))
    = (s , t)
    , UQlifting (FObjUQuot (Store S s) X ,- FObjUQuot (Store T t) X ,- []) (FObjUQuot (Store (S *C T) (s , t)) X)
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
    = (s , UQlifting (FObjUQuot (Store (S *C T) (s , t)) X ,- []) (FObjUQuot (Store S s) X)
           (\ h p -> h (`0 , p))
           ( (\ f0 f1 -> mapHide \ ((ws , wt) , q) -> ws , \ p0 p1 pq -> q (`0 , p0) (`0 , p1) (_ , pq))
           , _)
           h)
    , (t ,  UQlifting (FObjUQuot (Store (S *C T) (s , t)) X ,- []) (FObjUQuot (Store T t) X)
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


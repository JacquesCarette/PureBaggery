module Containers where

open import Basics
open import Quotient
open import ExtUni
open import Reasoning
open import Algebras
open import Actions
open import Iso
open import GroupsWeLike
open import ActionsWeLike
open import Numbers
open import Fin
open import Representables
open import RepresentablesWeLike

record ContainerDesc : Set where
  constructor _<|_
  field
    Shape : U
    Store : El Shape -> Representable

  [_]C : U -> U
  [_]C X = Shape `>< \ s -> let open REPRESENTABLE (Store s) in FObj X

  [_]CArr : (X Y : U) -> El (X `> Y) -> El ([_]C X `> [_]C Y)
  [_]CArr X Y f (s , px) = s , FArr X Y f px
    where open REPRESENTABLE (Store s)

  -- and [_]C is a Functor (all the hard work is in REPRESENTABLE)

  
open ContainerDesc public
open Representable public

module _ (C D : ContainerDesc) where
  private
    module C = ContainerDesc C
    module D = ContainerDesc D
  open REPRESENTABLE

  record _=CtrD=>_ : Set where
    field
      shape=> : El (C.Shape `> D.Shape)
      store<= : forall c -> D.Store (shape=> c) =Repr=> C.Store c

    -- induced action on containers
    [_]C=> : (X : U) -> El ([ C ]C X `> [ D ]C X)
    [_]C=> X (s , f) = shape=> s ,
      UQlifting (FObjUQuot (C.Store s) X ,- []) (FObjUQuot (D.Store (shape=> s)) X)
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
        open Algebras.Group
        open ACTION.Action
        open EQPRF X
        PC = Positions (C.Store s)
        PD = Positions (D.Store (shape=> s))
        GC = Grp (C.Store s)
        GD = Grp (D.Store (shape=> s))
        cact = act (Act (C.Store s))
        dact = act (Act (D.Store (shape=> s)))
        WD = Wiggles (D.Store (shape=> s))

    -- if you look at the expansion of this goal, you may lose the hope to which you are, in fact, entitled;
    -- the fact that nobody actually did any permutation makes this problem fall into the equational theory
    -- of Sigma and Pi, which Agda decides on the nose
    ctrMorNatural : (X Y : U)(f : El (X `> Y))(xc : El ([ C ]C X ))
      -> Pr (Oq ([ D ]C Y) ([_]C=> Y ([ C ]CArr X Y f xc)) ([ D ]CArr X Y f ([_]C=> X xc)))
    ctrMorNatural X Y f (s , px) = refl ([ D ]C Y) _

    IsCartesian : U
    IsCartesian = Shape C `-> \ c -> ExtendsToIso (groupAct=> (store<= c)) where
      open _=Action=>_
      open _=Repr=>_

    ExtendsToIso : U
    ExtendsToIso = HasInv (Shape C) (Shape D) shape=> `* IsCartesian

  record _<=CtrD=>_ : Set where
    field
      fwdmor : _=CtrD=>_
    open _=CtrD=>_ fwdmor
    field
      shapeInv : El (HasInv (Shape C) (Shape D) shape=>)
      isCartesian : El IsCartesian


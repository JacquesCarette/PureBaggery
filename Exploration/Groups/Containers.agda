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

  -- and it is natural (TODO)

-- HERE
-- and what are the cartesian morphisms?
-- and what are the full blown isos?

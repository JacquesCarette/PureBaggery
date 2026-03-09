{-# OPTIONS --erasure #-}

module Projtest where

data Nat : Set where ze : Nat ; su : Nat -> Nat

record _*_ (S T : Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T
open _*_

record One : Set where

Tup : Set -> Nat -> Set
Tup X ze = One
Tup X (su n) = X * Tup X n

record Rose : Set where
  inductive
  pattern
  field
    arity : Nat
    kids : Tup Rose arity
open Rose

data Ruse : Set where
  node : (n : Nat) -> Tup Ruse n -> Ruse

{-
leftSpineDepth : Rose -> Nat
leftSpinesDepth : (n : Nat) -> Tup Rose n -> Nat
leftSpineDepth r = leftSpinesDepth (r .arity) (r .kids)
leftSpinesDepth ze rs = ze
leftSpinesDepth (su n) rs = su (leftSpineDepth (rs .fst))
-}

leftSpineDepth' : Rose -> Nat
leftSpineDepth' record { arity = ze ; kids = rs } = ze
leftSpineDepth' record { arity = (su n) ; kids = r , rs } =
  su (leftSpineDepth' r)

data Fin : Nat -> Set where
  fz : {n : Nat} -> Fin (su n)
  fs : {n : Nat} -> Fin n -> Fin (su n)

_!_ : forall {X n} -> Tup X n -> Fin n -> X
xs ! fz = fst xs
xs ! fs i = xs .snd ! i

data Rec : Rose -> Set where
  node : forall n (ts : Tup Rose n)
      -> ((i : Fin n) -> Rec (ts ! i))
      -> Rec (record { arity = n ; kids = ts })

rec : (t : Rose) -> Rec t
rec record { arity = n ; kids = ts } = node n ts (sub ts)
  where
    sub : forall {n}(ts : Tup Rose n)(i : Fin n) -> Rec (ts ! i)
    sub (t , _) fz = rec t
    sub (_ , ts) (fs i) = sub ts i

-- why can't I dot node?
leftSpineDepth'' : (t : Rose) -> Rec t -> Nat
leftSpineDepth'' record { arity = ze ; kids = ts } (node _ _ f) = ze
leftSpineDepth'' record { arity = (su n) ; kids = ts } (node _ _ f) = su (leftSpineDepth'' _ (f fz))

data Ruc : Ruse -> Set where
  node : forall n (ts : Tup Ruse n)
      -> ((i : Fin n) -> Ruc (ts ! i))
      -> Ruc (node n ts)

ruc : (t : Ruse) -> Ruc t
ruc (node n ts) = node n ts (sub ts)
  where
    sub : forall {n}(ts : Tup Ruse n)(i : Fin n) -> Ruc (ts ! i)
    sub (t , _) fz = ruc t
    sub (_ , ts) (fs i) = sub ts i

-- ditto
leftSpineDepth''' : (t : Ruse) -> (@0 r : Ruc t) -> Nat
leftSpineDepth''' (node ze ts) (.node .ze .ts x) = ze
leftSpineDepth''' (node (su n) ts) (.node .(su n) .ts f) = su (leftSpineDepth''' _ (f fz))

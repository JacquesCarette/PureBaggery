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

leftSpineDepth : Rose -> Nat
leftSpinesDepth : (n : Nat) -> Tup Rose n -> Nat
leftSpineDepth r = leftSpinesDepth (r .arity) (r .kids)
leftSpinesDepth ze rs = ze
leftSpinesDepth (su n) rs = su (leftSpineDepth (rs .fst))

leftSpineDepth' : Rose -> Nat
leftSpineDepth' record { arity = ze ; kids = rs } = ze
leftSpineDepth' record { arity = (su n) ; kids = r , rs } =
  su (leftSpineDepth' r)


module Nary where

open import Basics
open import ExtUni

module _ (X : U) where

-- N-ary function type (in U)
N-ary : Nat -> U -> U
N-ary ze T = T
N-ary (su n) T = T `> N-ary n T

-- General N-ary "relation" Q -> Q -> ... -> Q -> S
N-ary-Rel : Nat -> Set -> Set -> Set
N-ary-Rel ze S _ = S
N-ary-Rel (su n) S Q = Q -> N-ary-Rel n S Q

-- same as above but in P
N-ary-RelNP : (S Q : U) (f : El S -> El Q) (n : Nat) -> (N-ary-Rel n P (El Q)) -> P
N-ary-RelNP S Q f ze NR = NR
N-ary-RelNP S Q f (su n) NR = S `-> \ s -> N-ary-RelNP S Q f n (NR (f s))

module _ (T : U)(R : El T -> El T -> P) where
  FunRelated : (n : Nat)(f g : El (N-ary n T)) -> P
  FunRelated ze f g = R f g
  FunRelated (su n) f g = T `-> \ t -> FunRelated n (f t) (g t)

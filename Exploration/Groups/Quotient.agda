module Quotient where


-- representation of quotienting by a relation
--   should be in a separate file and only a certain
--   interface exposed, so that no one can inspect the
--   implementation details. We'll just promise to be
--   good for now.

record Equiv (X : Set)(R : X -> X -> Set) : Set where
  field
    eqR : (x : X) -> R x x
    eqS : (x y : X) -> R x y -> R y x
    eqT : (x y z : X) -> R x y -> R y z -> R x z

record Quotient (X : Set)(R : X -> X -> Set)(Q : Equiv X R) : Set where
  constructor `[_]
  field
    rep : X

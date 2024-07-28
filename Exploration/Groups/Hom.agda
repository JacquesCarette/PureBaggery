module Hom where

open import Basics
open import ExtUni
open import Reasoning
open import Algebras

-- TODO: refactor hierarchically

module _ {X Y : U}(MX : Monoid X)(MY : Monoid Y) where
  private
    module MX = Monoid MX
    module MY = Monoid MY

  record HomMonoid : Set where
    field
      hom : El (X `> Y)

      homneu : Pr (Oq Y (hom MX.neu) MY.neu)
      hommul : (a b : El X) -> Pr (Oq Y (hom (MX.mul a b)) (MY.mul (hom a) (hom b)))

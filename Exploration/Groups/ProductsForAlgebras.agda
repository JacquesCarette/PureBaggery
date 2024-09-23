module ProductsForAlgebras where

open import Basics
open import ExtUni
open import Algebras

-- gives product structure for each of our algebraic notions

-- the Unit structures are trivial in ExtUni

oneSemiGroup : SemiGroup `One
oneSemiGroup = _

oneMonoid : Monoid `One
oneMonoid = _

oneGroup : Group `One
oneGroup = _


-- the Product structures go pointwise

module _ {X Y : U} where

  module _ (SX : SemiGroup X)(SY : SemiGroup Y) where

    open SemiGroup

    _*SemiGroup*_ : SemiGroup (X `* Y)
    mul _*SemiGroup*_ (x0 , y0) (x1 , y1) = mul SX x0 x1 , mul SY y0 y1
    mulmul- _*SemiGroup*_ (x0 , y0) (x1 , y1) (x2 , y2) = mulmul- SX x0 x1 x2 , mulmul- SY y0 y1 y2

  module _ (MX : Monoid X)(MY : Monoid Y) where

    open Monoid

    _*Monoid*_ : Monoid (X `* Y)
    _*Monoid*_ = monoid/ _ (semiGroup MX *SemiGroup* semiGroup MY) (record
      { neu = neu MX , neu MY
      ; mulneu- = \ (x , y) -> mulneu- MX x , mulneu- MY y
      ; mul-neu = \ (x , y) -> mul-neu MX x , mul-neu MY y
      })

  module _ (GX : Group X)(GY : Group Y) where

    open Group using (monoid; inv; mulinv-)

    _*Group*_ : Group (X `* Y)
    _*Group*_ = group/ _ (monoid GX *Monoid* monoid GY) (record
      { inv = inv GX >><< inv GY
      ; mulinv- = \ (x , y) -> mulinv- GX x , mulinv- GY y
      })


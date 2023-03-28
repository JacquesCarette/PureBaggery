{-# OPTIONS --without-K --safe #-}

-- SillyLists are Monoids
module SillyList.Monoid where

open import Algebra using (Monoid)
open import Data.Product using (_,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Bundles using (Setoid)

-- The definition of SillyList, map and fold
open import SillyList.Core
-- The definition of the equivalence relation to use
open import SillyList.Equivalence

private
  variable
    o e : Level

-- Silly lists are monoids
SLMonoid : Setoid o e → Monoid o (o ⊔ e)
SLMonoid S = record
  { Carrier = SillyList S
  ; _≈_ = _≈_
  ; _∙_ = _++_
  ; ε = []
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = ≈-equiv
        ; ∙-cong = ++-cong
        }
      ; assoc = λ x y z → assoc++ˡ {_} {_} {_} {x} {y} {z}
      }
    ; identity = (λ x → []++ˡ) , λ x → ++[]ˡ
    }
  }
-- Note how we end up using all the pieces of _≈_ somewhere,
-- directly or indirectly

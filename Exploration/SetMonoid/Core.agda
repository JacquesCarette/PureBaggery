{-# OPTIONS --without-K --safe #-}

-- Monoid based on propositional equality

module SetMonoid.Core where

open import Algebra using (RawMonoid; Op₂; IsMonoid)
open import Data.List using (List; foldr)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    o e : Level

-- We can't re-use Monoid from stdlib as it is polymorphic
-- over equality, and we don't want that. Here's a copy that
-- wires-in ≡
record Monoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  field
    Carrier  : Set c
    _∙_      : Op₂ Carrier
    ε        : Carrier
    isMonoid : IsMonoid _≡_ _∙_ ε

  open IsMonoid isMonoid public

  rawMonoid : RawMonoid _ _
  rawMonoid = record { _≈_ = _≡_; _∙_ = _∙_; ε = ε}

-- foldr over a _++_ turns into a _∙_
fold : (M : Monoid o e) → List (Monoid.Carrier M) → Monoid.Carrier M
fold M = foldr _∙_ ε where open Monoid M

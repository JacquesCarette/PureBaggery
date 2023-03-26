{-# OPTIONS --without-K --safe #-}

-- Define the data type itself, its basic kit (map, fold) and that's it!
module SillyList.Core where

open import Algebra using (Monoid)
-- open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
-- open import Data.Product using (_,_)
-- open import Function              using (id ; _∘_ )
open import Function.Equality as SF using (_⟨$⟩_; _⟶_) -- SF = Setoid Functions
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)
-- open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
-- open import Relation.Binary.Structures using (IsEquivalence)
-- open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

private
  variable
    o ℓ e : Level
    A B X Y Z : Setoid o e

∣_∣ : Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

infixr 4 _++_

-- Here's what could be called the "mathematician's list", as it is
-- the literal free monoid (over A)
data SillyList (A : Setoid o e) : Set o where
  [] : SillyList A
  Leaf : ∣ A ∣ → SillyList A
  _++_ : SillyList A → SillyList A → SillyList A

-- We can map on it; note the Setoid map (long _⟶_ )
SLmap : (f : A ⟶ B) → SillyList A → SillyList B
SLmap f [] = []
SLmap f (Leaf x) = Leaf (f ⟨$⟩ x)
SLmap f (l₀ ++ l₁) = SLmap f l₀ ++ SLmap f l₁

-- We can fold too. But note how this is intricately
-- tied to Monoid?
module _ (M : Monoid o e) where
  open Monoid M using (ε; _∙_) renaming (setoid to W)
  
  SLfold : SillyList W → ∣ W ∣
  SLfold [] = ε
  SLfold (Leaf x) = x
  SLfold (l₀ ++ l₁) = SLfold l₀ ∙ SLfold l₁


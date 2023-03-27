{-# OPTIONS --without-K --safe #-}

-- The equivalence relation we'll put on SillyList to make it into a List
module SillyList.Equivalence where

open import Algebra.Definitions using (Congruent₂)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)

open import SillyList.Core -- all of it

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level
    A B X Y Z : Setoid o e

infix  2 _≈_

-- Quotient SillyList.
-- This isn't the obvious quotient: it makes reflexivity, symmetry
-- provable instead of being baked in.
data _≈_ {A : Setoid o e} : SillyList A → SillyList A → Set (o ⊔ e) where
  -- it's a congruence
  Leaf : {a b : ∣ A ∣} → Setoid._≈_ A a b → Leaf a ≈ Leaf b
  []   : [] ≈ []
  _++_ : {l₁ l₂ s₁ s₂ : SillyList A} → l₁ ≈ s₁ → l₂ ≈ s₂ → l₁ ++ l₂ ≈ s₁ ++ s₂
  -- [] on left and right don't matter, on either side
  -- one could also assume ≈ is symmetric, but this leads to other problems.
  -- this way turns out more economical.
  []++ˡ : {l : SillyList A} → [] ++ l ≈ l
  ++[]ˡ : {l : SillyList A} → l ++ [] ≈ l
  []++ʳ : {l : SillyList A} → l ≈ [] ++ l
  ++[]ʳ : {l : SillyList A} → l ≈ l ++ []
  -- it is associative
  assoc++ˡ : {l₁ l₂ l₃ : SillyList A} → (l₁ ++ l₂) ++ l₃ ≈ l₁ ++ (l₂ ++ l₃)
  assoc++ʳ : {l₁ l₂ l₃ : SillyList A} → l₁ ++ (l₂ ++ l₃) ≈ (l₁ ++ l₂) ++ l₃
  -- and it is transitive too
  _⊚_ : {l₁ l₂ l₃ : SillyList A} → l₁ ≈ l₂ → l₂ ≈ l₃ → l₁ ≈ l₃ 

-- It really is an equivalence relation:
private
  module _ {A : Setoid o e} where
    open Setoid A hiding (_≈_)
    -- This is tedious, but rightly so: we're asking for something odd.
    -- Just because it workds doesn't mean it's a good idea!
    ≈-refl : Reflexive (_≈_ {A = A})
    ≈-refl {[]} = []
    ≈-refl {Leaf x} = Leaf refl
    ≈-refl {l₀ ++ l₁} = ≈-refl ++ ≈-refl

    ≈-sym : Symmetric (_≈_ {A = A})
    ≈-sym (Leaf x) = Leaf (sym x)
    ≈-sym [] = []
    ≈-sym (eq₀ ++ eq₁) = ≈-sym eq₀ ++ ≈-sym eq₁
    ≈-sym []++ˡ = []++ʳ
    ≈-sym []++ʳ = []++ˡ
    ≈-sym ++[]ˡ = ++[]ʳ
    ≈-sym ++[]ʳ = ++[]ˡ
    ≈-sym assoc++ˡ = assoc++ʳ
    ≈-sym assoc++ʳ = assoc++ˡ
    ≈-sym (eq₀ ⊚ eq₁) = ≈-sym eq₁ ⊚ ≈-sym eq₀

++-cong : {A : Setoid o e} → Congruent₂ (_≈_ {A = A}) _++_
++-cong = _++_
    
≈-equiv : {A : Setoid o e} → IsEquivalence (_≈_ {A = A})
≈-equiv = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = _⊚_
  }

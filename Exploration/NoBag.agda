{-# OPTIONS --without-K --safe #-}

-- Some impossibility results

-- One thing that might need to end up in here is that
-- containers look like Σ types, but while Σ is associative,
-- Container is not. That's because the natural morphisms are
-- different.
module NoBag where

open import Data.Bool using (Bool; true; false) -- for examples
open import Data.Container.Core
open import Data.Container.Morphism using (id; _∘_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Nat.Binary.Base using (ℕᵇ; zero; 2[1+_]; 1+[2_]) -- for examples
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Level using (Level; _⊔_; 0ℓ)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; _≢_; subst)
open import Relation.Nullary using (¬_)

-- removing a point from a type
_\\_ : {a : Level} → (A : Set a) → A → Set a
A \\ a = Σ A (λ x → ¬ (x ≡ a))

infix 5 _⇒Eq_ _≃_

-- Change the morphisms?
-- Conor: position part = "source shapes to target container of source positions"
--  Given such a thing, cd, say. (s, k) maps to D.map k (cd s).
--  So (s : C.Shape) → ⟦ D ⟧ (C.Position s) ?

-- container morphisms are equivalent when they are extensionally so
record _⇒Eq_ {s₁ s₂ p₁ p₂ : Level}
  {C : Container s₁ p₁} {D : Container s₂ p₂}
  (M N : C ⇒ D) : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  private
    module C = Container C
    module D = Container D
    module M = _⇒_ M
    module N = _⇒_ N
  field
    shape≡ : ∀ {s : C.Shape} → M.shape s ≡ N.shape s
    position≡ : ∀ {s : C.Shape} {p : Position D (M.shape s)} →
      M.position p ≡ N.position (subst D.Position (shape≡ {s}) p )

-- container equivalence
record _≃_ {s₁ s₂ p₁ p₂ : Level} (C : Container s₁ p₁) (D : Container s₂ p₂)
  : Set (s₁ ⊔ s₂ ⊔ p₁ ⊔ p₂) where
  field
    fwd : C ⇒ D
    bwd : D ⇒ C
    fwd∘bwd~id : (fwd ∘ bwd) ⇒Eq (id D)
    bwd∘fwd~id : (bwd ∘ fwd) ⇒Eq (id C)

-- A container is not trivial if it has a shape with an inhabited position
nonTrivial : {s p : Level} → Container s p → Set _
nonTrivial C = Σ (Container.Shape C)
               (λ s → Σ (Container.Position C s × Container.Position C s)
                λ {(p , q) → p ≢ q})

module _ {s p : Level} where
  diff : Container s p → Container (s ⊔ p) p
  diff (S ▷ P) = Σ S P ▷ (λ { (s , p) → P s \\ p})
  -- diff (S ▷ P) = S ▷ λ s → Σ (P s) (λ p → P s \\ p)

  zeroC : Container s p
  zeroC = ⊥ ▷ λ {()}

  zeroC' : (A : Set p) → Container s p
  zeroC' A = ⊥ ▷ λ _ → A

  zero-is-soln : zeroC ≃ diff zeroC
  zero-is-soln = record
    { fwd = (λ { ()}) ▷ λ { {()} _}
    ; bwd = (λ { ()}) ▷ λ { {()} _}
    ; fwd∘bwd~id = record { shape≡ = λ { {()} } ; position≡ = λ { {()} } }
    ; bwd∘fwd~id = record { shape≡ = λ { {()} } ; position≡ = λ { {()} } }
    }

-- Brutalist approach:
-- - assume Position is Fin
-- - look at families of shapes that all end up with the same size
-- - then need a family (Nat -> Set) that solves S(n+1) × Fin n ≃ S(n).
--    (obvious problem with that is that things get larger as n goes DOWN)


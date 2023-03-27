{-# OPTIONS --without-K --safe #-}

-- Homomorphisms of Setoid-based monoids

module SetoidMonoid.Hom where

open import Algebra using (Monoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Function              using (id ; _∘_ )
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_) -- SF = Setoid Functions
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level
    A B X Y Z : Setoid o e

-- We have a clear definition of monoid homomorphism:
record Hom (M₁ : Monoid o₁ e₁) (M₂ : Monoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where
  constructor hom
  field
     map : Monoid.Carrier M₁ → Monoid.Carrier M₂
     isHom : IsMonoidHomomorphism (Monoid.rawMonoid M₁) (Monoid.rawMonoid M₂) map

  open IsMonoidHomomorphism isHom public
  open IsRelHomomorphism isRelHomomorphism public

  -- the underlying setoid map from a monoid homomorphism
  setoid⟶ : Monoid.setoid M₁ ⟶ Monoid.setoid M₂
  setoid⟶ = record { _⟨$⟩_ = map; cong = cong}

-- For re-use:
-- Identity homomorphism
idH : {M : Monoid o e} → Hom M M
idH {M = M} = hom id (record
  { isMagmaHomomorphism = record
    { isRelHomomorphism = record { cong = id }
    ; homo = λ _ _ → refl
    }
  ; ε-homo = refl
  })
  where open Monoid M using (refl)

-- Homomorphism composition.
-- First, some kit to make later things less ugly
module _ {M : Monoid o₁ e₁} {N : Monoid o₂ e₂} where
  open IsMonoidHomomorphism
  open IsMagmaHomomorphism
  open IsRelHomomorphism
  private
    module M = Monoid M
    module N = Monoid N

  -- constructor for homomorphism
  mkIsHom : (f : M.Carrier → N.Carrier) →
    ({x y : M.Carrier} → x M.≈ y → f x N.≈ f y) →
    ((x y : M.Carrier) → f (x M.∙ y) N.≈ f x N.∙ f y) →
    (f M.ε N.≈ N.ε) →
    IsMonoidHomomorphism M.rawMonoid N.rawMonoid f
  cong (isRelHomomorphism (isMagmaHomomorphism (mkIsHom f c _ _))) = c
  homo (isMagmaHomomorphism (mkIsHom f _ h _)) = h
  ε-homo (mkIsHom _ _ _ pres-ε) = pres-ε

_∘H_ : {M₁ : Monoid o₁ e₁} {M₂ : Monoid o₂ e₂} {M₃ : Monoid o₃ e₃} →
  Hom M₂ M₃ → Hom M₁ M₂ → Hom M₁ M₃
_∘H_ {M₁ = M₁} {M₃ = M₃} f g =
    let h = F.map ∘ G.map in
    hom h (mkIsHom {M = M₁} {M₃} h (F.cong ∘ G.cong)
                   (λ x y → trans (F.cong (G.homo x y)) (F.homo (G.map x) (G.map y)))
                   (trans (F.cong G.ε-homo)  F.ε-homo))
  where
    module F = Hom f
    module G = Hom g
    open Monoid M₃ using (trans)


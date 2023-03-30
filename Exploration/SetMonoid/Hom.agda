{-# OPTIONS --without-K --safe #-}

module SetMonoid.Hom where

open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Function              using (id ; _∘_ )
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)

open import SetMonoid.Core

private
  variable
    o o₁ o₂ o₃ e e₁ e₂ e₃ : Level
    A B X Y Z : Set o

-- Need to define monoid homomorphism.
-- This is essentially identical to SetoidMonoid.Hom...
record Hom (M₁ : Monoid o₁ e₁) (M₂ : Monoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where
  constructor hom
  field
     map : Monoid.Carrier M₁ → Monoid.Carrier M₂
     isHom : IsMonoidHomomorphism (Monoid.rawMonoid M₁) (Monoid.rawMonoid M₂) map

  open IsMonoidHomomorphism isHom public
  open IsRelHomomorphism isRelHomomorphism public

-- Identity homomorphism
idH : {M : Monoid o e} → Hom M M
idH {M = M} = hom id (record
                     { isMagmaHomomorphism = record
                       { isRelHomomorphism = record { cong = id }
                       ; homo = λ _ _ → ≡.refl
                       }
                     ; ε-homo = ≡.refl
                     })

-- Homomorphism composition.
-- First, some kit to make later things less ugly
module H {M : Monoid o₁ e₁} {N : Monoid o₂ e₂} where
  open IsMonoidHomomorphism
  open IsMagmaHomomorphism
  open IsRelHomomorphism
  private
    module M = Monoid M
    module N = Monoid N

  -- constructor for homomorphism
  mkIsHom : (f : M.Carrier → N.Carrier) →
    ({x y : M.Carrier} → x ≡ y → f x ≡ f y) →
    ((x y : M.Carrier) → f (x M.∙ y) ≡ f x N.∙ f y) →
    (f M.ε ≡ N.ε) →
    IsMonoidHomomorphism M.rawMonoid N.rawMonoid f
  cong (isRelHomomorphism (isMagmaHomomorphism (mkIsHom f c _ _))) = c
  homo (isMagmaHomomorphism (mkIsHom f _ h _)) = h
  ε-homo (mkIsHom _ _ _ pres-ε) = pres-ε

_∘H_ : {M₁ : Monoid o₁ e₁} {M₂ : Monoid o₂ e₂} {M₃ : Monoid o₃ e₃} →
  Hom M₂ M₃ → Hom M₁ M₂ → Hom M₁ M₃
_∘H_ {M₁ = M₁} {M₃ = M₃} f g =
    let h = F.map ∘ G.map in
    hom h (H.mkIsHom {M = M₁} {M₃} h (F.cong ∘ G.cong)
                     (λ x y → ≡.trans (F.cong (G.homo x y)) (F.homo (G.map x) (G.map y)))
                     (≡.trans (F.cong G.ε-homo)  F.ε-homo))
  where
    module F = Hom f
    module G = Hom g

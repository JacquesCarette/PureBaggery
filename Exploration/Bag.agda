{-# OPTIONS --without-K --safe #-}

-- A Bag will be represented as a list of contents quotiented by permutations
module Bag where

open import Algebra using (Monoid; CommutativeMonoid; Congruent₂)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Data.List as List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ)
open import Data.Product using (_,_)
open import Function              using (id ; _∘_ )
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Adjoint using (Adjoint)
open import Categories.NaturalTransformation using (ntHelper)

open import PermJ
open import SillyList using (Hom; hom; HomId; module H; _H∘_) -- split!

private
  variable
    o o₁ o₂ o₃ e e₁ e₂ e₃ : Level
    A B X Y Z : Set o

-- it really is an equivalence relation:
≈-equiv : {X : Set o} → IsEquivalence (_≈_ {X = X})
≈-equiv = record { refl = idPerm ; sym = sym ; trans = trans }

-- lists quotiented by ≈ are commutative monoids
--   Is using resp-≡ a good idea? It gives the right result *eventually*
comm-monoid : Set o → CommutativeMonoid o o
comm-monoid S = record
  { Carrier = List S
  ; _≈_ = _≈_
  ; _∙_ = _++_
  ; ε = []
  ; isCommutativeMonoid =  record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≈-equiv
          ; ∙-cong = ++-cong
          }
        ; assoc = λ x y z → resp-≡ (++-assoc x y z)
        }
      ; identity = (λ x → resp-≡ (++-identityˡ x)) , (λ x → resp-≡ (++-identityʳ x))
      }
    ; comm = ≈-commutative
    }
  }

-- The collection of commutative monoids forms a Category
-- (Duplicate code, factor out)
CMonoidCat : (o e : Level) → Category (suc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
CMonoidCat o e = record
  { Obj = CommutativeMonoid o e
  ; _⇒_ = λ m n → Hom (monoid m) (monoid n)
  ; _≈_ = λ {_} {B} f g → (∀ x → CommutativeMonoid._≈_ B (map f x) (map g x))
  ; id = HomId
  ; _∘_ = _H∘_
  ; assoc = λ { {D = D} _ → refl D}
  ; sym-assoc = λ { {D = D} _ → refl D}
  ; identityˡ = λ {_} {B} _ → refl B
  ; identityʳ = λ {_} {B} _ → refl B
  ; identity² = λ {A} _ → refl A
  ; equiv = λ {A} {B} → record
    { refl = λ _ → refl B
    ; sym = λ Fx≈Fy x → CommutativeMonoid.sym B (Fx≈Fy x)
    ; trans = λ Ix≈Jx Jx≈Hx x → CommutativeMonoid.trans B (Ix≈Jx x) (Jx≈Hx x)
    }
  ; ∘-resp-≈ = λ {_} {_} {C} {f} {h} {g} {i} fx≈hx gx≈ix x →
                CommutativeMonoid.trans C (cong f (gx≈ix x)) (fx≈hx (Hom.map i x))
  }
  where
    open Hom using (map; cong)
    open CommutativeMonoid using (refl; monoid)

-- There is an obvious forgetful Functor. Best to call it Underlying.
-- (also duplicate)
Underlying : (o e : Level) → Functor (CMonoidCat o e) (Setoids o e)
Underlying o e = record
  { F₀             =   CommutativeMonoid.setoid
  ; F₁             =   ?
  ; identity       =   {!!} -- ≡.refl
  ; homomorphism   =   {!!} -- ≡.refl
  ; F-resp-≈       =   λ f≡g {x} → {!!} -- f≡g x
  }
{-
-- Lists induce a (Free) functor from Sets to the category of Monoids
Free : (o : Level) → Functor (Sets o) (MonoidCat o o)
Free o = record
  { F₀ = list-monoid
  ; F₁ = λ {A = M} {N} f → hom (map f)
                               (H.mkIsHom {M = list-monoid M} {list-monoid N} (map f)
                                          (λ { ≡.refl → ≡.refl })
                                          (map-++-commute f)
                                          ≡.refl)
  ; identity = map-id
  ; homomorphism = map-compose
  ; F-resp-≈ = λ f≈g x → map-cong (λ y → f≈g {y}) x
  }

-- Note how the Adjoint here is not fully level polymorphic either.
-- Here it's because we're using ≡ .
--
-- Roughly then:
-- unit is singleton
--   naturality of unit says map onto singleton is the same as singleton-apply
-- counit is fold
--   naturality of counit says fold-map is map-fold (at the right types)
-- zig says that creating a list-list (of singletons) and then folding
--   (for the Monoid) will just extract the original list
-- zag says... right-unit

ListLeft : (o : Level) → Adjoint (Free o) (Underlying o o)
ListLeft o = record
  { unit = ntHelper (record { η = λ _ → [_] ; commute = λ _ → ≡.refl })
  ; counit = ntHelper (record { η = fold ; commute = foldr-natural })
  ; zig = foldr-map-singleton
  ; zag = λ {M} {x} → Monoid.identityʳ M x
  }
  where
    -- kit for co-unit
    FU : Functor (MonoidCat o o) (MonoidCat o o)
    FU = Free o ∘F Underlying o o
    module FU = Functor FU
    fold : (X : Monoid o o) → Hom (FU.₀ X) X
    fold X = hom (foldr _∙_ ε)
                 (H.mkIsHom {M = list-monoid Carrier} {X} (foldr _∙_ ε)
                   (λ { ≡.refl → ≡.refl }) -- respects ≡
                   (foldr-++-∙ {M = X})
                   ≡.refl)                 -- respects ε
      where open Monoid X
-}

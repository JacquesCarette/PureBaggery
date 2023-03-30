{-# OPTIONS --without-K --safe #-}

-- Where SillyList was about the mathematician's list, as the "obvious" quotient,
-- here we look at the computer scientists' list. We use the normal form, which
-- needs no quotienting at all. So much so that we can get rid of Setoids altogether
-- and work with propositional equality!!
module FreeMonoid where

open import Algebra using (RawMonoid; Op₂; IsMonoid)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Data.List as List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Properties
open import Data.Product using (_,_)
open import Function              using (id ; _∘_ )
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_; cong₂)
open import Relation.Binary.PropositionalEquality using (isEquivalence; module ≡-Reasoning)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Sets using (Sets)
open import Categories.Adjoint using (Adjoint)
open import Categories.NaturalTransformation using (ntHelper)

open import SetMonoid.Core
open import SetMonoid.Hom

private
  variable
    o o₁ o₂ o₃ e e₁ e₂ e₃ : Level
    A B X Y Z : Set o

-- lists are monoids; no level polymorphism because of ≡
list-monoid : Set o → Monoid o o
list-monoid S = record
  { Carrier = List S
  ; _∙_ = _++_
  ; ε = []
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence
        ; ∙-cong = cong₂ _++_
        }
      ; assoc = ++-assoc
      }
    ; identity = ++-identity
    }
  }
-- We also have that fold has a number of properties over a Monoid.

-- foldr over a _++_ turns into a _∙_
module _ {M : Monoid o e} where
  open Monoid M renaming (Carrier to W)

  -- There might be an equational way to do this, but let's brute force it
  -- This relies on two properties of Monoid (so would hold or left unital magmas)
  foldr-++-∙ : (x y : List W) → fold M (x ++ y) ≡ fold M x ∙ fold M y
  foldr-++-∙ [] y = sym (identityˡ _)
  foldr-++-∙ (x ∷ xs) y = ≡.trans (≡.cong (x ∙_) (foldr-++-∙ xs y)) (sym (assoc _ _ _))

-- foldr over map-singleton does nothing. Maybe should be in stdlib?
foldr-map-singleton : {A : Set o} (l : List A) → foldr _++_ [] (List.map [_] l) ≡ l
foldr-map-singleton [] = ≡.refl
foldr-map-singleton (x ∷ l) = ≡.cong (x ∷_) (foldr-map-singleton l)

-- foldr is natural, i.e. foldr ∘ map is the same as Hom.mmap ∘ foldr
module _ {M N : Monoid o e} (f : Hom M N) where
  private
    module M = Monoid M
    module N = Monoid N
    foldrM = foldr M._∙_ M.ε
    foldrN = foldr N._∙_ N.ε
  open Hom f

  -- naturality follows from f being a monoid homomorphism:
  foldr-natural : (l : List M.Carrier) → foldrN (List.map map l) ≡ map (foldrM l)
  foldr-natural [] = ≡.sym ε-homo
  foldr-natural (x ∷ xs) = begin
    map x N.∙ foldrN (List.map map xs) ≡⟨ ≡.cong (map x N.∙_) (foldr-natural xs) ⟩
    map x N.∙ map (foldrM xs)          ≡˘⟨ homo x (foldrM xs) ⟩
    map (x M.∙ foldrM xs)              ∎
    where open ≡-Reasoning
  
-- The collection of monoids form a Category
MonoidCat : (o e : Level) → Category (suc (o ⊔ e)) (o ⊔ e) o
MonoidCat o e = record
  { Obj = Monoid o e
  ; _⇒_ = Hom
  ; _≈_ = λ f g → (∀ x → map f x ≡ map g x)
  ; id = idH
  ; _∘_ = _∘H_
  ; assoc = λ _ → ≡.refl
  ; sym-assoc = λ _ → ≡.refl
  ; identityˡ = λ _ → ≡.refl
  ; identityʳ = λ _ → ≡.refl
  ; identity² = λ _ → ≡.refl
  ; equiv = record
    { refl = λ _ → ≡.refl
    ; sym = λ Fx≈Fy x → ≡.sym (Fx≈Fy x)
    ; trans = λ Ix≈Jx Jx≈Hx x → ≡.trans (Ix≈Jx x) (Jx≈Hx x)
    }
  ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} fx≈hx gx≈ix x →
                ≡.trans (cong f (gx≈ix x)) (fx≈hx (map i x))
  }
  where
    open Hom using (map; cong)

-- There is an obvious forgetful Functor. Best to call it Underlying.
-- Note how we 'lose' the Level e
Underlying : (o e : Level) → Functor (MonoidCat o e) (Sets o)
Underlying o e = record
  { F₀             =   Monoid.Carrier
  ; F₁             =   Hom.map
  ; identity       =   ≡.refl
  ; homomorphism   =   ≡.refl
  ; F-resp-≈       =   λ f≡g {x} → f≡g x
  }

-- Lists induce a (Free) functor from Sets to the category of Monoids
Free : (o : Level) → Functor (Sets o) (MonoidCat o o)
Free o = record
  { F₀ = list-monoid
  ; F₁ = λ {A = M} {N} f → hom (List.map f)
                               (H.mkIsHom {M = list-monoid M} {list-monoid N} (List.map f)
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
  ; counit = ntHelper (record { η = fold′ ; commute = foldr-natural })
  ; zig = foldr-map-singleton
  ; zag = λ {M} {x} → Monoid.identityʳ M x
  }
  where
    -- kit for co-unit
    FU : Functor (MonoidCat o o) (MonoidCat o o)
    FU = Free o ∘F Underlying o o
    module FU = Functor FU
    fold′ : (X : Monoid o o) → Hom (FU.₀ X) X
    fold′ X = hom (foldr _∙_ ε)
                  (H.mkIsHom {M = list-monoid Carrier} {X} (foldr _∙_ ε)
                    (λ { ≡.refl → ≡.refl }) -- respects ≡
                    (foldr-++-∙ {M = X})
                    ≡.refl)                 -- respects ε
      where open Monoid X

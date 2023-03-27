{-# OPTIONS --without-K --safe #-}

module SillyList where

open import Algebra using (Monoid; Congruent₂)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Data.Product using (_,_)
open import Function              using (id ; _∘_ )
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_) -- SF = Setoid Functions
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Adjoint using (Adjoint)
open import Categories.NaturalTransformation using (ntHelper)

-- The definition of SillyList, map and fold
open import SillyList.Core public
-- The definition of the equivalence relation to use
open import SillyList.Equivalence public
-- Some useful properties of SLmap
open import SillyList.Properties public
-- We need to talk about homomorphisms of Setoid-based monoids
open import SetoidMonoid.Hom

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level
    A B X Y Z : Setoid o e

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
-- Note how we end up using all the pieces of _≈_ somewhere.

-- The collection of monoids form a Category
MonoidCat : (o e : Level) → Category (suc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
MonoidCat o e = record
  { Obj = Monoid o e
  ; _⇒_ = Hom
  ; _≈_ = λ {_} {B} f g → (∀ x → Monoid._≈_ B (map f x) (map g x))
  ; id = idH
  ; _∘_ = _∘H_
  ; assoc = λ { {D = D} _ → refl D}
  ; sym-assoc = λ { {D = D} _ → refl D}
  ; identityˡ = λ {_} {B} _ → refl B
  ; identityʳ = λ {_} {B} _ → refl B
  ; identity² = λ {A} _ → refl A
  ; equiv = λ {A} {B} → record
    { refl = λ _ → refl B
    ; sym = λ Fx≈Fy x → sym B (Fx≈Fy x)
    ; trans = λ Ix≈Jx Jx≈Hx x → trans B (Ix≈Jx x) (Jx≈Hx x)
    }
  ; ∘-resp-≈ = λ {_} {_} {C} {f} {h} {g} {i} fx≈hx gx≈ix x →
                trans C (cong f (gx≈ix x)) (fx≈hx (map i x))
  }
  where
    open Hom using (map; cong)
    open Monoid using (refl; sym; trans)

-- There is an obvious forgetful Functor. Best to call it Underlying.
Underlying : (o e : Level) → Functor (MonoidCat o e) (Setoids o e)
Underlying o e = record
  { F₀             =   Monoid.setoid
  ; F₁             =   Hom.setoid⟶
  ; identity       =   id
  ; homomorphism   =   λ {_} {_} {Z} {f} {g} x≈y → Hom.cong g (Hom.cong f x≈y) 
  ; F-resp-≈       =   λ {_} {B} {f} {g} f≈g {x} {y} x≈y → Monoid.trans B (f≈g x) (Hom.cong g x≈y)
  }

-- Lists induce a (Free) functor from (Carrier) Setoids to the category of Monoids
Free : (o e : Level) → Functor (Setoids o e) (MonoidCat o (o ⊔ e))
Free o e = record
  { F₀ = SLMonoid
  ; F₁ = λ {A} {B} f →
           let M = SLMonoid A
               N = SLMonoid B in
           hom (SLmap f)
               (mkIsHom {M = M} {N} (SLmap f)
                   (SLmap-cong f)
                   (λ _ _ → Monoid.refl N)
                   [])
  ; identity = SLmap-id
  ; homomorphism = SLmap-hom
  ; F-resp-≈ = SLmap-S-cong
  }

-- Note how the Adjoint here is not fully level polymorphic!
-- The problem is that the Free Functor mixes in objects into the
-- witnesses of ≈ and so we 'lose' a degree of freedom.

-- Roughly then:
-- unit is singleton (aka Leaf)
--   naturality of unit says map onto singleton is the same as singleton-apply
-- counit is fold
--   naturality of counit says fold-map is map-fold (at the right types)
-- zig says that creating a list-list (of singletons) and then folding
--   (for the SLMonoid) will just extract the original list
-- zag says... nothing of interest! It's just true by definition.


ListLeft : (o : Level) → Adjoint (Free o o) (Underlying o o)
ListLeft o = record
  { unit = ntHelper (record { η = singleton ; commute = λ f x≈y → Leaf (Π.cong f x≈y) })
  ; counit = ntHelper (record { η = fold ; commute = SLfold-natural })
  ; zig = zig
  ; zag = id
  }
  where
    -- kit for unit
    UF : Functor (Setoids o o) (Setoids o o)
    UF = Underlying o o ∘F Free o o
    module UF = Functor UF
    -- singleton
    singleton : (X : Setoid o o) → X ⟶ (UF.₀ X)
    _⟨$⟩_ (singleton X) = Leaf
    Π.cong (singleton X) = Leaf

    -- kit for co-unit
    FU : Functor (MonoidCat o o) (MonoidCat o o)
    FU = Free o o ∘F Underlying o o
    module FU = Functor FU
    fold : (X : Monoid o o) → Hom (FU.₀ X) X
    fold X = hom (SLfold X)
                 (mkIsHom {M = SLMonoid (Monoid.setoid X)} {X} (SLfold X)
                          SLfold-cong
                          (λ _ _ → Monoid.refl X) -- ∙-homo is free
                          (Monoid.refl X))        -- ε-pres is free
    zig : {S : Setoid o o} (x : SillyList S) →
      SLfold (SLMonoid S) (SLmap (singleton S) x) ≈ x
    zig []       = []
    zig {S = S} (Leaf x) = Leaf (Setoid.refl S)
    zig (x ++ y) = zig x ++ zig y

{-# OPTIONS --without-K #-}

-- A Bag will be represented as a list of contents quotiented by permutations
module Bag where

open import Algebra using (Monoid; CommutativeMonoid; Congruent₂)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Data.List as List using (List; []; _∷_; _++_; [_]; foldr)
open import Data.List.Properties using (++-assoc; ++-identityˡ; ++-identityʳ;
  map-++-commute; map-id; map-compose)
open import Data.Product using (_,_)
open import Function              using (id ; _∘_ )
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_)
open import Level using (Level; suc; _⊔_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)
import Relation.Binary.PropositionalEquality.Core as PE
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
    A B X Y Z : Setoid o e

∣_∣ : Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

-- it really is an equivalence relation:
≈-equiv : {X : Set o} → IsEquivalence (_≈_ {X = X})
≈-equiv = record { refl = idPerm ; sym = sym ; trans = trans }

-- lists quotiented by ≈ are commutative monoids
--   Is using resp-≡ a good idea? It gives the right result *eventually*
--   Note how we never ever looks at S's equivalence!! 
comm-monoid : Setoid o e → CommutativeMonoid o o
comm-monoid S = record
  { Carrier = List (Setoid.Carrier S)
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

-- the underlying setoid map from a commutative monoid homomorphism
setoid⟶ : {M N : CommutativeMonoid o e} →
  Hom (CommutativeMonoid.monoid M) (CommutativeMonoid.monoid N) →
  CommutativeMonoid.setoid M ⟶ CommutativeMonoid.setoid N
setoid⟶ h = record { _⟨$⟩_ = Hom.map h; cong = Hom.cong h }

-- There is an obvious forgetful Functor. Best to call it Underlying.
-- (also duplicate)
Underlying : (o e : Level) → Functor (CMonoidCat o e) (Setoids o e)
Underlying o e = record
  { F₀             =   CommutativeMonoid.setoid
  ; F₁             =   λ {M} {N} h → setoid⟶ {M = M} {N} h
  ; identity       =   id
  ; homomorphism   =   λ {_} {_} {_} {f} {g} x≈y → Hom.cong g (Hom.cong f x≈y)
  ; F-resp-≈       =   λ {_} {B} {f} {g} f≈g {x} {y} x≈y →
                         CommutativeMonoid.trans B (f≈g x) (Hom.cong g x≈y)
  }

-- let's see if this is the only blocker
postulate
  map-resp-≈ : {f g : A ⟶ B} →
      ({x y : ∣ A ∣} → Setoid._≈_ A x y → Setoid._≈_ B (f ⟨$⟩ x) (g ⟨$⟩ y)) →
      {x : List ∣ A ∣} → List.map (f ⟨$⟩_) x ≈ List.map (g ⟨$⟩_) x

-- Properly quotiented Lists induce a (Free) functor from (Carrier) Setoids
-- to the category of Commutative Monoids
Free : (o e : Level) → Functor (Setoids o e) (CMonoidCat o o)
Free o e = record
  { F₀ = comm-monoid
  ; F₁ = λ {A} {B} f →
           let M = comm-monoid A
               N = comm-monoid B
               F = λ x → f ⟨$⟩ x in
           hom (List.map F)
               (H.mkIsHom {M = monoid M} {monoid N} (List.map F)
                   (map-perm F)
                   (λ xs ys → trans (resp-≡ (map-++-commute F xs ys))
                                    (++-cong {x = List.map F xs} idPerm idPerm))
                   [])
  ; identity = λ _ → resp-≡ (map-id _) 
  ; homomorphism = λ x → resp-≡ (map-compose x)
    ; F-resp-≈ = λ {_} {_} {f} {g} f≈g x → map-resp-≈ {f = f} {g} f≈g {x}
  }
  where open CommutativeMonoid using (refl; monoid)
ListLeft : (o : Level) → Adjoint (Free o o) (Underlying o o)
ListLeft o = record
  { unit = ntHelper (record { η = λ X → record { _⟨$⟩_ = [_] ; cong = {!!} }
                            ; commute = {!!}
                            })
  ; counit = ntHelper (record { η = {!!} ; commute = {!!} })
  ; zig = {!!}
  ; zag = {!!}
  }


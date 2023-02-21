{-# OPTIONS --without-K --safe #-}

module SillyList where

open import Algebra using (Monoid; Congruent₂)
open import Algebra.Morphism.Structures using (IsMonoidHomomorphism; IsMagmaHomomorphism)
open import Data.Product using (_,_)
open import Function              using (id ; _∘_ ; const)
open import Function.Equality using (Π; _⟨$⟩_; _⟶_)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Morphism.Structures using (IsRelHomomorphism)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Adjoint using (Adjoint)

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level

∣_∣ : Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

infixr 4 _++_
infix  2 _≈_

-- Here's what could be called the "mathematician's list", as it is
-- the literal free monoid (over A)
data SillyList (A : Setoid o e) : Set o where
  [] : SillyList A
  Leaf : ∣ A ∣ → SillyList A
  _++_ : SillyList A → SillyList A → SillyList A

-- We can map on it
SLmap : {A : Setoid o₁ e₁} {B : Setoid o₂ e₂} (f : A ⟶ B) → SillyList A → SillyList B
SLmap f [] = []
SLmap f (Leaf x) = Leaf (f ⟨$⟩ x)
SLmap f (l₀ ++ l₁) = SLmap f l₀ ++ SLmap f l₁

-- Since that's quotiented, exhibit that as well:
data _≈_ {A : Setoid o e} : SillyList A → SillyList A → Set (o ⊔ e) where
  -- it's a congruence
  Leaf : {a b : ∣ A ∣} → Setoid._≈_ A a b → Leaf a ≈ Leaf b
  []   : [] ≈ []
  _++_ : {l₁ l₂ s₁ s₂ : SillyList A} → l₁ ≈ s₁ → l₂ ≈ s₂ → l₁ ++ l₂ ≈ s₁ ++ s₂
  -- [] on left and right don't matter, on either side
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

    ++-cong : Congruent₂ (_≈_ {A = A}) _++_
    ++-cong = _++_
    
≈-equiv : {A : Setoid o e} → IsEquivalence (_≈_ {A = A})
≈-equiv = record
  { refl = ≈-refl
  ; sym = ≈-sym
  ; trans = _⊚_
  }

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

-- We have a clear definition of monoid homomorphism:
record Hom (M₁ : Monoid o₁ e₁) (M₂ : Monoid o₂ e₂) : Set (o₁ ⊔ o₂ ⊔ e₁ ⊔ e₂) where
  constructor hom
  field
     map : Monoid.Carrier M₁ → Monoid.Carrier M₂
     isHom : IsMonoidHomomorphism (Monoid.rawMonoid M₁) (Monoid.rawMonoid M₂) map

  open IsMonoidHomomorphism isHom public
  open IsRelHomomorphism isRelHomomorphism public

-- For re-use
HomId : {M : Monoid o e} → Hom M M
HomId {M = M} = hom id (record { isMagmaHomomorphism = record
                         { isRelHomomorphism = record { cong = id }
                         ; homo = λ _ _ → refl }
                       ; ε-homo = refl })
  where open Monoid M using (refl)

_H∘_ : {M₁ : Monoid o₁ e₁} {M₂ : Monoid o₂ e₂} {M₃ : Monoid o₃ e₃} →
  Hom M₂ M₃ → Hom M₁ M₂ → Hom M₁ M₃
_H∘_ {M₃ = M} f g = hom (F.map ∘ G.map) (record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record
        { cong = F.cong ∘ G.cong }
      ; homo = λ x y → trans (F.cong (G.homo x y)) (F.homo (G.map x) (G.map y)) 
      }
    ; ε-homo = trans (F.cong G.ε-homo)  F.ε-homo
    })
  where
    module F = Hom f
    module G = Hom g
    open Monoid M using (trans)
    
-- The collection of monoids form a Category
MonoidCat : (o e : Level) → Category (lsuc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
MonoidCat o e = record
  { Obj = Monoid o e
  ; _⇒_ = Hom
  ; _≈_ = λ {A} {B} f g → (∀ x → Monoid._≈_ B (map f x) (map g x))
  ; id = HomId
  ; _∘_ = _H∘_
  ; assoc = {!!}
  ; sym-assoc = {!!}
  ; identityˡ = λ {_} {B} _ → Monoid.refl B
  ; identityʳ = {!!}
  ; identity² = {!!}
  ; equiv = λ {A} {B} → record
    { refl = λ _ → Monoid.refl B
    ; sym = {!!}
    ; trans = {!!}
    }
  ; ∘-resp-≈ = {!!}
  }
  where
    open Hom


Forget : (o e : Level) → Functor (MonoidCat o e) (Setoids o e)
Forget o e = record
  { F₀             =   λ m →
    let open Monoid m in
    record { Carrier = Carrier ; _≈_ = Monoid._≈_ m ; isEquivalence = Monoid.isEquivalence m }
  ; F₁             =   λ f → record
                             { _⟨$⟩_ = Hom.map f
                             ; cong = cong (isRelHomomorphism (Hom.isHom f))
                             }
  ; identity       =   id
  ; homomorphism   =   {!Hom.!}
  ; F-resp-≈       =   λ {_} {B} {f} {g} f≈g {x} {y} x≈y → Monoid.trans B (f≈g x) (Hom.cong g x≈y)
  }
  where
    open IsMonoidHomomorphism
    open IsRelHomomorphism

Free : (o e : Level) → Functor (Setoids o e) (MonoidCat o (o ⊔ e))
Free o e = record
  { F₀ = SLMonoid
  ; F₁ = λ f → hom (SLmap f) {!!}
  ; identity = {!!}
  ; homomorphism = {!!}
  ; F-resp-≈ = λ F≐G → {!!}
  }
{-
ListLeft : (ℓ : Level) → Adjoint (Free ℓ) (Forget ℓ)
ListLeft ℓ = record
  { unit = record { η = λ _ x → [ x ]
                  ; commute = λ _ → ≡.refl }
  ; counit = record { η = λ X →
    let fold = foldr (_*_ X) (Id X)
        _+_ = _*_ X
        e   = Id X in
    MkHom fold ≡.refl
          λ {x} {y} → ind (λ l → fold (l ++ y) ≡ fold l + fold y)
                          (≡.sym (leftId X))
                          (λ z zs eq → ≡.trans (≡.cong (z +_) eq) (≡.sym (assoc X))) x
                    ; commute = λ {X} {Y} f l →
   let foldX = foldr (_*_ X) (Id X)
       foldY = foldr (_*_ Y) (Id Y)
       _+_ = _*_ Y in
       ind (λ ll → foldY (map (mor f) ll) ≡ mor f (foldX ll))
           (≡.sym (pres-Id f))
           (λ z zs eq → ≡.trans (≡.cong ((mor f z) +_) eq) (≡.sym (pres-Op f)) ) l }
  ; zig = λ l → ind (λ ll → ll ≡ foldr _++_ [] (map [_] ll)) ≡.refl (λ y ys eq → ≡.cong (y ∷_) eq) l
  ; zag = λ {X} → ≡.sym (rightId X)
  }
-}

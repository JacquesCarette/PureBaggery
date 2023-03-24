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

open import SetoidPartition using (module Build)
open import SetoidPermutations
open import SillyList using (Hom; hom; HomId; module H; _H∘_) -- split!

private
  variable
    o o₁ o₂ o₃ e e₁ e₂ e₃ : Level
    A B : Setoid o e

∣_∣ : Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

module _ {X : Setoid o e} where
  open BuildPerm {S = X}
  -- it really is an equivalence relation:
  ≈-equiv : IsEquivalence (BuildPerm._≈_ {S = X})
  ≈-equiv = record { refl = idPerm ; sym = sym ; trans = trans }

-- lists quotiented by ≈ are commutative monoids
--   Is using resp-≡ a good idea? It gives the right result *eventually*
comm-monoid : Setoid o e → CommutativeMonoid o (o ⊔ e)
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
  where open BuildPerm {S = S}

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

-- Properly quotiented Lists induce a (Free) functor from (Carrier) Setoids
-- to the category of Commutative Monoids
Free : (o e : Level) → Functor (Setoids o e) (CMonoidCat o (o ⊔ e))
Free o e = record
  { F₀ = comm-monoid
  ; F₁ = λ {A} {B} f →
           let M = comm-monoid A
               N = comm-monoid B
               F = λ x → f ⟨$⟩ x in
           hom (List.map F)
               (H.mkIsHom {M = monoid M} {monoid N} (List.map F)
                   (map-perm f)
                   (λ xs ys → trans (resp-≡ (map-++-commute F xs ys))
                                    (++-cong {xs = List.map F xs} idPerm idPerm))
                   [])
  ; identity = λ _ → resp-≡ (map-id _) 
  ; homomorphism = λ x → resp-≡ (map-compose x)
    ; F-resp-≈ = λ {_} {_} {f} {g} f≈g x → map-resp-≈ f g f≈g idPerm
  }
  where
    open CommutativeMonoid using (refl; monoid)
    open BuildPerm

-- This stuff will need to move elsewhere, but for now, here is good enough
module _ {o : Level} (CM : CommutativeMonoid o o) where
  open CommutativeMonoid CM using (_∙_; ε; refl; ∙-cong; sym; trans; identityˡ; comm; assoc)
    renaming (Carrier to X; _≈_ to _≋_; setoid to SX)
  open Build SX using (_↣_↢_; onleft; onright; empty)
  open BuildPerm {S = SX} using (_≈_; cons; []; allRPart⇒Perm′) renaming (trans to ≈trans)
  fold : List X → X
  fold = foldr _∙_ ε

  -- it doesn't make sense to do this in SetoidPartition because it ultimately
  -- has good properties only for CommutativeMonoid
  fold-part : {xs ys zs : List X} → xs ↣ zs ↢ ys → fold xs ∙ fold ys ≋ fold zs
  fold-part (onleft x {xs = xs} {ys} {zs} p x≋y) =
    trans (assoc x (fold xs) (fold zs)) (∙-cong x≋y (fold-part p)) 
  fold-part (onright y p y≋z) = {!!}
  fold-part empty = identityˡ ε
  
  fold-cong : {x y : List X} → x ≈ y → fold x ≋ fold y
  fold-cong (cons insert-x xs≈ys x≋y) = {!!}
  fold-cong [] = refl
  
ListLeft : (o : Level) → Adjoint (Free o o) (Underlying o o)
ListLeft o = record
  { unit = ntHelper (record
    { η = λ X → record
      { _⟨$⟩_ = [_]
      ; cong = λ x≈y → cons (onleft _ empty (Setoid.refl X)) [] (Setoid.sym X x≈y)
      }
    ; commute = λ {X} {Y} f x≈y → cons (onleft _ empty (Π.cong f x≈y)) [] (Π.cong f (Setoid.refl X))
    })
  ; counit = ntHelper (record
    { η = λ X → hom (fold X)
                    (record
                      { isMagmaHomomorphism = record
                        { isRelHomomorphism = record { cong = fold-cong X }
                        ; homo = {!!}
                        }
                      ; ε-homo = {!!}
                      })
    ; commute = {!!}
    })
  ; zig = {!!}
  ; zag = λ {B} x≈y → let open CommutativeMonoid B in
                      trans (identityʳ _) x≈y
  }
  where
    open BuildPerm hiding (trans)
    open Build


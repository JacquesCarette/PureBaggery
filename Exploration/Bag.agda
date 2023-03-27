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
import Relation.Binary.Reasoning.Setoid as Reasoning
open import Relation.Binary.Structures using (IsEquivalence)

open import Categories.Category using (Category)
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Adjoint using (Adjoint)
open import Categories.NaturalTransformation using (ntHelper)

open import SetoidPartition using (module Build)
open import SetoidPermutations
open import SetoidMonoid.Hom using (Hom; hom; idH; _∘H_; mkIsHom)

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
  ; id = idH
  ; _∘_ = _∘H_
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
               (mkIsHom {M = monoid M} {monoid N} (List.map F)
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
  open CommutativeMonoid CM renaming (Carrier to X; _≈_ to _≋_; setoid to SX)
  open Build SX using (_↣_↢_; onleft; onright; empty)
  open BuildPerm {S = SX} using (_≈_; cons; []; allRPart⇒Perm′) renaming (trans to ≈trans)
  open Reasoning SX
  fold : List X → X
  fold = foldr _∙_ ε

  -- it doesn't make sense to do this in SetoidPartition because it ultimately
  -- has good properties only for CommutativeMonoid
  fold-part : {xs ys zs : List X} → xs ↣ zs ↢ ys → fold xs ∙ fold ys ≋ fold zs
  fold-part (onleft x {xs = xs} {ys} {zs} p x≋y) =
    trans (assoc x (fold xs) (fold zs)) (∙-cong x≋y (fold-part p)) 
  fold-part (onright y {xs = xs} {ys} {zs} p y≋z) = begin
    fold xs ∙ (y ∙ fold zs) ≈˘⟨ assoc (fold xs) y (fold zs) ⟩
    fold xs ∙ y ∙ fold zs   ≈⟨ ∙-congʳ (comm (fold xs) y)  ⟩
    y ∙ fold xs ∙ fold zs   ≈⟨ assoc y (fold xs) (fold zs) ⟩
    y ∙ (fold xs ∙ fold zs) ≈⟨ ∙-cong y≋z (fold-part p) ⟩
    _ ∙ fold ys ∎
  fold-part empty = identityˡ ε
  
  fold-cong : {xs ys : List X} → xs ≈ ys → fold xs ≋ fold ys
  fold-cong (cons {x} {y} {xs} {ys} {zs} insert-x xs≈ys x≋y) = begin
    y ∙ fold xs     ≈⟨ ∙-congˡ (fold-cong xs≈ys) ⟩
    y ∙ fold ys     ≈˘⟨ ∙-congʳ (identityʳ y) ⟩
    y ∙ ε ∙ fold ys ≈˘⟨ ∙-congʳ (∙-congʳ x≋y) ⟩
    x ∙ ε ∙ fold ys ≈⟨ fold-part insert-x ⟩
    fold zs ∎
  fold-cong [] = refl

  fold-++ : (xs ys : List X) → fold (xs ++ ys) ≋ fold xs ∙ fold ys
  fold-++ [] ys = sym (identityˡ _)
  fold-++ (x ∷ xs) ys = begin
    x ∙ fold (xs ++ ys)     ≈⟨ ∙-congˡ (fold-++ xs ys) ⟩
    x ∙ (fold xs ∙ fold ys) ≈˘⟨ assoc _ _ _ ⟩
    x ∙ fold xs ∙ fold ys   ∎

-- homomorphism related properties need 2 commutative monoids
module _ {o : Level} (X Y : CommutativeMonoid o o) where
  private
    module CX = CommutativeMonoid X
    module CY = CommutativeMonoid Y
    foldX : List CX.Carrier → CX.Carrier
    foldX xs = foldr CX._∙_ CX.ε xs
    foldY : List CY.Carrier → CY.Carrier
    foldY ys = foldr CY._∙_ CY.ε ys
    
  fold-map-comm : (f : Hom CX.monoid CY.monoid) → (xs : List CX.Carrier) →
    foldY (List.map (Hom.map f) xs) CY.≈ Hom.map f (foldX xs)
  fold-map-comm f [] = CY.sym (Hom.ε-homo f)
  fold-map-comm f (x ∷ xs) = begin
    Hom.map f x CY.∙ foldY (List.map (Hom.map f) xs) ≈⟨ CY.∙-congˡ (fold-map-comm f xs) ⟩
    Hom.map f x CY.∙ Hom.map f (foldX xs)            ≈⟨ CY.sym (Hom.homo f x (foldX xs)) ⟩
    Hom.map f (x CX.∙ foldX xs)                      ∎
    where open Reasoning CY.setoid
  
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
    { η = λ X → let open CommutativeMonoid X in
                hom (fold X)
                    (record
                      { isMagmaHomomorphism = record
                        { isRelHomomorphism = record { cong = fold-cong X }
                        ; homo = fold-++ X
                        }
                      ; ε-homo = refl
                      })
    ; commute = λ {X} {Y} → fold-map-comm X Y
    })
  ; zig = λ x → resp-≡ (fold-singleton x)
  ; zag = λ {B} x≈y → let open CommutativeMonoid B in
                      trans (identityʳ _) x≈y
  }
  where
    open BuildPerm hiding (trans)
    open Build
    -- this is always true, should put somewhere else
    fold-singleton : {A : Set o} (xs : List A) → foldr _++_ [] (List.map [_] xs) PE.≡ xs
    fold-singleton [] = PE.refl
    fold-singleton (x ∷ xs) = PE.cong (x ∷_) (fold-singleton xs)


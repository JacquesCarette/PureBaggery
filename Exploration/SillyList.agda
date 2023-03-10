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

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level
    A B X Y Z : Setoid o e

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

-- We can map on it; note the Setoid map (long _⟶_ )
SLmap : (f : A ⟶ B) → SillyList A → SillyList B
SLmap f [] = []
SLmap f (Leaf x) = Leaf (f ⟨$⟩ x)
SLmap f (l₀ ++ l₁) = SLmap f l₀ ++ SLmap f l₁

-- We can fold too. But note how this is intricately
-- tied to Monoid?
module _ (M : Monoid o e) where
  open Monoid M using (ε; _∙_) renaming (setoid to W)
  
  SLfold : SillyList W → ∣ W ∣
  SLfold [] = ε
  SLfold (Leaf x) = x
  SLfold (l₀ ++ l₁) = SLfold l₀ ∙ SLfold l₁

-- Since that's quotiented, exhibit that as well:
-- Note well the level here.
data _≈_ {A : Setoid o e} : SillyList A → SillyList A → Set (o ⊔ e) where
  -- it's a congruence
  Leaf : {a b : ∣ A ∣} → Setoid._≈_ A a b → Leaf a ≈ Leaf b
  []   : [] ≈ []
  _++_ : {l₁ l₂ s₁ s₂ : SillyList A} → l₁ ≈ s₁ → l₂ ≈ s₂ → l₁ ++ l₂ ≈ s₁ ++ s₂
  -- [] on left and right don't matter, on either side
  -- one could also assume ≈ is symmetric, but this leads to other problems.
  -- this way turns out more economical.
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

-- We're going to need to know that SLmap preserves ≈
-- And this is yet another split on the proof of ≈
SLmap-cong : {x y : SillyList A} (f : A ⟶ B) → x ≈ y → SLmap f x ≈ SLmap f y
SLmap-cong f (Leaf x≈y) = Leaf (Π.cong f x≈y)
SLmap-cong f [] = []
SLmap-cong f (x≈y ++ z≈w) = SLmap-cong f x≈y ++ SLmap-cong f z≈w
SLmap-cong f []++ˡ = []++ˡ
SLmap-cong f ++[]ˡ = ++[]ˡ
SLmap-cong f []++ʳ = []++ʳ
SLmap-cong f ++[]ʳ = ++[]ʳ
SLmap-cong f assoc++ˡ = assoc++ˡ
SLmap-cong f assoc++ʳ = assoc++ʳ
SLmap-cong f (x≈y ⊚ z≈w) = SLmap-cong f x≈y ⊚ SLmap-cong f z≈w

-- The following 3 proofs have all the same pattern. They are all
-- "by induction" on SillyList. We could encapsulate this in an
-- induction principle and then use it. Perhaps worth it for
-- pedagogical reasons?
SLmap-id : (x : SillyList A) → SLmap SF.id x ≈ x
SLmap-id [] = []
SLmap-id {A = A} (Leaf x) = Leaf (Setoid.refl A)
SLmap-id (x ++ y) = SLmap-id x ++ SLmap-id y

SLmap-hom : {f : X ⟶ Y} {g : Y ⟶ Z} (x : SillyList X) →
  SLmap (g SF.∘ f) x ≈ SLmap g (SLmap f x)
SLmap-hom [] = []
SLmap-hom {Z = Z} (Leaf x) = Leaf (Setoid.refl Z)
SLmap-hom (x ++ y) = SLmap-hom x ++ SLmap-hom y

-- SLmap respects when two Setoid functions are ≈
SLmap-S-cong : {f g : X ⟶ Y} → ({x y : ∣ X ∣} → Setoid._≈_ X x y →
  Setoid._≈_ Y (f ⟨$⟩ x) (g ⟨$⟩ y)) → (x : SillyList X) → SLmap f x ≈ SLmap g x
SLmap-S-cong resp [] = []
SLmap-S-cong {X = X} resp (Leaf x) = Leaf (resp (Setoid.refl X))
SLmap-S-cong resp (x ++ y) = SLmap-S-cong resp x ++ SLmap-S-cong resp y

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

-- For re-use:
-- Identity homomorphism
HomId : {M : Monoid o e} → Hom M M
HomId {M = M} = hom id (record { isMagmaHomomorphism = record
                         { isRelHomomorphism = record { cong = id }
                         ; homo = λ _ _ → refl }
                       ; ε-homo = refl })
  where open Monoid M using (refl)


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
    ({x y : M.Carrier} → x M.≈ y → f x N.≈ f y) →
    ((x y : M.Carrier) → f (x M.∙ y) N.≈ f x N.∙ f y) →
    (f M.ε N.≈ N.ε) →
    IsMonoidHomomorphism M.rawMonoid N.rawMonoid f
  cong (isRelHomomorphism (isMagmaHomomorphism (mkIsHom f c _ _))) = c
  homo (isMagmaHomomorphism (mkIsHom f _ h _)) = h
  ε-homo (mkIsHom _ _ _ pres-ε) = pres-ε

_H∘_ : {M₁ : Monoid o₁ e₁} {M₂ : Monoid o₂ e₂} {M₃ : Monoid o₃ e₃} →
  Hom M₂ M₃ → Hom M₁ M₂ → Hom M₁ M₃
_H∘_ {M₁ = M₁} {M₃ = M₃} f g =
    let h = F.map ∘ G.map in
    hom h (H.mkIsHom {M = M₁} {M₃} h (F.cong ∘ G.cong)
                     (λ x y → trans (F.cong (G.homo x y)) (F.homo (G.map x) (G.map y)))
                     (trans (F.cong G.ε-homo)  F.ε-homo))
  where
    module F = Hom f
    module G = Hom g
    open Monoid M₃ using (trans)

-- the underlying setoid map from a monoid homomorphism
setoid⟶ : {M N : Monoid o e} → Hom M N → Monoid.setoid M ⟶ Monoid.setoid N
setoid⟶ h = record { _⟨$⟩_ = Hom.map h; cong = Hom.cong h }

-- We also have that SLfold has a number of properties.
-- These are here because some properties involve monoid homomorphisms.

module _ {M : Monoid o e} where
  open Monoid M renaming (_≈_ to _≈M_; setoid to W)

  -- SLfold respects monoid SL equivalence
  SLfold-cong : {x y : SillyList W} → x ≈ y → SLfold M x ≈M SLfold M y
  SLfold-cong (Leaf x) = x
  SLfold-cong [] = refl
  SLfold-cong (eq₀ ++ eq₁) = ∙-cong (SLfold-cong eq₀) (SLfold-cong eq₁)
  SLfold-cong []++ˡ = identityˡ _
  SLfold-cong ++[]ˡ = identityʳ _
  SLfold-cong []++ʳ = sym (identityˡ _)
  SLfold-cong ++[]ʳ = sym (identityʳ _)
  SLfold-cong assoc++ˡ = assoc _ _ _
  SLfold-cong assoc++ʳ = sym (assoc _ _ _)
  SLfold-cong (eq₀ ⊚ eq₁) = trans (SLfold-cong eq₀) (SLfold-cong eq₁)

-- SLfold is natural, i.e. SLfold ∘ map is the same as Hom.map ∘ SLfold
module _ {M N : Monoid o e} (f : Hom M N) where
  open Monoid M using () renaming (_∙_ to _∙M_)
  open Monoid N using (sym; refl; trans; ∙-cong) renaming (_≈_ to _≈N_; _∙_ to _∙N_)
  open Hom f
  
  SLfold-natural : (x : SillyList (Monoid.setoid M)) →
        SLfold N (SLmap (setoid⟶ f) x) ≈N Hom.map f (SLfold M x)
  SLfold-natural [] = sym ε-homo
  SLfold-natural (Leaf x) = refl
  SLfold-natural (x ++ y) = trans
    (∙-cong (SLfold-natural x) (SLfold-natural y))
    (sym (homo (SLfold M x) (SLfold M y)))

-- The collection of monoids form a Category
MonoidCat : (o e : Level) → Category (suc (o ⊔ e)) (o ⊔ e) (o ⊔ e)
MonoidCat o e = record
  { Obj = Monoid o e
  ; _⇒_ = Hom
  ; _≈_ = λ {_} {B} f g → (∀ x → Monoid._≈_ B (map f x) (map g x))
  ; id = HomId
  ; _∘_ = _H∘_
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
  ; F₁             =   setoid⟶
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
               (H.mkIsHom {M = M} {N} (SLmap f)
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
                 (H.mkIsHom {M = SLMonoid (Monoid.setoid X)} {X} (SLfold X)
                            SLfold-cong
                            (λ _ _ → Monoid.refl X) -- ∙-homo is free
                            (Monoid.refl X))        -- ε-pres is free
    zig : {S : Setoid o o} (x : SillyList S) →
      SLfold (SLMonoid S) (SLmap (singleton S) x) ≈ x
    zig []       = []
    zig {S = S} (Leaf x) = Leaf (Setoid.refl S)
    zig (x ++ y) = zig x ++ zig y

{-# OPTIONS --without-K --safe #-}

-- Bag = Free Commutative Monoid.
-- No effective normal forms to be had, we have to do the quotient thing.

-- One way: re-use SillyList! Modify ≈ .

module SillyBag where

open import Algebra using (Monoid; CommutativeMonoid; Congruent₂)
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

-- Note how we re-use SLfold. The point is that to define it, we don't care
-- about commutativity as a property, it only shows up later.
open import SetoidMonoid.Hom using (Hom; hom; idH; _∘H_; mkIsHom)
open import SillyList using (SillyList; []; Leaf; _++_)
  renaming (SLmap to SBmap; SLfold to SBfold; SLfold-natural to SBfold-natural)

private
  variable
    o ℓ e o₁ o₂ o₃ e₁ e₂ e₃ : Level
    A B X Y Z : Setoid o e

∣_∣ : Setoid o e → Set o
∣ S ∣ = Setoid.Carrier S

infix  2 _≈_

-- Quotient things. Same as before, with an extra axiom
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
  -- Extra: commute
  commute : {l₁ l₂ : SillyList A} → l₁ ++ l₂ ≈ l₂ ++ l₁


-- It really is an equivalence relation:
-- (mostly a repeat, but I don't know how to avoid the cut-and-paste.
--  whenever there is cut-and-paste, it is because of that.)
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
    ≈-sym commute = commute

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
SBmap-cong : {x y : SillyList A} (f : A ⟶ B) → x ≈ y → SBmap f x ≈ SBmap f y
SBmap-cong f (Leaf x≈y) = Leaf (Π.cong f x≈y)
SBmap-cong f [] = []
SBmap-cong f (x≈y ++ z≈w) = SBmap-cong f x≈y ++ SBmap-cong f z≈w
SBmap-cong f []++ˡ = []++ˡ
SBmap-cong f ++[]ˡ = ++[]ˡ
SBmap-cong f []++ʳ = []++ʳ
SBmap-cong f ++[]ʳ = ++[]ʳ
SBmap-cong f assoc++ˡ = assoc++ˡ
SBmap-cong f assoc++ʳ = assoc++ʳ
SBmap-cong f (x≈y ⊚ z≈w) = SBmap-cong f x≈y ⊚ SBmap-cong f z≈w
SBmap-cong f commute = commute

-- The following 3 proofs have all the same pattern. They are all
-- "by induction" on SillyList. And, again, identical bodies to
-- what's in SillyList, but at a different type.
SBmap-id : (x : SillyList A) → SBmap SF.id x ≈ x
SBmap-id [] = []
SBmap-id {A = A} (Leaf x) = Leaf (Setoid.refl A)
SBmap-id (x ++ y) = SBmap-id x ++ SBmap-id y

SBmap-hom : {f : X ⟶ Y} {g : Y ⟶ Z} (x : SillyList X) →
  SBmap (g SF.∘ f) x ≈ SBmap g (SBmap f x)
SBmap-hom [] = []
SBmap-hom {Z = Z} (Leaf x) = Leaf (Setoid.refl Z)
SBmap-hom (x ++ y) = SBmap-hom x ++ SBmap-hom y

-- SBmap respects when two Setoid functions are ≈
SBmap-S-cong : {f g : X ⟶ Y} → ({x y : ∣ X ∣} → Setoid._≈_ X x y →
  Setoid._≈_ Y (f ⟨$⟩ x) (g ⟨$⟩ y)) → (x : SillyList X) → SBmap f x ≈ SBmap g x
SBmap-S-cong resp [] = []
SBmap-S-cong {X = X} resp (Leaf x) = Leaf (resp (Setoid.refl X))
SBmap-S-cong resp (x ++ y) = SBmap-S-cong resp x ++ SBmap-S-cong resp y


-- Silly Bags are commutative monoids
SBCommMonoid : Setoid o e → CommutativeMonoid o (o ⊔ e)
SBCommMonoid S = record
  { Carrier = SillyList S
  ; _≈_ = _≈_
  ; _∙_ = _++_
  ; ε = []
  ; isCommutativeMonoid = record
    { isMonoid = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = ≈-equiv
          ; ∙-cong = ++-cong
          }
        ; assoc = λ x y z → assoc++ˡ {_} {_} {_} {x} {y} {z}
        }
      ; identity = (λ x → []++ˡ) , λ x → ++[]ˡ
      }
    ; comm = λ _ _ → commute
    }
  }
-- Note how we end up using all the pieces of _≈_ somewhere.

-- We can re-use Hom and other kit because that doesn't care about extra properties

-- the underlying setoid map from a commutative monoid homomorphism
setoid⟶ : {M N : CommutativeMonoid o e} →
  Hom (CommutativeMonoid.monoid M) (CommutativeMonoid.monoid N) →
  CommutativeMonoid.setoid M ⟶ CommutativeMonoid.setoid N
setoid⟶ h = record { _⟨$⟩_ = Hom.map h; cong = Hom.cong h }

-- We also have that SBfold has a number of properties.
-- These are here because some properties involve (commutative) monoid homomorphisms.

module _ {CM : CommutativeMonoid o e} where
  open CommutativeMonoid CM renaming (_≈_ to _≈M_; setoid to W; monoid to M)

  -- SBfold respects monoid SL equivalence
  SBfold-cong : {x y : SillyList W} → x ≈ y → SBfold M x ≈M SBfold M y
  SBfold-cong (Leaf x) = x
  SBfold-cong [] = refl
  SBfold-cong (eq₀ ++ eq₁) = ∙-cong (SBfold-cong eq₀) (SBfold-cong eq₁)
  SBfold-cong []++ˡ = identityˡ _
  SBfold-cong ++[]ˡ = identityʳ _
  SBfold-cong []++ʳ = sym (identityˡ _)
  SBfold-cong ++[]ʳ = sym (identityʳ _)
  SBfold-cong assoc++ˡ = assoc _ _ _
  SBfold-cong assoc++ʳ = sym (assoc _ _ _)
  SBfold-cong (eq₀ ⊚ eq₁) = trans (SBfold-cong eq₀) (SBfold-cong eq₁)
  SBfold-cong commute = comm _ _ -- key! This is where commutativity is used


-- The collection of commutative monoids forms a Category
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
    ; sym = λ Fx≈Fy x → sym B (Fx≈Fy x)
    ; trans = λ Ix≈Jx Jx≈Hx x → trans B (Ix≈Jx x) (Jx≈Hx x)
    }
  ; ∘-resp-≈ = λ {_} {_} {C} {f} {h} {g} {i} fx≈hx gx≈ix x →
                trans C (cong f (gx≈ix x)) (fx≈hx (map i x))
  }
  where
    open Hom using (map; cong)
    open CommutativeMonoid using (refl; sym; trans; monoid)

-- There is an obvious forgetful Functor. Best to call it Underlying.
Underlying : (o e : Level) → Functor (CMonoidCat o e) (Setoids o e)
Underlying o e = record
  { F₀             =   CommutativeMonoid.setoid
  ; F₁             =   λ {M} {N} hom → setoid⟶ {M = M} {N} hom
  ; identity       =   id
  ; homomorphism   =   λ {_} {_} {Z} {f} {g} x≈y → Hom.cong g (Hom.cong f x≈y) 
  ; F-resp-≈       =   λ {_} {B} {f} {g} f≈g {x} {y} x≈y →
                         CommutativeMonoid.trans B (f≈g x) (Hom.cong g x≈y)
  }

-- Properly quotiented Lists induce a (Free) functor from (Carrier) Setoids
-- to the category of Commutative Monoids
Free : (o e : Level) → Functor (Setoids o e) (CMonoidCat o (o ⊔ e))
Free o e = record
  { F₀ = SBCommMonoid
  ; F₁ = λ {A} {B} f →
           let M = SBCommMonoid A
               N = SBCommMonoid B in
           hom (SBmap f)
               (mkIsHom {M = monoid M} {monoid N} (SBmap f)
                 (SBmap-cong f)
                 (λ _ _ → refl N)
                 [])
  ; identity = SBmap-id
  ; homomorphism = SBmap-hom
  ; F-resp-≈ = SBmap-S-cong
  }
  where open CommutativeMonoid using (refl; monoid)

-- And we have our Adjoint.

-- The interpretation of the pieces is essentially the same.

-- One could quibble: hey, that's not a Bag at all! But that would be WRONG.
-- It's a Free Commutative Monoid. What the hell else is it going to be?!?!?

ListLeft : (o : Level) → Adjoint (Free o o) (Underlying o o)
ListLeft o = record
  { unit = ntHelper (record { η = singleton ; commute = λ f x≈y → Leaf (Π.cong f x≈y) })
  ; counit = ntHelper (record { η = fold ; commute = SBfold-natural })
  ; zig = zig
  ; zag = id
  }
  where
    open CommutativeMonoid using (monoid; setoid; refl)
    -- kit for unit
    UF : Functor (Setoids o o) (Setoids o o)
    UF = Underlying o o ∘F Free o o
    module UF = Functor UF
    -- singleton
    singleton : (X : Setoid o o) → X ⟶ (UF.₀ X)
    _⟨$⟩_ (singleton X) = Leaf
    Π.cong (singleton X) = Leaf

    -- kit for co-unit
    FU : Functor (CMonoidCat o o) (CMonoidCat o o)
    FU = Free o o ∘F Underlying o o
    module FU = Functor FU
    fold : (X : CommutativeMonoid o o) → Hom (monoid (FU.₀ X)) (monoid X)
    fold X = hom (SBfold (monoid X))
                 (mkIsHom {M = monoid (SBCommMonoid (setoid X))} {N = monoid X}
                          (SBfold (monoid X))
                          (SBfold-cong {CM = X})
                          (λ _ _ → refl X) -- ∙-homo is free
                          (refl X))        -- ε-pres is free
    zig : {S : Setoid o o} (x : SillyList S) →
      SBfold (monoid (SBCommMonoid S)) (SBmap (singleton S) x) ≈ x
    zig []       = []
    zig {S = S} (Leaf x) = Leaf (Setoid.refl S)
    zig (x ++ y) = zig x ++ zig y

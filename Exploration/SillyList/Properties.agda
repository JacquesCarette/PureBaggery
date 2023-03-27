{-# OPTIONS --without-K --safe #-}

-- properties of map and fold
module SillyList.Properties where

open import Algebra using (Monoid)
open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_) -- SF = Setoid Functions
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)

open import SillyList.Core using (SillyList; []; Leaf; _++_; SLmap; SLfold; ∣_∣ )
open import SillyList.Equivalence hiding (++-cong; ≈-equiv) -- we just need _≈_
open import SetoidMonoid.Hom using (Hom)

private
  variable
    o e : Level
    A B X Y Z : Setoid o e

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
  open Monoid M using () renaming (_∙_ to _∙M_; setoid to MX)
  open Monoid N using (sym; refl; trans; ∙-cong) renaming (_≈_ to _≈N_; _∙_ to _∙N_)
  open Hom f renaming (setoid⟶ to F)
  
  SLfold-natural : (x : SillyList MX) → SLfold N (SLmap F x) ≈N map (SLfold M x)
  SLfold-natural [] = sym ε-homo
  SLfold-natural (Leaf x) = refl
  SLfold-natural (x ++ y) = trans
    (∙-cong (SLfold-natural x) (SLfold-natural y))
    (sym (homo (SLfold M x) (SLfold M y)))

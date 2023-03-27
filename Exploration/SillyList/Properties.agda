{-# OPTIONS --without-K --safe #-}

module SillyList.Properties where

open import Function.Equality as SF using (Π; _⟨$⟩_; _⟶_) -- SF = Setoid Functions
open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Bundles using (Setoid)

open import SillyList.Core using (SillyList; []; Leaf; _++_; SLmap; ∣_∣ )
open import SillyList.Equivalence hiding (++-cong; ≈-equiv) -- we just need _≈_

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
